(*
  L1, the verified wrapper layer, in the model (design/36 §5).

  The event loop runs a library computation (the server, unchanged) that
  emits TODAY'S socket actions on HANDLES, exactly as close-v2's handle
  layer (asyncHLModel): Accept l | Read h n | Write h bs, with responses
  Accepted | Got | Wrote.  L1 performs them with the honest L0 calls in the
  L0 world (honestL0World), and absorbs the raw behaviours:

   - writes are BUFFERED: Write h bs answers Wrote at once; the bytes go
     into h's fd's outbox, sent at once if the outbox was empty, the rest
     later, when the fd is writable (a partial send or EAGAIN stalls only
     that fd);
   - a read is done only on an fd the round's poll reported readable and
     no call has since found empty (the ROUND DISCIPLINE); otherwise
     "would block" with no syscall;
   - EOF auto-closes the fd, as the handle layer does; if its outbox is not
     empty the fd stays open (closing) until the outbox is flushed;
   - a broken connection (an error other than a transient one, from recv
     or send) ends the episode: its outbox is dropped and the next Read of
     its handle reports EOF and closes the fd;
   - accept: EAGAIN or an aborted pending connection is "no connection";
     EMFILE/ENFILE set `exhausted`, and the listener is then not polled
     until L1 closes an fd;
   - pausing: an fd whose outbox holds more than hw bytes is not polled for
     input (so L2 is not told it is readable).

  A round: perform the computation's new actions; poll (no wait); flush
  the outboxes of the fds the poll found writable; close the closing fds
  whose outboxes are empty; give the computation the snapshot.

  l1do performs one action (its response, the next world and L1 state, and
  the raw L0 events); lrounds the whole run, as asyncHLModel's hrounds.
  NONE: an L0 call failed (the C exits) or blocked; L1 never makes such
  calls (to be proved: l1_inv, honestL1Props).
*)
Theory honestL1Model
Ancestors
  asyncCore asyncLevel1 asyncM3World ffiSpikeSocketFFI ffi honestL0
  honestL0World alist
Libs
  preamble

(* ------------------------------------------------------------------------
   L0 calls, as the CakeML code makes them: a zero buffer of the call's
   length goes in, and the call's event is recorded
   ------------------------------------------------------------------------ *)

Definition l0_do_def:
  l0_do n conf alen w =
    case l0_ffi_fn n conf (REPLICATE alen 0w) w of
    | SOME (FFIreturn out w') =>
        SOME (out, w', IO_event (ExtCall n) conf (ZIP (REPLICATE alen (0w:word8), out)))
    | _ => NONE
End

(* The decoded result of a call; a result that cannot be decoded is
   treated as an error (cannot happen: honestL0's dec_enc_res) *)
Definition l0_res_of_def:
  l0_res_of out = case dec_res out of SOME r => r | NONE => Fail E_OTHER []
End

Definition sys_accept_def:
  sys_accept l w = l0_do «sys_accept» (fd_bytes l) 13 w
End

Definition sys_recv_def:
  sys_recv f n w = l0_do «sys_recv» (fd_bytes f) (13 + n) w
End

Definition sys_send_def:
  sys_send f bs w = l0_do «sys_send» (fd_bytes f ++ bs) 13 w
End

Definition sys_close_def:
  sys_close f w = l0_do «sys_close» (fd_bytes f) 13 w
End

(* A non-blocking poll of (fd, events) entries: events 1 IN, 2 OUT *)
Definition poll_conf_def:
  poll_conf (fes : (word64 # num) list) =
    0w :: FLAT (MAP (λ(f, e). fd_bytes f ++ [n2w e]) fes)
End

Definition sys_poll_def:
  sys_poll fes w = l0_do «sys_poll» (poll_conf fes) (13 + LENGTH fes) w
End

(* ------------------------------------------------------------------------
   L1's state
   ------------------------------------------------------------------------ *)

Datatype:
  l1st = <| tbl : (word64 # word64) list    (* open handle, its fd (as hstate) *)
          ; nxt : num                       (* handles issued so far *)
          ; outbox : (word64 # word8 list) list   (* fd, bytes not yet sent *)
          ; closing : word64 list           (* fds L2 no longer sees, still flushing *)
          ; gone : word64 list              (* fds whose connection broke *)
          ; rdy : word64 list               (* readable at this round's poll, not yet
                                               found empty *)
          ; exhausted : bool |>             (* the last accept ran out of fds *)
End

(* The j-th handle, skipping the listener's number: asyncHLModel's hdln and
   hdl, restated so that this theory needs none of the CF ancestors of
   asyncHLModel (the refinement proves them equal) *)
Definition l1hdln_def:
  l1hdln (lfdn:num) (j:num) = if j < lfdn then j else j + 1
End

Definition l1hdl_def:
  l1hdl (lfd:word64) j : word64 = n2w (l1hdln (w2n lfd) j)
End

Definition l1init_def:
  l1init = <| tbl := []; nxt := 0; outbox := []; closing := []; gone := [];
              rdy := []; exhausted := F |>
End

Definition outbox_of_def:
  outbox_of st f = case ALOOKUP st.outbox f of SOME bs => bs | NONE => []
End

Definition set_outbox_def:
  set_outbox f bs st =
    st with outbox := if bs = [] then ADELKEY f st.outbox
                      else (f, bs) :: ADELKEY f st.outbox
End

(* Errors after which a call is simply retried later *)
Definition l1_transient_def:
  l1_transient e ⇔ MEM e [E_AGAIN; E_INTR; E_NOBUFS; E_NOMEM]
End

(* Forget fd f: its outbox, brokenness and readiness; a close frees an fd,
   so accepting may succeed again *)
Definition forget_def:
  forget f st =
    set_outbox f [] (st with <| gone := FILTER ($≠ f) st.gone;
                                closing := FILTER ($≠ f) st.closing;
                                rdy := FILTER ($≠ f) st.rdy;
                                exhausted := F |>)
End

(* Close fd f (L1 ignores close's result: an interrupted close may leave
   the fd open, which needs a signal handler the program does not install) *)
Definition l1_close_def:
  l1_close f (w, st) =
    case sys_close f w of
    | NONE => NONE
    | SOME (_, w', ev) => SOME ((w', forget f st), [ev])
End

(* After a raw send of the outbox of f *)
Definition after_send_def:
  after_send f r st =
    case r of
    | Ok k => set_outbox f (DROP k (outbox_of st f)) st
    | Fail e _ =>
        if l1_transient e then st
        else set_outbox f [] (st with gone := f :: FILTER ($≠ f) st.gone)
End

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

Definition l1do_def:
  l1do lfd (w, st) (Accept l) =
    (if ¬MEM l st.rdy ∨ st.exhausted then SOME (Accepted NONE, (w, st), [])
     else
       case sys_accept l w of
       | NONE => NONE
       | SOME (out, w', ev) =>
           case l0_res_of out of
           | Ok f =>
               if l1hdln (w2n lfd) st.nxt < dimword (:64) then
                 SOME (Accepted (SOME (l1hdl lfd st.nxt)),
                       (w', st with <| tbl := (l1hdl lfd st.nxt, n2w f) :: st.tbl;
                                       nxt := st.nxt + 1 |>), [ev])
               else NONE
           | Fail e _ =>
               SOME (Accepted NONE,
                     (w', st with <| rdy := FILTER ($≠ l) st.rdy;
                                     exhausted := (e = E_MFILE ∨ e = E_NFILE) |>), [ev])) ∧
  l1do lfd (w, st) (Read h n) =
    (if 0 < n ∧ n < 256 ** 8 then
       case ALOOKUP st.tbl h of
       | NONE => SOME (Got (SOME []), (w, st), [])
       | SOME f =>
           let st0 = st with tbl := ADELKEY h st.tbl in
           if MEM f st.gone then
             OPTION_MAP (λ(ws, evs). (Got (SOME []), ws, evs)) (l1_close f (w, st0))
           else if ¬MEM f st.rdy then SOME (Got NONE, (w, st), [])
           else
             case sys_recv f n w of
             | NONE => NONE
             | SOME (out, w', ev) =>
                 case l0_res_of out of
                 | Ok k =>
                     if 0 < k then SOME (Got (SOME (TAKE k (DROP 13 out))), (w', st), [ev])
                     else if outbox_of st f = [] then         (* EOF: auto-close *)
                       OPTION_MAP (λ(ws, evs). (Got (SOME []), ws, ev :: evs))
                         (l1_close f (w', st0))
                     else                                     (* EOF, still flushing *)
                       SOME (Got (SOME []),
                             (w', st0 with <| closing := f :: st.closing;
                                              rdy := FILTER ($≠ f) st.rdy |>), [ev])
                 | Fail e _ =>
                     if l1_transient e then
                       SOME (Got NONE, (w', st with rdy := FILTER ($≠ f) st.rdy), [ev])
                     else                                     (* broken: the episode ends *)
                       OPTION_MAP (λ(ws, evs). (Got (SOME []), ws, ev :: evs))
                         (l1_close f (w', st0))
     else NONE) ∧
  l1do lfd (w, st) (Write h bs) =
    case ALOOKUP st.tbl h of
    | NONE => SOME (Wrote, (w, st), [])
    | SOME f =>
        if MEM f st.gone then SOME (Wrote, (w, st), [])
        else if outbox_of st f ≠ [] then
          SOME (Wrote, (w, set_outbox f (outbox_of st f ++ bs) st), [])
        else
          case sys_send f bs w of
          | NONE => NONE
          | SOME (out, w', ev) =>
              SOME (Wrote, (w', after_send f (l0_res_of out) (set_outbox f bs st)), [ev])
End

(* Performing a round's actions in order *)
Definition l1acts_def:
  l1acts lfd ws [] = SOME ([], [], ws) ∧
  l1acts lfd ws (a :: acts) =
    case l1do lfd ws a of
    | NONE => NONE
    | SOME (r, ws1, evs1) =>
        case l1acts lfd ws1 acts of
        | NONE => NONE
        | SOME (rs, evs, ws2) => SOME (r :: rs, evs1 ++ evs, ws2)
End

(* ------------------------------------------------------------------------
   The poll, the flush and the closes
   ------------------------------------------------------------------------ *)

(* The entries polled for the interest handles hs: an open handle's fd for
   input (and output if its outbox is not empty) unless paused; the
   listener unless exhausted; then every other fd with a non-empty outbox,
   for output *)
Definition l1_poll_set_def:
  l1_poll_set lfd hw st (hs : word64 list) =
    let ins = FLAT (MAP (λh. case ALOOKUP st.tbl h of
                             | SOME f => if LENGTH (outbox_of st f) ≤ hw
                                         then [(f, if outbox_of st f = [] then 1 else 3)]
                                         else []
                             | NONE => if h = lfd ∧ ¬st.exhausted then [(lfd, 1n)] else []) hs) in
      ins ++ MAP (λ(f, bs). (f, 2n))
               (FILTER (λ(f, bs). bs ≠ [] ∧ ¬MEM f (MAP FST ins)) st.outbox)
End

(* The revents of the poll's entries; none if the poll failed *)
Definition poll_revents_def:
  poll_revents fes out =
    case l0_res_of out of
    | Ok _ => ZIP (MAP FST fes, MAP byte_revents (TAKE (LENGTH fes) (DROP 13 out)))
    | Fail _ _ => []
End

(* Readable: a recv would not block (IN), or would report an error or EOF
   (ERR, HUP) *)
Definition readable_fds_def:
  readable_fds rv = MAP FST (FILTER (λ(f, r). r.rin ∨ r.rhup ∨ r.rerr) rv)
End

Definition writable_fds_def:
  writable_fds rv = MAP FST (FILTER (λ(f, r). r.rout ∨ r.rhup ∨ r.rerr) rv)
End

(* The ready handles L2 is told about (as asyncHLModel's hready): an open
   handle whose fd is readable, the listener if readable, and a closed
   handle (it reads as EOF) *)
Definition l1_ready_def:
  l1_ready lfd st rdy hs =
    FILTER (λh. case ALOOKUP st.tbl h of
                | SOME f => MEM f rdy
                | NONE => if h = lfd then MEM h rdy else T) hs
End

(* Flush the outboxes of the writable fds fs, one send each *)
Definition l1_flush_def:
  l1_flush [] ws = SOME (ws, []) ∧
  l1_flush (f :: fs) (w, st) =
    if outbox_of st f = [] ∨ MEM f st.gone then l1_flush fs (w, st)
    else
      case sys_send f (outbox_of st f) w of
      | NONE => NONE
      | SOME (out, w', ev) =>
          case l1_flush fs (w', after_send f (l0_res_of out) st) of
          | NONE => NONE
          | SOME (ws, evs) => SOME (ws, ev :: evs)
End

(* Close the closing fds whose outbox is empty or whose connection broke *)
Definition l1_reap_def:
  l1_reap [] ws = SOME (ws, []) ∧
  l1_reap (f :: fs) (w, st) =
    if outbox_of st f = [] ∨ MEM f st.gone then
      case l1_close f (w, st) of
      | NONE => NONE
      | SOME (ws, evs) =>
          case l1_reap fs ws of
          | NONE => NONE
          | SOME (ws', evs') => SOME (ws', evs ++ evs')
    else l1_reap fs (w, st)
End

(* The round's poll, flush and closes: the ready handles, the next state
   and the events *)
Definition l1_tail_def:
  l1_tail lfd hw hs (w, st) =
    let fes = l1_poll_set lfd hw st hs in
    case sys_poll fes w of
    | NONE => NONE
    | SOME (out, w1, pev) =>
        let rv = poll_revents fes out;
            rdy = readable_fds rv;
            st1 = st with rdy := rdy in
          case l1_flush (writable_fds rv) (w1, st1) of
          | NONE => NONE
          | SOME ((w2, st2), fevs) =>
              case l1_reap st2.closing (w2, st2) of
              | NONE => NONE
              | SOME ((w3, st3), cevs) =>
                  SOME (l1_ready lfd st rdy hs, (w3, st3), pev :: fevs ++ cevs)
End

(* ------------------------------------------------------------------------
   The run (as asyncHLModel's hrounds)
   ------------------------------------------------------------------------ *)

(* One round: the actions acts, then the poll of the interest handles hs:
   the snapshot, the next state and the round's events; NONE if a call
   failed *)
Definition l1round_def:
  l1round lfd hw hs ws acts =
    case l1acts lfd ws acts of
    | NONE => NONE
    | SOME (rs, evs, ws1) =>
        case l1_tail lfd hw hs ws1 of
        | NONE => NONE
        | SOME (rdy, ws2, tevs) => SOME (ssnap rdy rs, ws2, evs ++ tevs)
End

(* lrounds lfd hw ifds m ws0 n: after n rounds of L1 running m with
   interest ifds (a function of the history), started in ws0: the history,
   the state, and NONE once a call has failed *)
Definition lrounds_def:
  lrounds lfd hw ifds m ws0 0 = SOME ([], ws0, []) ∧
  lrounds lfd hw ifds m ws0 (SUC n) =
    case lrounds lfd hw ifds m ws0 n of
    | NONE => NONE
    | SOME (h, ws, evs) =>
        case l1round lfd hw (ifds h) ws (new_actions (log_of m) h) of
        | NONE => NONE
        | SOME (snap, ws', revs) => SOME (h ++ [snap], ws', evs ++ revs)
End

(* No call of the run fails *)
Definition lrun_ok_def:
  lrun_ok lfd hw ifds m ws0 ⇔ ∀n. lrounds lfd hw ifds m ws0 n ≠ NONE
End
