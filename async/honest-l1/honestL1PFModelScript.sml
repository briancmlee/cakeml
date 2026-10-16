(*
  L1 with PREFETCHING, in the model (design/36 §6, "R1: a finding before
  proving", option (A)).  A prototype beside honestL1Model; nothing there
  changes.

  The lazy L1 (honestL1Model) tells the server what the kernel's poll said
  and finds out the truth at the later syscall, so an accept can fail and a
  read can block after a "ready" (design/36 §6, C1-C5).  This L1 instead
  pulls input into its own buffers at the end of each round and tells the
  server what its buffers hold:
   - after the round's poll, for each fd in the poll's INPUT interest that
     the poll found readable (IN, HUP or ERR):
       - a connection fd with an empty inbox and no EOF: ONE recv of
         pf_chunk bytes.  Data goes into the inbox; 0 bytes or a broken
         connection (an error other than a transient one) sets EOF;
         a transient error does nothing;
       - the listener with an empty accept queue: ONE accept.  A new fd
         joins the accept queue; EMFILE/ENFILE set `exhausted`; anything
         else does nothing;
   - the input interest is the server's poll interest only (BACKPRESSURE:
     a server that stops polling its listener stops accepting; a server
     that stops polling a connection stops receiving on it), minus paused
     fds (outbox above hw), fds whose inbox is not empty or at EOF, and the
     listener when exhausted or its queue is not empty;
   - ready (for the server): an open handle whose inbox is not empty or at
     EOF; the listener if its accept queue is not empty; a closed handle
     (it reads as EOF);
   - Read h n: TAKE n of the inbox; at EOF with an empty inbox, EOF and
     auto-close (deferred while the outbox flushes); otherwise would-block.
     No syscall;
   - Accept: the oldest queued fd, under a fresh handle; none if the queue
     is empty.  No syscall;
   - Write: as honestL1Model (buffered; one send if the outbox was empty).
  These are the version-2 world's semantics exactly (socketV2FFI), with the
  buffers as the world's state; the refinement (R1) is then a forward
  simulation (honestL1PFRefine).

  A round: the actions; then the poll (chunked, as honestL1Model), the
  flush of the writable outboxes, the fetch, the reap of the closing fds;
  the snapshot.  The run also records what each round fetched (the fetch
  log), from which R1 builds the version-2 world's schedule.
*)
Theory honestL1PFModel
Ancestors
  honestL1Model asyncCore asyncLevel1 asyncM3World honestL0 honestL0World alist
Libs
  preamble

(* ------------------------------------------------------------------------
   The state
   ------------------------------------------------------------------------ *)

Datatype:
  l1p = <| b : l1st                          (* honestL1Model's state: handles,
                                                outboxes, closing, gone,
                                                exhausted (its rdy is unused) *)
         ; inb : (word64 # word8 list) list  (* fd, fetched bytes not yet read *)
         ; eof : word64 list                 (* fds whose input has ended *)
         ; acq : word64 list |>              (* accepted fds not yet handed out *)
End

Definition pinit_def:
  pinit = <| b := l1init; inb := []; eof := []; acq := [] |>
End

Definition inb_of_def:
  inb_of ps f = case ALOOKUP ps.inb f of SOME bs => bs | NONE => []
End

Definition set_inb_def:
  set_inb f bs ps =
    ps with inb := if bs = [] then ADELKEY f ps.inb else (f, bs) :: ADELKEY f ps.inb
End

(* The bytes one fetch asks for *)
Definition pf_chunk_def:
  pf_chunk = 65536n
End

(* What a fetch found: a new connection's fd, data on an fd, the end of an
   fd's input: an orderly EOF (the peer's FIN) or a broken connection (a
   reset or another hard error; the raw error is in the event trace).  L1
   keeps the distinction; the server's vocabulary (Got) has only EOF, so
   both read as EOF there (and are Eof2 in the version-2 world) *)
Datatype:
  fetched = FConn word64 | FData word64 (word8 list) | FEof word64 | FReset word64
End

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

Definition pdo_def:
  pdo lfd (w, ps) (Accept l) =
    (if l ≠ lfd then NONE
     else
       case ps.acq of
       | [] => SOME (Accepted NONE, (w, ps), [])
       | f :: q =>
           if l1hdln (w2n lfd) ps.b.nxt < dimword (:64) then
             SOME (Accepted (SOME (l1hdl lfd ps.b.nxt)),
                   (w, ps with <| b := ps.b with <| tbl := (l1hdl lfd ps.b.nxt, f) :: ps.b.tbl;
                                                   nxt := ps.b.nxt + 1 |>;
                                  acq := q |>), [])
           else NONE) ∧
  pdo lfd (w, ps) (Read h n) =
    (if 0 < n ∧ n < 256 ** 8 then
       case ALOOKUP ps.b.tbl h of
       | NONE => SOME (Got (SOME []), (w, ps), [])
       | SOME f =>
           if inb_of ps f ≠ [] then
             SOME (Got (SOME (TAKE n (inb_of ps f))),
                   (w, set_inb f (DROP n (inb_of ps f)) ps), [])
           else if MEM f ps.eof then                     (* EOF: auto-close *)
             let ps0 = ps with <| b := ps.b with tbl := ADELKEY h ps.b.tbl;
                                  eof := FILTER ($≠ f) ps.eof |> in
               if outbox_of ps.b f = [] ∨ MEM f ps.b.gone then
                 OPTION_MAP (λ((w', b'), evs). (Got (SOME []), (w', ps0 with b := b'), evs))
                   (l1_close f (w, ps0.b))
               else                                      (* still flushing *)
                 SOME (Got (SOME []),
                       (w, ps0 with b := ps0.b with closing := f :: ps0.b.closing), [])
           else SOME (Got NONE, (w, ps), [])
     else NONE) ∧
  pdo lfd (w, ps) (Write h bs) =
    OPTION_MAP (λ(r, (w', b'), evs). (r, (w', ps with b := b'), evs))
      (l1do lfd (w, ps.b) (Write h bs))
End

Definition pacts_def:
  pacts lfd ws [] = SOME ([], [], ws) ∧
  pacts lfd ws (a :: acts) =
    case pdo lfd ws a of
    | NONE => NONE
    | SOME (r, ws1, evs1) =>
        case pacts lfd ws1 acts of
        | NONE => NONE
        | SOME (rs, evs, ws2) => SOME (r :: rs, evs1 ++ evs, ws2)
End

(* ------------------------------------------------------------------------
   The poll, the fetch, the flush and the closes
   ------------------------------------------------------------------------ *)

(* May L1 fetch on f now? *)
Definition wants_input_def:
  wants_input lfd hw ps f ⇔
    if f = lfd then ps.acq = [] ∧ ¬ps.b.exhausted
    else inb_of ps f = [] ∧ ¬MEM f ps.eof ∧ LENGTH (outbox_of ps.b f) ≤ hw
End

(* The entries polled for the interest handles hs: an open handle's fd for
   input if L1 wants input on it, and for output if its outbox is not
   empty; the listener for input if L1 wants input on it; then every other
   fd with a non-empty outbox, for output *)
Definition pf_poll_set_def:
  pf_poll_set lfd hw ps (hs : word64 list) =
    let ins = FLAT (MAP (λh. case ALOOKUP ps.b.tbl h of
                             | SOME f =>
                                 let i = (if wants_input lfd hw ps f then 1n else 0);
                                     ou = (if outbox_of ps.b f = [] then 0 else 2n) in
                                   if i + ou = 0 then [] else [(f, i + ou)]
                             | NONE => if h = lfd ∧ wants_input lfd hw ps lfd
                                       then [(lfd, 1n)] else []) hs) in
      ins ++ MAP (λ(f, bs). (f, 2n))
               (FILTER (λ(f, bs). bs ≠ [] ∧ ¬MEM f (MAP FST ins)) ps.b.outbox)
End

(* The fds polled for input *)
Definition in_fds_def:
  in_fds (fes : (word64 # num) list) = MAP FST (FILTER (λ(f, e). ODD e) fes)
End

(* Fetch on the fds fs: one accept (the listener) or one recv (a
   connection) each, re-checking wants_input (an fd may be listed twice) *)
Definition pf_fetch_def:
  pf_fetch lfd hw [] ws = SOME (ws, [], []) ∧
  pf_fetch lfd hw (f :: fs) (w, ps) =
    if ¬wants_input lfd hw ps f then pf_fetch lfd hw fs (w, ps)
    else if f = lfd then
      case sys_accept lfd w of
      | NONE => NONE
      | SOME (out, w1, ev) =>
          let (ps1, fl) =
                case l0_res_of out of
                | Ok k => (ps with acq := ps.acq ++ [n2w k], [FConn (n2w k)])
                | Fail e _ =>
                    (ps with b := ps.b with exhausted := (e = E_MFILE ∨ e = E_NFILE), [])
          in
            case pf_fetch lfd hw fs (w1, ps1) of
            | NONE => NONE
            | SOME (ws, log, evs) => SOME (ws, fl ++ log, ev :: evs)
    else
      case sys_recv f pf_chunk w of
      | NONE => NONE
      | SOME (out, w1, ev) =>
          let (ps1, fl) =
                case l0_res_of out of
                | Ok k =>
                    if 0 < k then (set_inb f (TAKE k (DROP 13 out)) ps,
                                   [FData f (TAKE k (DROP 13 out))])
                    else (ps with eof := f :: ps.eof, [FEof f])
                | Fail e _ =>
                    if l1_transient e then (ps, [])
                    else (ps with eof := f :: ps.eof, [FReset f])
          in
            case pf_fetch lfd hw fs (w1, ps1) of
            | NONE => NONE
            | SOME (ws, log, evs) => SOME (ws, fl ++ log, ev :: evs)
End

(* The ready handles L2 is told about (as asyncHLModel's hready) *)
Definition pf_ready_def:
  pf_ready lfd ps hs =
    FILTER (λh. case ALOOKUP ps.b.tbl h of
                | SOME f => inb_of ps f ≠ [] ∨ MEM f ps.eof
                | NONE => if h = lfd then ps.acq ≠ [] else T) hs
End

(* The round's poll, flush, fetch and closes: the ready handles, the next
   state, the fetch log and the events *)
Definition pf_tail_def:
  pf_tail lfd hw hs (w, ps) =
    let fes = pf_poll_set lfd hw ps hs in
    case l1_polls (poll_chunks fes) w of
    | NONE => NONE
    | SOME (rv, w1, pevs) =>
        case l1_flush (writable_fds rv) (w1, ps.b) of
        | NONE => NONE
        | SOME ((w2, b2), fevs) =>
            case pf_fetch lfd hw (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))
                   (w2, ps with b := b2) of
            | NONE => NONE
            | SOME ((w3, ps3), log, gevs) =>
                case l1_reap ps3.b.closing (w3, ps3.b) of
                | NONE => NONE
                | SOME ((w4, b4), cevs) =>
                    let ps4 = ps3 with b := b4 in
                      SOME (pf_ready lfd ps4 hs, (w4, ps4), log,
                            pevs ++ fevs ++ gevs ++ cevs)
End

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Definition pround_def:
  pround lfd hw hs ws acts =
    case pacts lfd ws acts of
    | NONE => NONE
    | SOME (rs, evs, ws1) =>
        case pf_tail lfd hw hs ws1 of
        | NONE => NONE
        | SOME (rdy, ws2, log, tevs) => SOME (ssnap rdy rs, ws2, log, evs ++ tevs)
End

(* prounds lfd hw ifds m ws0 n: after n rounds, the history, the state, the
   events, and the fetch log of each round *)
Definition prounds_def:
  prounds lfd hw ifds m ws0 0 = SOME ([], ws0, [], []) ∧
  prounds lfd hw ifds m ws0 (SUC n) =
    case prounds lfd hw ifds m ws0 n of
    | NONE => NONE
    | SOME (h, ws, evs, logs) =>
        case pround lfd hw (ifds h) ws (new_actions (log_of m) h) of
        | NONE => NONE
        | SOME (snap, ws', log, revs) =>
            SOME (h ++ [snap], ws', evs ++ revs, logs ++ [log])
End
