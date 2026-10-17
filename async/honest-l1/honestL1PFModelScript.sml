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
         joins the accept queue; EMFILE (the process is out of fds) pauses
         the listener: the accept is retried pf_backoff rounds later (as
         servers pause accepting and retry); anything else (ENFILE included) does nothing,
         so the accept is retried in the next round;
   - the input interest is the server's poll interest only (BACKPRESSURE:
     a server that stops polling its listener stops accepting; a server
     that stops polling a connection stops receiving on it), minus paused
     fds (paused by the policy pol, e.g. outbox above hw), fds whose inbox is not empty or at EOF, and the
     listener when paused or its queue is not empty;
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

  A round: the actions; then the poll (one call, as honestL1Model), the
  flush of the writable outboxes, the fetch, the write timeout (D23,
  stall_step), the reap of the closing fds;
  the snapshot; one round of the listener's pause passes.  The run
  also records what each round fetched (the fetch log), from which R1 builds the version-2 world's schedule.
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
                                                (its rdy and exhausted are unused) *)
         ; inb : (word64 # word8 list) list  (* fd, fetched bytes not yet read *)
         ; eof : word64 list                 (* fds whose input has ended *)
         ; acq : word64 list                 (* accepted fds not yet handed out *)
         ; pause : num                       (* rounds left before the listener
                                                is polled again (after EMFILE) *)
         ; stalls : (word64 # num) list |>     (* held fds, with the rounds
                                                without send progress (D23) *)
End

Definition pinit_def:
  pinit = <| b := l1init; inb := []; eof := []; acq := []; pause := 0; stalls := [] |>
End

Definition inb_of_def:
  inb_of ps f = case ALOOKUP ps.inb f of SOME bs => bs | NONE => []
End

Definition set_inb_def:
  set_inb f bs ps =
    ps with inb := if bs = [] then ADELKEY f ps.inb else (f, bs) :: ADELKEY f ps.inb
End

(* The rounds the listener pauses after an accept fails with EMFILE: the
   accept is retried every pf_backoff rounds while the process is out of
   fds (its value matters to no proof) *)
Definition pf_backoff_def:
  pf_backoff = 8n
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

(* A round's Accept actions: the only actions that take a handle (D25) *)
Definition naccepts_def:
  naccepts (acts : sact list) = LENGTH (FILTER (λa. ∃l. a = Accept l) acts)
End

Theorem naccepts_simps[simp]:
  naccepts [] = 0 ∧ naccepts (Accept l :: acts) = naccepts acts + 1 ∧
  naccepts (Read h n :: acts) = naccepts acts ∧ naccepts (Write h bs :: acts) = naccepts acts ∧
  naccepts (acts1 ++ acts2) = naccepts acts1 + naccepts acts2
Proof
  simp[naccepts_def, FILTER_APPEND]
QED

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

(* The pause policy (design/45 §2.2, Q1 (P2)): pol ps f, "do not fetch
   f now".  Servers pause an fd whose outbox is above the high-water mark
   (D4); the proxy and the client never pause in L1 (the proxy manages its
   interest itself) *)
Definition pol_self_def:
  pol_self hw (ps : l1p) (f : word64) ⇔ hw < LENGTH (outbox_of ps.b f)
End

Definition pol_never_def:
  pol_never (ps : l1p) (f : word64) ⇔ F
End

(* pol never pauses an fd whose outbox is within hw (pol_self hw and
   pol_never both; the liveness results assume it) *)
Definition pol_ok_def:
  pol_ok hw pol ⇔ ∀ps f. LENGTH (outbox_of ps.b f) ≤ hw ⇒ ¬pol ps f
End

Theorem pol_ok_self:
  pol_ok hw (pol_self hw)
Proof
  simp[pol_ok_def, pol_self_def]
QED

Theorem pol_ok_never:
  pol_ok hw pol_never
Proof
  simp[pol_ok_def, pol_never_def]
QED

(* May L1 fetch on f now?  The listener: when no connection awaits a
   handle and accepting is not paused (D17); a connection: when L1 holds
   none of its input, it is not at EOF, and the policy does not pause it *)
Definition wants_input_def:
  wants_input lfd pol ps f ⇔
    if f = lfd then ps.acq = [] ∧ ps.pause = 0
    else inb_of ps f = [] ∧ ¬MEM f ps.eof ∧ ¬pol ps f
End

(* The entries polled for the interest handles hs: an open handle's fd for
   input if L1 wants input on it, and for output if its outbox is not
   empty; the listener for input if L1 wants input on it; then every other
   fd with a non-empty outbox, for output *)
Definition pf_poll_set_def:
  pf_poll_set lfd pol ps (hs : word64 list) =
    let ins = FLAT (MAP (λh. case ALOOKUP ps.b.tbl h of
                             | SOME f =>
                                 let i = (if wants_input lfd pol ps f then 1n else 0);
                                     ou = (if outbox_of ps.b f = [] then 0 else 2n) in
                                   if i + ou = 0 then [] else [(f, i + ou)]
                             | NONE => if h = lfd ∧ wants_input lfd pol ps lfd
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
  pf_fetch lfd pol [] ws = SOME (ws, [], []) ∧
  pf_fetch lfd pol (f :: fs) (w, ps) =
    if ¬wants_input lfd pol ps f then pf_fetch lfd pol fs (w, ps)
    else if f = lfd then
      case sys_accept lfd w of
      | NONE => NONE
      | SOME (out, w1, ev) =>
          let (ps1, fl) =
                case l0_res_of out of
                | Ok k => (ps with acq := ps.acq ++ [n2w k], [FConn (n2w k)])
                | Fail e _ =>
                    ((if e = E_MFILE then ps with pause := pf_backoff else ps), [])
          in
            case pf_fetch lfd pol fs (w1, ps1) of
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
            case pf_fetch lfd pol fs (w1, ps1) of
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

(* The fds L1 holds: open (with a handle) or closing *)
Definition pf_held_def:
  pf_held (ps : l1p) = MAP SND ps.b.tbl ++ ps.b.closing
End

(* D23, the write timeout (user decision; generalises D19's hung-up
   policy to every fd).  A peer that stops reading for good looks, through
   poll and send, like a slow one: a receiver that keeps its window closed
   while it acknowledges the probes keeps the connection open indefinitely
   ([T] RFC 1122 4.2.2.17), so no error ever comes.  So every fd L1 holds
   has a stall count (`stalls`): each round that ends with its outbox not
   empty and no smaller than before the round's flush adds 1; a round with
   progress or an empty outbox resets it to 0; at pf_sendwait the outbox
   is dropped.  An fd whose input ends with a hard error (FReset: the
   connection really broke) has its outbox dropped at once (D19 (a)).
   Dropping marks the fd gone (later writes are dropped), so it is closed
   as soon as the server has closed or read to EOF (the reap, or the
   auto-close) *)
Definition pf_sendwait_def:
  pf_sendwait = 8n
End

Definition drop_out_def:
  drop_out (b : l1st) f = set_outbox f [] (b with gone := f :: FILTER ($≠ f) b.gone)
End

(* One round's stall counts (D23): hfs are the fds to count (the round
   passes pf_held, every fd L1 holds); ob is the outboxes before the
   round's flush; log is the round's fetch log *)
Definition stall_step_def:
  stall_step (hfs : word64 list) (ob : word64 -> word8 list) log (ps : l1p) =
    let held = (λf. MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing);
        hs0 = FILTER (λ(f, n). held f) ps.stalls ++
              MAP (λf. (f, 0n)) (nub (FILTER (λf. held f ∧ ¬MEM f (MAP FST ps.stalls)) hfs));
        hs1 = MAP (λ(f, n). if MEM (FReset f) log then (f, pf_sendwait)
                            else if outbox_of ps.b f = [] ∨
                                    LENGTH (outbox_of ps.b f) < LENGTH (ob f) then (f, 0)
                            else (f, n + 1)) hs0;
        drop = MAP FST (FILTER (λ(f, n). pf_sendwait ≤ n) hs1)
    in ps with <| b := FOLDL drop_out ps.b drop;
                  stalls := FILTER (λ(f, n). n < pf_sendwait) hs1 |>
End

Theorem drop_out_fields[simp]:
  (drop_out b f).tbl = b.tbl ∧ (drop_out b f).nxt = b.nxt ∧
  (drop_out b f).closing = b.closing ∧ (drop_out b f).exhausted = b.exhausted ∧
  (drop_out b f).rdy = b.rdy
Proof
  simp[drop_out_def, set_outbox_def]
QED

Theorem FOLDL_drop_out:
  ∀l b. (FOLDL drop_out b l).tbl = b.tbl ∧ (FOLDL drop_out b l).nxt = b.nxt ∧
        (FOLDL drop_out b l).closing = b.closing ∧ (FOLDL drop_out b l).rdy = b.rdy ∧
        (∀f. outbox_of (FOLDL drop_out b l) f = (if MEM f l then [] else outbox_of b f)) ∧
        (∀f. MEM f (FOLDL drop_out b l).gone ⇔ MEM f b.gone ∨ MEM f l) ∧
        (∀f. MEM f (MAP FST (FOLDL drop_out b l).outbox) ⇒ MEM f (MAP FST b.outbox))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘drop_out b h’ strip_assume_tac) >> simp[] >>
  rpt conj_tac
  >- (rw[] >> gvs[drop_out_def, outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY])
  >- (gen_tac >> simp[drop_out_def, set_outbox_def, MEM_FILTER] >> metis_tac[])
  >> rpt strip_tac >> first_x_assum drule >>
  simp[drop_out_def, set_outbox_def, ADELKEY_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem stall_step_fields[simp]:
  (stall_step hfs ob log ps).b.tbl = ps.b.tbl ∧ (stall_step hfs ob log ps).b.nxt = ps.b.nxt ∧
  (stall_step hfs ob log ps).b.closing = ps.b.closing ∧
  (stall_step hfs ob log ps).b.rdy = ps.b.rdy ∧
  (stall_step hfs ob log ps).acq = ps.acq ∧ (stall_step hfs ob log ps).inb = ps.inb ∧
  (stall_step hfs ob log ps).eof = ps.eof ∧ (stall_step hfs ob log ps).pause = ps.pause
Proof
  simp[stall_step_def, FOLDL_drop_out]
QED

(* The write timeout only drops outboxes, of fds L1 holds *)
Theorem stall_step_b:
  ∃l. (stall_step hfs ob log ps).b = FOLDL drop_out ps.b l ∧
      ∀f. MEM f l ⇒ MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing
Proof
  simp[stall_step_def] >> irule_at Any EQ_REFL >>
  rpt strip_tac >> gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_APPEND, nub_set] >>
  every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem stall_step_outbox:
  (∀f. outbox_of (stall_step hfs ob log ps).b f = [] ∨
       outbox_of (stall_step hfs ob log ps).b f = outbox_of ps.b f) ∧
  (∀f. MEM f (stall_step hfs ob log ps).b.gone ⇒
       MEM f ps.b.gone ∨ MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing) ∧
  (∀f. MEM f (MAP FST (stall_step hfs ob log ps).b.outbox) ⇒ MEM f (MAP FST ps.b.outbox))
Proof
  qspecl_then [‘hfs’, ‘ob’, ‘log’, ‘ps’] strip_assume_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_b) >>
  simp[FOLDL_drop_out] >> rw[] >> metis_tac[FOLDL_drop_out]
QED

(* The round's poll, flush, fetch and closes: the ready handles, the next
   state, the fetch log and the events *)
Definition pf_tail_def:
  pf_tail lfd pol hs (w, ps) =
    let fes = pf_poll_set lfd pol ps hs in
    case l1_polls [fes] w of
    | NONE => NONE
    | SOME (rv, w1, pevs) =>
        case l1_flush (writable_fds rv) (w1, ps.b) of
        | NONE => NONE
        | SOME ((w2, b2), fevs) =>
            case pf_fetch lfd pol (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))
                   (w2, ps with b := b2) of
            | NONE => NONE
            | SOME ((w3, ps3'), log, gevs) =>
                let ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3' in
                case l1_reap ps3.b.closing (w3, ps3.b) of
                | NONE => NONE
                | SOME ((w4, b4), cevs) =>
                    let ps4 = ps3 with <| b := b4; pause := ps3.pause − 1 |> in
                      SOME (pf_ready lfd ps4 hs, (w4, ps4), log,
                            pevs ++ fevs ++ gevs ++ cevs)
End

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Definition pround_def:
  pround lfd pol hs ws acts =
    case pacts lfd ws acts of
    | NONE => NONE
    | SOME (rs, evs, ws1) =>
        case pf_tail lfd pol hs ws1 of
        | NONE => NONE
        | SOME (rdy, ws2, log, tevs) => SOME (ssnap rdy rs, ws2, log, evs ++ tevs)
End

(* prounds lfd pol ifds m ws0 n: after n rounds, the history, the state, the
   events, and the fetch log of each round *)
Definition prounds_def:
  prounds lfd pol ifds m ws0 0 = SOME ([], ws0, [], []) ∧
  prounds lfd pol ifds m ws0 (SUC n) =
    case prounds lfd pol ifds m ws0 n of
    | NONE => NONE
    | SOME (h, ws, evs, logs) =>
        case pround lfd pol (ifds h) ws (new_actions (log_of m) h) of
        | NONE => NONE
        | SOME (snap, ws', log, revs) =>
            SOME (h ++ [snap], ws', evs ++ revs, logs ++ [log])
End
