(*
  L1, the verified wrapper layer (design/36 §5): a draft of its functional
  core, i.e. what the L1 event loop does with each action of the server
  (L2) and each raw L0 result, in TODAY'S vocabulary towards L2:
     actions   Accept l | Read c n | Write c bs
     responses Accepted (fd option) | Got (data option) | Wrote
  (the same constructors as asyncM3World's sact/sresp, named L2... here to
  keep this draft free of the CF ancestors).

  L1's per-fd state: the outbox (written by L2, not yet accepted by the
  kernel), gone fds (reset / peer gone), the fds the current round's poll
  reported readable and that no call has since found empty (the ROUND
  DISCIPLINE), and whether the last accept ran out of fds.

  Proved here: in the SIMPLE world (sends accepted in full, no errors),
  each wrapper is today's call: one raw call, the same response, and no
  state left behind (write_simple, read_simple, accept_simple).
*)
Theory honestL1
Ancestors
  words list alist honestL0
Libs
  preamble

Datatype:
  l2_act = L2Accept word64 | L2Read word64 num | L2Write word64 (word8 list)
End

Datatype:
  l2_resp = L2Accepted (word64 option) | L2Got ((word8 list) option) | L2Wrote
End

Datatype:
  l1st = <| outbox : (word64 # word8 list) list
          ; gone : word64 list
          ; rdy : word64 list          (* readable this round, not yet found empty *)
          ; exhausted : bool |>
End

Definition outbox_of_def:
  outbox_of st c = case ALOOKUP st.outbox c of SOME bs => bs | NONE => []
End

Definition set_outbox_def:
  set_outbox c bs st = st with outbox := (c, bs) :: ADELKEY c st.outbox
End

(* Errors after which the call may simply be tried again later *)
Definition transient_def:
  transient e ⇔ MEM e [E_AGAIN; E_INTR; E_NOBUFS; E_NOMEM]
End

(* ---- write: buffered; Wrote at once; the raw send happens in the same
   round (flush) ---- *)

Definition l1_write_def:
  l1_write c bs st =
    if MEM c st.gone then (L2Wrote, st)          (* peer gone: dropped, and
                                                    the next read says EOF *)
    else (L2Wrote, set_outbox c (outbox_of st c ++ bs) st)
End

(* The raw send to make for c this round, if any *)
Definition l1_flush_call_def:
  l1_flush_call st c =
    if MEM c st.gone ∨ outbox_of st c = [] then NONE else SOME (outbox_of st c)
End

(* After the raw send's result *)
Definition l1_after_send_def:
  l1_after_send c (SendCount k) st = set_outbox c (DROP k (outbox_of st c)) st ∧
  l1_after_send c (SendErr e) st =
    if transient e then st                       (* OUT interest; retry *)
    else set_outbox c [] (st with gone := c :: st.gone)
End

(* ---- read: read-or-closed, with the round discipline.  The raw result
   is NONE when L1 makes no syscall. ---- *)

(* Whether L1 calls recv for Read c *)
Definition l1_read_calls_def:
  l1_read_calls st c ⇔ ¬MEM c st.gone ∧ MEM c st.rdy
End

Definition l1_read_def:
  l1_read c r st =
    if MEM c st.gone then (L2Got (SOME []), st)
    else if ¬MEM c st.rdy then (L2Got NONE, st)
    else case r of
      | NONE => (L2Got NONE, st)
      | SOME (RecvData d) => (L2Got (SOME d), st)
      | SOME RecvEof => (L2Got (SOME []), st)
      | SOME (RecvErr e) =>
          if transient e then (L2Got NONE, st with rdy := FILTER ($≠ c) st.rdy)
          else (L2Got (SOME []), set_outbox c [] (st with gone := c :: st.gone))
End

(* ---- accept: accept-or-skip ---- *)

Definition l1_accept_def:
  l1_accept l r st =
    if ¬MEM l st.rdy then (L2Accepted NONE, st)
    else case r of
      | NONE => (L2Accepted NONE, st)
      | SOME (AccFd f) => (L2Accepted (SOME f), st)
      | SOME (AccErr e) =>
          if e = E_MFILE ∨ e = E_NFILE then
            (L2Accepted NONE, st with <| exhausted := T; rdy := FILTER ($≠ l) st.rdy |>)
          else (L2Accepted NONE, st with rdy := FILTER ($≠ l) st.rdy)
End

(* ---- readiness: what L1 polls, and what L2 is told ---- *)

(* The (fd, events) list L1 polls: L2's read interest (the listener left
   out while exhausted; fds with an outbox above hw left out: pausing),
   and OUT for every fd with a non-empty outbox.  events: 1 IN, 2 OUT. *)
Definition l1_poll_set_def:
  l1_poll_set lfd hw st (interest : word64 list) =
    MAP (λf. (f, 1n + (if outbox_of st f ≠ [] then 2 else 0)))
        (FILTER (λf. ¬(f = lfd ∧ st.exhausted) ∧ LENGTH (outbox_of st f) ≤ hw) interest) ++
    MAP (λ(f, bs). (f, 2)) (FILTER (λ(f, bs). bs ≠ [] ∧ ¬MEM f interest) st.outbox)
End

(* The fds L2 is told are readable: IN, HUP or ERR (the following recv
   reports which); these also start the round's discipline set *)
Definition l1_readable_def:
  l1_readable (polled : (word64 # revents) list) =
    MAP FST (FILTER (λ(f, r). r.rin ∨ r.rhup ∨ r.rerr) polled)
End

(* ------------------------------------------------------------------------
   The simple world: each wrapper is today's call
   ------------------------------------------------------------------------ *)

(* A write on a live fd with an empty outbox: Wrote, one raw send of
   exactly bs, and when the kernel takes it all, nothing is left over *)
Theorem write_simple:
  ¬MEM c st.gone ∧ outbox_of st c = [] ∧ bs ≠ [] ⇒
  ∃st1. l1_write c bs st = (L2Wrote, st1) ∧
        l1_flush_call st1 c = SOME bs ∧
        outbox_of (l1_after_send c (SendCount (LENGTH bs)) st1) c = [] ∧
        (l1_after_send c (SendCount (LENGTH bs)) st1).gone = st.gone ∧
        (l1_after_send c (SendCount (LENGTH bs)) st1).rdy = st.rdy
Proof
  rw[l1_write_def, l1_flush_call_def, l1_after_send_def, set_outbox_def,
     outbox_of_def]
QED

(* A read of a fd reported readable: the data or EOF, exactly as recv
   said, and the state unchanged *)
Theorem read_simple:
  ¬MEM c st.gone ∧ MEM c st.rdy ⇒
  l1_read_calls st c ∧
  l1_read c (SOME (RecvData d)) st = (L2Got (SOME d), st) ∧
  l1_read c (SOME RecvEof) st = (L2Got (SOME []), st)
Proof
  rw[l1_read_calls_def, l1_read_def]
QED

Theorem accept_simple:
  MEM l st.rdy ⇒
  l1_accept l (SOME (AccFd f)) st = (L2Accepted (SOME f), st)
Proof
  rw[l1_accept_def]
QED

(* With no outboxes and not exhausted, L1 polls exactly L2's interest,
   for IN only: today's «sock_poll» *)
Theorem poll_simple:
  st.outbox = [] ∧ ¬st.exhausted ⇒
  l1_poll_set lfd hw st interest = MAP (λf. (f, 1)) interest
Proof
  rw[l1_poll_set_def, outbox_of_def] >>
  ‘FILTER (λf. T) interest = interest’ by simp[FILTER_EQ_ID] >>
  fs[]
QED

(* ------------------------------------------------------------------------
   What L1 guarantees beyond the simple world (first facts; the run-level
   versions are phase 4)
   ------------------------------------------------------------------------ *)

(* A slow reader stalls only itself: a failed or partial send on c changes
   no other fd's outbox or brokenness, and no readiness *)
Theorem stall_local:
  c ≠ d ⇒
  outbox_of (l1_after_send c r st) d = outbox_of st d ∧
  (MEM d (l1_after_send c r st).gone ⇔ MEM d st.gone) ∧
  (l1_after_send c r st).rdy = st.rdy
Proof
  Cases_on ‘r’ >> rw[l1_after_send_def, set_outbox_def, outbox_of_def,
                     ALOOKUP_ADELKEY]
QED

(* A broken connection is never shown to L2 as data afterwards: once gone,
   every read is EOF and makes no syscall *)
Theorem gone_is_eof:
  MEM c st.gone ⇒ l1_read c r st = (L2Got (SOME []), st) ∧ ¬l1_read_calls st c
Proof
  rw[l1_read_def, l1_read_calls_def]
QED

(* Out of fds: the listener is not polled for input until exhausted is
   cleared (by a close), so a blocking loop cannot spin on it *)
Theorem exhausted_quiet:
  st.exhausted ∧ MEM (lfd, ev) (l1_poll_set lfd hw st interest) ⇒ ev = 2
Proof
  rw[l1_poll_set_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[]
QED
