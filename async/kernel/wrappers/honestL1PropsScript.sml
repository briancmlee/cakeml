(*
  What L1 guarantees, round by round (proved; design/36 §5.1).

   - read_no_syscall: the ROUND DISCIPLINE.  A Read of a handle whose fd
     the round's poll did not report readable (or a call has since found
     empty) answers "would block" and makes no L0 call;
   - recv_found_empty: after a recv found an fd empty (EAGAIN or a
     transient error) the fd leaves the round's readable set, so no second
     recv on it happens in the round;
   - gone_is_eof: once an fd's connection broke, L2 reads EOF on its handle
     and the fd is closed: L2 never sees data from a broken connection;
   - stall_local: a send's result on one fd changes no other fd's outbox
     or brokenness (a slow reader stalls only itself);
   - write_buffered: a Write to an fd with a non-empty outbox makes no L0
     call and answers Wrote at once;
   - exhausted_quiet: while out of fds, the listener is not polled for
     input (so a blocking loop cannot spin on it);
   - paused_quiet: an fd whose outbox is above the high-water mark is
     polled for output only (L2 is not told it is readable).
*)
Theory honestL1Props
Ancestors
  honestL1Model honestL0 loopPollWorld alist
Libs
  preamble

Theorem read_no_syscall:
  0 < n ∧ n < 256 ** 8 ∧ ALOOKUP st.tbl h = SOME f ∧ ¬MEM f st.gone ∧ ¬MEM f st.rdy ⇒
  l1do lfd (w, st) (Read h n) = SOME (Got NONE, (w, st), [])
Proof
  rw[l1do_def]
QED

Theorem recv_found_empty:
  0 < n ∧ n < 256 ** 8 ∧ ALOOKUP st.tbl h = SOME f ∧ ¬MEM f st.gone ∧ MEM f st.rdy ∧
  sys_recv f n w = SOME (out, w', ev) ∧ l0_res_of out = Fail e raw ∧ l1_transient e ⇒
  l1do lfd (w, st) (Read h n) = SOME (Got NONE, (w', st with rdy := FILTER ($≠ f) st.rdy), [ev]) ∧
  ¬MEM f (FILTER ($≠ f) st.rdy)
Proof
  rw[l1do_def, MEM_FILTER]
QED

Theorem gone_is_eof:
  0 < n ∧ n < 256 ** 8 ∧ ALOOKUP st.tbl h = SOME f ∧ MEM f st.gone ∧
  sys_close f w = SOME (out, w', ev) ⇒
  ∃st'. l1do lfd (w, st) (Read h n) = SOME (Got (SOME []), (w', st'), [ev]) ∧
        ALOOKUP st'.tbl h = NONE ∧ ¬MEM f st'.gone ∧ outbox_of st' f = []
Proof
  strip_tac >> simp[l1do_def, l1_close_def] >>
  simp[forget_def, set_outbox_def, outbox_of_def, ALOOKUP_ADELKEY, MEM_FILTER]
QED

Theorem outbox_of_set_outbox:
  outbox_of (set_outbox f bs st) d = if d = f then bs else outbox_of st d
Proof
  rw[outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >> rw[]
QED

Theorem stall_local:
  d ≠ f ⇒
  outbox_of (after_send f r st) d = outbox_of st d ∧
  (MEM d (after_send f r st).gone ⇔ MEM d st.gone) ∧
  (after_send f r st).rdy = st.rdy ∧
  (after_send f r st).tbl = st.tbl
Proof
  strip_tac >> Cases_on ‘r’ >> simp[after_send_def] >>
  TRY IF_CASES_TAC >>
  simp[outbox_of_set_outbox] >> simp[set_outbox_def, MEM_FILTER, outbox_of_def] >>
  rw[] >> gvs[]
QED

Theorem write_buffered:
  ALOOKUP st.tbl h = SOME f ∧ ¬MEM f st.gone ∧ outbox_of st f ≠ [] ⇒
  l1do lfd (w, st) (Write h bs) =
    SOME (Wrote, (w, set_outbox f (outbox_of st f ++ bs) st), [])
Proof
  rw[l1do_def]
QED

Theorem exhausted_quiet:
  st.exhausted ∧ ¬MEM lfd (MAP SND st.tbl) ∧ MEM (lfd, e) (l1_poll_set lfd hw st hs) ⇒
  e = 2
Proof
  rw[l1_poll_set_def, MEM_FLAT, MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
  Cases_on ‘ALOOKUP st.tbl h’ >> gvs[] >> every_case_tac >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[]
QED

Theorem paused_quiet:
  hw < LENGTH (outbox_of st f) ∧ f ≠ lfd ∧ MEM (f, e) (l1_poll_set lfd hw st hs) ⇒
  e = 2
Proof
  rw[l1_poll_set_def, MEM_FLAT, MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
  Cases_on ‘ALOOKUP st.tbl h’ >> gvs[] >> every_case_tac >> gvs[]
QED
