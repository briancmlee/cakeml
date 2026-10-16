(*
  L3-09 (S3), the trace-only part: polls are not observed by the echo's
  raw-trace vocabulary.  The accepted fds, the bytes read and sent per
  episode, and episodes being open or closed read accept, recv, send and
  close events only, so they are unchanged by removing polls (nopoll), and
  evrel-related traces (the blocking run's and the PF run's) agree on them.

  MAIN: evrel_nopoll, nopoll_accepted, nopoll_sent, nopoll_read.
*)
Theory honestL1BObs
Ancestors
  honestL1BSim honestL1BStmts honestEchoL0Spec ffi
Libs
  preamble

Definition is_poll_def:
  is_poll (IO_event n conf bs) ⇔ n = ExtCall «sys_poll»
End

Definition nopoll_def:
  nopoll evs = FILTER (λev. ¬is_poll ev) evs
End

Theorem nopoll_append[simp]:
  nopoll (xs ++ ys) = nopoll xs ++ nopoll ys
Proof
  simp[nopoll_def, FILTER_APPEND]
QED

Theorem epoll_is_poll:
  epoll fes ev ⇒ is_poll ev
Proof
  rw[epoll_def] >> simp[is_poll_def]
QED

Theorem nopoll_epolls:
  EVERY (epoll fes) es ⇒ nopoll es = []
Proof
  rw[nopoll_def, FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[epoll_is_poll]
QED

(* MAIN *)
Theorem evrel_nopoll:
  ∀pevs bevs. evrel pevs bevs ⇒ nopoll pevs = nopoll bevs
Proof
  Induct_on ‘evrel’ >> rw[] >> imp_res_tac nopoll_epolls >>
  simp[nopoll_def, is_poll_def]
QED

Theorem poll_not_accepted:
  is_poll ev ⇒ l0_event_accepted ev = NONE ∧ l0_event_closed ev = NONE ∧
               (∀f. l0_event_recv f ev = []) ∧ (∀f. l0_event_sent f ev = [])
Proof
  Cases_on ‘ev’ >> rw[is_poll_def] >>
  simp[l0_event_accepted_def, l0_event_closed_def, l0_event_recv_def, l0_event_sent_def]
QED

Theorem nopoll_accepted:
  ∀evs. l0_accepted (nopoll evs) = l0_accepted evs
Proof
  Induct >> simp[nopoll_def, l0_accepted_def] >> rw[] >>
  fs[nopoll_def, l0_accepted_def] >> imp_res_tac poll_not_accepted >> simp[]
QED

Theorem ep_events_nopoll:
  ∀evs j k opn. l0_ep_events j k opn (nopoll evs) = nopoll (l0_ep_events j k opn evs)
Proof
  Induct >> simp[nopoll_def, l0_ep_events_def] >> rw[] >>
  fs[nopoll_def, l0_ep_events_def] >> imp_res_tac poll_not_accepted >> simp[] >>
  every_case_tac >> simp[FILTER_APPEND] >> rw[] >> fs[]
QED

Theorem FLAT_MAP_nopoll[local]:
  (∀ev. is_poll ev ⇒ f ev = []) ⇒ FLAT (MAP f (nopoll l)) = FLAT (MAP f l)
Proof
  strip_tac >> Induct_on ‘l’ >> simp[nopoll_def] >> rw[] >> fs[nopoll_def]
QED

Theorem nopoll_sent:
  l0_sent j (nopoll evs) = l0_sent j evs
Proof
  simp[l0_sent_def, nopoll_accepted, ep_events_nopoll] >> rw[] >>
  irule FLAT_MAP_nopoll >> metis_tac[poll_not_accepted]
QED

Theorem nopoll_read:
  l0_read j (nopoll evs) = l0_read j evs
Proof
  simp[l0_read_def, nopoll_accepted, ep_events_nopoll] >> rw[] >>
  irule FLAT_MAP_nopoll >> metis_tac[poll_not_accepted]
QED

Theorem EVERY_closed_nopoll[local]:
  EVERY (λe. l0_event_closed e ≠ SOME f) (nopoll l) ⇔
  EVERY (λe. l0_event_closed e ≠ SOME f) l
Proof
  Induct_on ‘l’ >> simp[nopoll_def] >> rw[] >> fs[nopoll_def] >>
  imp_res_tac poll_not_accepted >> simp[]
QED

Theorem EXISTS_closed_nopoll[local]:
  EXISTS (λe. l0_event_closed e = SOME f) (nopoll l) ⇔
  EXISTS (λe. l0_event_closed e = SOME f) l
Proof
  Induct_on ‘l’ >> simp[nopoll_def] >> rw[] >> fs[nopoll_def] >>
  imp_res_tac poll_not_accepted >> simp[]
QED

Theorem accepted_not_poll[local]:
  l0_event_accepted ev = SOME f ⇒ ¬is_poll ev
Proof
  metis_tac[poll_not_accepted, optionTheory.NOT_NONE_SOME]
QED

Theorem nopoll_split[local]:
  nopoll l = a ++ [ev] ++ b ⇒
  ∃a' b'. l = a' ++ [ev] ++ b' ∧ nopoll a' = a ∧ nopoll b' = b
Proof
  rw[nopoll_def] >> fs[FILTER_EQ_APPEND, FILTER_EQ_CONS] >> gvs[] >>
  qexistsl_tac [‘l3' ++ l1’, ‘l2 ++ l4’] >> REWRITE_TAC[APPEND_ASSOC] >> simp[FILTER_APPEND]
QED

(* MAIN *)
Theorem ep_open_nopoll:
  ep_open j (nopoll evs) ⇔ ep_open j evs
Proof
  rw[ep_open_def, EQ_IMP_THM]
  >- (drule nopoll_split >> strip_tac >> gvs[] >>
      qexistsl_tac [‘a'’, ‘ev’, ‘b'’, ‘f’] >>
      gvs[nopoll_accepted, EVERY_closed_nopoll])
  >> qexistsl_tac [‘nopoll pre’, ‘ev’, ‘nopoll post’, ‘f’] >>
  imp_res_tac accepted_not_poll >>
  simp[nopoll_accepted, EVERY_closed_nopoll] >> simp[nopoll_def]
QED

Theorem ep_closed_nopoll:
  ep_closed j (nopoll evs) ⇔ ep_closed j evs
Proof
  rw[ep_closed_def, EQ_IMP_THM]
  >- (drule nopoll_split >> strip_tac >> gvs[] >>
      qexistsl_tac [‘a'’, ‘ev’, ‘b'’, ‘f’] >>
      gvs[nopoll_accepted, EXISTS_closed_nopoll])
  >> qexistsl_tac [‘nopoll pre’, ‘ev’, ‘nopoll post’, ‘f’] >>
  imp_res_tac accepted_not_poll >>
  simp[nopoll_accepted, EXISTS_closed_nopoll] >> simp[nopoll_def]
QED
