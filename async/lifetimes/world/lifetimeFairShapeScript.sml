(*
  The version-2 fairness assumption lifetime_fair only depends on the world's
  SHAPE (its listeners, its clients' EOF flags, its reserved fds and its
  schedule), which the program's operations do not change.  So it holds
  throughout a run: lifetime_fair_ops, lifetime_fair_tick.
*)
Theory lifetimeFairShape
Ancestors
  llist alist socketWorld lifetimeWorld lifetimeFair
Libs
  preamble

Definition shape2_def:
  shape2 s = (MAP FST s.listening, MAP (λcn. cn.peer_closed) s.clients,
              s.reserved, s.future)
End

Theorem EL_MAP_peer_closed[local]:
  MAP (λcn. cn.peer_closed) l1 = MAP (λcn. cn.peer_closed) l2 ∧ j < LENGTH l1 ⇒
  (EL j l1).peer_closed = (EL j l2).peer_closed
Proof
  rw[] >> ‘LENGTH l1 = LENGTH l2’ by metis_tac[LENGTH_MAP] >>
  qpat_x_assum ‘MAP _ _ = MAP _ _’ (mp_tac o Q.AP_TERM ‘EL j’) >> simp[EL_MAP]
QED

Theorem arrival_ok2_shape:
  shape2 s = shape2 t ⇒ (arrival_ok2 s a ⇔ arrival_ok2 t a)
Proof
  Cases_on ‘a’ >> rw[shape2_def, arrival_ok2_def] >>
  ‘LENGTH s.clients = LENGTH t.clients ∧ LENGTH s.listening = LENGTH t.listening’
    by metis_tac[LENGTH_MAP] >>
  gvs[] >> TRY (eq_tac >> rw[] >> gvs[] >> metis_tac[EL_MAP_peer_closed]) >>
  simp[ALOOKUP_NONE] >> metis_tac[]
QED

Theorem MAP_FST_AFUPDKEY_any[local]:
  MAP FST (AFUPDKEY k f l) = MAP FST l
Proof
  simp[]
QED

Theorem deliver2_shape:
  shape2 s = shape2 t ⇒ shape2 (deliver2 s a) = shape2 (deliver2 t a)
Proof
  Cases_on ‘a’ >> rw[shape2_def, deliver2_def, update_client_def] >>
  ‘LENGTH s.clients = LENGTH t.clients’ by metis_tac[LENGTH_MAP] >>
  gvs[ALOOKUP_NONE] >>
  TRY (metis_tac[EL_MAP_peer_closed]) >>
  simp[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[] >>
  metis_tac[EL_MAP_peer_closed]
QED

Theorem FOLDL_deliver2_shape:
  ∀as s t. shape2 s = shape2 t ⇒
           shape2 (FOLDL deliver2 s as) = shape2 (FOLDL deliver2 t as)
Proof
  Induct >> simp[] >> metis_tac[deliver2_shape]
QED

Theorem step_ok2_shape:
  ∀as s t. shape2 s = shape2 t ⇒ (step_ok2 s as ⇔ step_ok2 t as)
Proof
  Induct >> simp[step_ok2_def] >> metis_tac[arrival_ok2_shape, deliver2_shape]
QED

Theorem shape2_future[local]:
  shape2 s = shape2 t ⇒ s.future = t.future
Proof
  simp[shape2_def]
QED

Theorem tick2_shape:
  shape2 s = shape2 t ⇒ shape2 (tick2 s) = shape2 (tick2 t)
Proof
  rw[tick2_def] >> imp_res_tac shape2_future >> simp[] >> CASE_TAC >> simp[] >>
  irule FOLDL_deliver2_shape >> gvs[shape2_def]
QED

Theorem ticks2_shape:
  ∀n s t. shape2 s = shape2 t ⇒ shape2 (ticks2 n s) = shape2 (ticks2 n t)
Proof
  Induct >> simp[ticks2_def] >> metis_tac[tick2_shape]
QED

Theorem next_step2_shape[local]:
  shape2 s = shape2 t ⇒ next_step2 s = next_step2 t
Proof
  simp[next_step2_def] >> metis_tac[shape2_future]
QED

(* MAIN: fairness depends only on the shape *)
Theorem lifetime_fair_shape:
  shape2 s = shape2 t ⇒ (lifetime_fair s ⇔ lifetime_fair t)
Proof
  rw[lifetime_fair_def] >> eq_tac >> rw[] >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  ‘shape2 (ticks2 n s) = shape2 (ticks2 n t)’ by metis_tac[ticks2_shape] >>
  metis_tac[step_ok2_shape, next_step2_shape]
QED

(* The program's operations leave the shape alone *)
Theorem ops_shape:
  (sock_accept2 l s = SOME (r, s') ⇒ shape2 s' = shape2 s) ∧
  (sock_read2 c n s = SOME (d, s') ⇒ shape2 s' = shape2 s) ∧
  (sock_write2 c bs s = SOME s' ⇒ shape2 s' = shape2 s) ∧
  (sock_close2 c s = SOME s' ⇒ shape2 s' = shape2 s)
Proof
  rw[sock_accept2_def, sock_read2_def, sock_write2_def, sock_close2_def,
     AllCaseEqs(), update_client_def, shape2_def, client_of_def] >>
  gvs[] >> simp[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[]
QED

(* MAIN: fairness holds after the program's operations and after a tick,
   and the next step's arrivals are effective *)
Theorem lifetime_fair_ops:
  lifetime_fair s ⇒
  (sock_accept2 l s = SOME (r, s') ⇒ lifetime_fair s') ∧
  (sock_read2 c n s = SOME (d, s') ⇒ lifetime_fair s') ∧
  (sock_write2 c bs s = SOME s' ⇒ lifetime_fair s') ∧
  (sock_close2 c s = SOME s' ⇒ lifetime_fair s')
Proof
  rw[] >> imp_res_tac ops_shape >> metis_tac[lifetime_fair_shape]
QED

Theorem lifetime_fair_tick:
  lifetime_fair s ⇒ lifetime_fair (tick2 s) ∧ step_ok2 s (next_step2 s)
Proof
  rw[lifetime_fair_def]
  >- (first_x_assum (qspec_then ‘SUC n’ mp_tac) >> simp[ticks2_def])
  >> first_x_assum (qspec_then ‘0’ mp_tac) >> simp[ticks2_def]
QED
