(*
  The end-to-end example's model side: a library computation that waits
  until listener 3 is ready and then accepts a connection on it,

      accept3 = bind (wait ready3) (λu. emit (Accept 3w)),

  and the fact that no run of it against the socket world is a misuse
  (srun_ok), provided 3 is a listener in the initial world: its only
  action is Accept 3w, and listeners are never removed.
*)
Theory asyncM3ExampleModel
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncM3World
  ffiSpikeSocketFFI alist
Libs
  preamble

(* Listener 3 is ready in this snapshot *)
Definition ready3_def:
  ready3 (sn : (word64, sresp) snapshot) =
    if 3w ∈ sn.ready then SOME () else NONE
End

(* Wait until listener 3 is ready, then accept a connection on it *)
Definition accept3_def:
  accept3 = bind (wait ready3) (λu. emit (Accept 3w))
End

Theorem wf_accept3:
  wf accept3
Proof
  simp[accept3_def] >> irule wf_bind >> simp[wf_wait, wf_emit]
QED

(* accept3 only ever emits Accept 3w, once *)
Theorem accept3_actions:
  (accept3 h).actions = [] ∨ (accept3 h).actions = [Accept 3w]
Proof
  simp[accept3_def, bind_def] >> CASE_TAC >> simp[wait_def, emit_def]
QED

Theorem new_actions_accept3:
  new_actions (log_of accept3) h = [] ∨
  new_actions (log_of accept3) h = [Accept 3w]
Proof
  rw[new_actions_def, log_of_def, accept3_actions] >>
  qspec_then ‘h’ strip_assume_tac (Q.GEN ‘h’ accept3_actions) >>
  qspec_then ‘FRONT h’ strip_assume_tac (Q.GEN ‘h’ accept3_actions) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Listeners are never removed
   ------------------------------------------------------------------------ *)

Theorem is_listener_AFUPDKEY[local]:
  ALOOKUP (AFUPDKEY k f al) x ≠ NONE ⇔ ALOOKUP al x ≠ NONE
Proof
  simp[AFUPDKEY_ALOOKUP] >> every_case_tac >> simp[]
QED

Theorem is_listener_deliver1[local]:
  is_listener s l ⇒ is_listener (deliver1 s a) l
Proof
  Cases_on ‘a’ >> rw[deliver1_def, is_listener_def, is_listener_AFUPDKEY]
QED

Theorem is_listener_deliver[local]:
  ∀arrs s. is_listener s l ⇒ is_listener (deliver s arrs) l
Proof
  Induct >> rw[deliver_def] >> fs[GSYM deliver_def] >>
  metis_tac[is_listener_deliver1]
QED

Theorem is_listener_tick:
  is_listener s l ⇒ is_listener (tick s) l
Proof
  rw[tick_def] >> CASE_TAC >> simp[] >>
  irule is_listener_deliver >> fs[is_listener_def]
QED

Theorem is_listener_sock_accept:
  sock_accept l' s = SOME (r, s') ∧ is_listener s l ⇒ is_listener s' l
Proof
  rw[sock_accept_def, AllCaseEqs()] >> gvs[is_listener_def, is_listener_AFUPDKEY]
QED

(* ------------------------------------------------------------------------
   No misuse in any run of accept3
   ------------------------------------------------------------------------ *)

Theorem sock_acts_accept3_round[local]:
  is_listener s 3w ∧ (acts = [] ∨ acts = [Accept 3w]) ⇒
  ∃rs evs s'. sock_acts s acts = SOME (rs, evs, s') ∧ is_listener s' 3w
Proof
  rw[] >> simp[sock_acts_def, sock_do_def] >>
  Cases_on ‘sock_accept 3w s’
  >- gvs[sock_accept_def, is_listener_def, AllCaseEqs()] >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >> simp[sock_acts_def] >>
  drule_all is_listener_sock_accept >> simp[]
QED

Theorem is_listener_srounds[local]:
  is_listener s0 3w ⇒ ∀n. is_listener (SND (srounds fds accept3 s0 n)) 3w
Proof
  strip_tac >> Induct >- simp[srounds_def] >>
  simp[srounds_SUC, sock_poll_def] >> irule is_listener_tick >>
  qabbrev_tac ‘s = SND (srounds fds accept3 s0 n)’ >>
  qabbrev_tac ‘acts = new_actions (log_of accept3) (FST (srounds fds accept3 s0 n))’ >>
  ‘acts = [] ∨ acts = [Accept 3w]’ by simp[Abbr ‘acts’, new_actions_accept3] >>
  mp_tac (Q.INST [‘acts’ |-> ‘acts’, ‘s’ |-> ‘s’] sock_acts_accept3_round) >>
  impl_tac >- simp[] >> rw[] >> simp[sock_acts_tot_def]
QED

(* MAIN: if 3 is a listener in the initial world, no run of accept3 against
   the socket world contains a misuse. *)
Theorem srun_ok_accept3:
  is_listener s0 3w ⇒ srun_ok fds accept3 s0
Proof
  rw[srun_ok_def] >>
  drule is_listener_srounds >> disch_then (qspecl_then [‘fds’, ‘n’] assume_tac) >>
  qspec_then ‘FST (srounds fds accept3 s0 n)’ assume_tac
    (Q.GEN ‘h’ new_actions_accept3) >>
  drule_all sock_acts_accept3_round >> rw[] >> simp[]
QED
