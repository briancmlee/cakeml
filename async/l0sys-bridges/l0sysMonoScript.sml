(*
  How a process's own steps change its channels (for B2's system
  invariant): what a channel has sent only grows, what its peer sent
  changes only by an arrival of data, a channel that stopped taking data
  (peer EOF, broken, closed) stays so, a channel stops connecting but never
  starts again, and a new channel starts empty.  wmono w w' says so for a
  call or an arrival other than data.
*)
Theory l0sysMono
Ancestors
  honestL0 honestL0World honestL0Rely l0sys l0sysInv l0sysInvCall
Libs
  preamble

(* A channel that drops arriving data *)
Definition frozen_def:
  frozen (c : lchan) ⇔ c.peer_eof ∨ c.broken ∨ c.closed
End

Definition cmono_def:
  cmono (x : lchan) y ⇔
    x.sent ≼ y.sent ∧ y.peer_sent = x.peer_sent ∧ (frozen x ⇒ frozen y) ∧
    (y.connecting ⇒ x.connecting ∧ y.sent = x.sent)
End

Definition wmono_def:
  wmono (w : l0world) w' ⇔
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀c. c < LENGTH w.chans ⇒ cmono (EL c w.chans) (EL c w'.chans)) ∧
    (∀c. LENGTH w.chans ≤ c ∧ c < LENGTH w'.chans ⇒
         (EL c w'.chans).sent = [] ∧ (EL c w'.chans).peer_sent = [])
End

Theorem cmono_refl[simp]:
  cmono x x
Proof
  simp[cmono_def]
QED

Theorem cmono_trans:
  cmono x y ∧ cmono y z ⇒ cmono x z
Proof
  rw[cmono_def] >> metis_tac[IS_PREFIX_TRANS]
QED

Theorem wmono_refl[simp]:
  wmono w w
Proof
  simp[wmono_def]
QED

Theorem wmono_upd:
  wmono w w' ∧ (j < LENGTH w'.chans ⇒ cmono (EL j w'.chans) (g (EL j w'.chans))) ∧
  (j < LENGTH w.chans ∨ (g (EL j w'.chans)).sent = (EL j w'.chans).sent) ⇒
  wmono w (upd_lchan j g w')
Proof
  rw[wmono_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[] >>
  TRY (irule cmono_trans >> qexists_tac ‘EL c w'.chans’ >> fs[] >> NO_TAC) >>
  fs[cmono_def]
QED

Theorem wmono_fields:
  wmono w w' ⇒
  wmono w (w' with open_fds := X) ∧ wmono w (w' with listeners := L) ∧
  wmono w (w' with reserved := R) ∧ wmono w (w' with <| clock := n; hist := h |>) ∧
  wmono w (w' with <| listeners := L; open_fds := X |>)
Proof
  simp[wmono_def]
QED

Theorem wmono_append:
  wmono w w' ∧ c0.sent = [] ∧ c0.peer_sent = [] ⇒
  wmono w (w' with chans := w'.chans ++ [c0]) ∧
  wmono w (w' with <| chans := w'.chans ++ [c0]; open_fds := X |>) ∧
  wmono w (w' with <| listeners := L; chans := w'.chans ++ [c0] |>)
Proof
  rw[wmono_def] >> rw[EL_APPEND1, EL_APPEND2] >>
  Cases_on ‘c < LENGTH w'.chans’ >> gvs[EL_APPEND1, EL_APPEND2] >>
  ‘c = LENGTH w'.chans’ by simp[] >> gvs[]
QED

Theorem cmono_break[simp]:
  cmono x (break_lchan e k x)
Proof
  rw[cmono_def, break_lchan_def, frozen_def]
QED

Theorem wmono_breaks:
  ∀q w'. wmono w w' ⇒ wmono w (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w' q)
Proof
  Induct >> rw[] >> first_x_assum irule >> irule wmono_upd >> simp[] >>
  disj2_tac >> rw[break_lchan_def]
QED

Theorem wmono_close_fd:
  wmono w w' ⇒ wmono w (close_fd f w')
Proof
  rw[close_fd_def] >> every_case_tac >> gvs[wmono_fields] >>
  TRY (irule wmono_breaks >> simp[wmono_fields] >> NO_TAC) >>
  irule wmono_upd >> simp[wmono_fields, cmono_def, frozen_def]
QED

(*---------------------------------------------------------------------------*)
(* Calls *)

Theorem l0_chan_of_lt:
  l0_chan_of w f = SOME j ⇒ j < LENGTH w.chans
Proof
  rw[l0_chan_of_def, AllCaseEqs()]
QED

Theorem wmono_call:
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒ wmono w w1
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> simp[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [
    gvs[l0_listen_def, AllCaseEqs(), wmono_fields] >> NO_TAC,
    drule l0_accept_cases >> strip_tac >> gvs[wmono_fields] >>
    TRY (irule wmono_upd >> simp[wmono_fields] >> disj2_tac >> rw[break_lchan_def]) >> NO_TAC,
    drule l0_recv_cases >> strip_tac >> gvs[] >>
    irule wmono_upd >> simp[cmono_def, frozen_def] >> metis_tac[l0_chan_of_lt],
    drule l0_send_cases >> strip_tac >> gvs[] >>
    irule wmono_upd >> simp[cmono_def, frozen_def] >> metis_tac[l0_chan_of_lt],
    gvs[l0_shutdown_def, AllCaseEqs()] >>
    irule wmono_upd >> simp[cmono_def, frozen_def] >> metis_tac[l0_chan_of_lt],
    drule l0_connect_cases >> strip_tac >> gvs[] >>
    TRY (irule wmono_upd >> simp[cmono_def, frozen_def]) >>
    irule (cj 2 wmono_append) >> simp[fresh_lchan_def] >> NO_TAC,
    gvs[l0_connerr_def, AllCaseEqs()] >>
    irule wmono_upd >> simp[cmono_def, frozen_def] >> metis_tac[l0_chan_of_lt],
    gvs[l0_close_def, AllCaseEqs()] >> rw[wmono_close_fd]]
QED

(*---------------------------------------------------------------------------*)
(* Arrivals *)

Theorem wmono_deliver:
  (∀j bs. a ≠ LData j bs) ⇒ wmono w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  TRY (irule (cj 3 wmono_append) >> simp[fresh_lchan_def] >> NO_TAC) >>
  irule wmono_upd >> simp[cmono_def, frozen_def, break_lchan_def] >> rw[]
QED

(* Data arriving at channel j: it reaches the peer's stream unless the
   channel drops it *)
Theorem deliver_data:
  LENGTH (l0_deliver w (LData j bs)).chans = LENGTH w.chans ∧
  ∀c. c < LENGTH w.chans ⇒
      (EL c (l0_deliver w (LData j bs)).chans).sent = (EL c w.chans).sent ∧
      ((EL c (l0_deliver w (LData j bs)).chans).connecting ⇔ (EL c w.chans).connecting) ∧
      (frozen (EL c (l0_deliver w (LData j bs)).chans) ⇔ frozen (EL c w.chans)) ∧
      (EL c (l0_deliver w (LData j bs)).chans).peer_sent =
      if c = j ∧ ¬frozen (EL c w.chans) ∧ ¬(EL c w.chans).connecting
      then (EL c w.chans).peer_sent ++ bs else (EL c w.chans).peer_sent
Proof
  rw[l0_deliver_def, upd_lchan_def, EL_LUPDATE, frozen_def] >> rw[] >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* Queues: no call queues a connection; an arrival queues only a new one *)

Definition queued_def:
  queued (w : l0world) c ⇔ ∃l p q. MEM (l, p, q) w.listeners ∧ MEM c q
End

Theorem queued_upd[simp]:
  queued (upd_lchan j g w) c ⇔ queued w c
Proof
  simp[queued_def]
QED

Theorem MEM_AFUPDKEY_imp:
  ∀L. MEM (a, b) (AFUPDKEY k f L) ⇒ MEM (a, b) L ∨ ∃b0. MEM (k, b0) L ∧ b = f b0
Proof
  Induct >> simp[AFUPDKEY_def] >> Cases >> rw[AFUPDKEY_def] >> metis_tac[]
QED

Theorem queued_breaks:
  ∀q w. queued (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q) c ⇔ queued w c
Proof
  Induct >> simp[]
QED

Theorem queued_close_fd:
  queued (close_fd f w) c ⇒ queued w c
Proof
  rw[close_fd_def] >> every_case_tac >> gvs[queued_breaks] >>
  gvs[queued_def, MEM_FILTER] >> metis_tac[]
QED

Theorem queued_pop:
  FILTER (λ(l', p, q). l' = l) w.listeners = (l1, p, j :: q') :: t ∧
  MEM (a, p', q'') (AFUPDKEY l (K (p, q')) w.listeners) ∧ MEM c q'' ⇒ queued w c
Proof
  strip_tac >> drule MEM_AFUPDKEY_imp >> rw[queued_def]
  >- metis_tac[] >>
  ‘MEM (l1, p, j :: q') (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
  gvs[MEM_FILTER] >> metis_tac[MEM]
QED

Theorem queued_call:
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧ queued w1 c ⇒
  queued w c
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> strip_tac >> gvs[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (FIRST [
    gvs[l0_listen_def, AllCaseEqs(), queued_def] >> metis_tac[MEM],
    drule l0_accept_cases >> strip_tac >> gvs[] >>
    gvs[queued_def] >> metis_tac[queued_pop, queued_def],
    drule l0_recv_cases >> strip_tac >> gvs[] >> NO_TAC,
    drule l0_send_cases >> strip_tac >> gvs[] >> NO_TAC,
    gvs[l0_shutdown_def, AllCaseEqs()] >> NO_TAC,
    drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[queued_def] >> NO_TAC,
    gvs[l0_connerr_def, AllCaseEqs()] >> NO_TAC,
    gvs[l0_close_def, AllCaseEqs()] >> metis_tac[queued_close_fd]]) >>
  drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[queued_def, fail_def] >>
  metis_tac[]
QED

Theorem queued_deliver:
  queued (l0_deliver w a) c ⇒ queued w c ∨ c = LENGTH w.chans
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  gvs[queued_def] >> drule MEM_AFUPDKEY_imp >> rw[] >> gvs[] >- metis_tac[] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED
