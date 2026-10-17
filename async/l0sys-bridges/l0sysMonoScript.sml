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
