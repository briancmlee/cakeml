(*
  #46's select world and QuietSpec's give the same answers along runs
  that select only on the listener and accepted connections.

  The two oracles differ in one place: QuietSpec's select fails on an fd
  that is not a socket of the model (sel_ok), #46's does not.  Along a run
  whose every select names only the listener and fds that earlier accepts
  returned (ok_calls), every select is sel_ok, because the world keeps
  those fds as sockets (sock_inv): the listener stays, an accepted
  connection stays a connection (version 1 never closes), and a pending
  connection is already a connection.

  MAIN: oracle_agree, answers_agree.
*)
Theory asyncEchoBridgeWorld
Ancestors
  pair list rich_list arithmetic option llist alist words
  ffi ffiSpikeSocketFFI ffiSpikeSocketFair asyncM4BlkWorld asyncM4BlkLoop
  asyncM4BlkMain EchoSpec QuietSpec ffiAgreeUpto
Libs
  preamble

(* ------------------------------------------------------------------------
   The world keeps the listener and accepted connections
   ------------------------------------------------------------------------ *)

Definition sock_inv_def:
  sock_inv L A s ⇔
    is_listener s L ∧ (∀c. MEM c A ⇒ is_conn s c) ∧
    ∀l q c. ALOOKUP s.listeners l = SOME q ∧ MEM c q ⇒ is_conn s c
End

Theorem ALOOKUP_AFUPDKEY_NONE[local,simp]:
  ALOOKUP (AFUPDKEY k f l) c = NONE ⇔ ALOOKUP l c = NONE
Proof
  rw[AFUPDKEY_ALOOKUP] >> Cases_on ‘ALOOKUP l c’ >> simp[]
QED

Theorem sock_inv_sched[local,simp]:
  sock_inv L A (s with sched := x) ⇔ sock_inv L A s
Proof
  simp[sock_inv_def, is_listener_def, is_conn_def]
QED

Theorem deliver1_inv[local]:
  sock_inv L A s ⇒ sock_inv L A (deliver1 s a)
Proof
  Cases_on ‘a’ >>
  rw[sock_inv_def, deliver1_def, is_listener_def, is_conn_def, AFUPDKEY_ALOOKUP] >>
  gvs[AllCaseEqs()] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem FOLDL_deliver1_inv[local]:
  ∀as s. sock_inv L A s ⇒ sock_inv L A (FOLDL deliver1 s as)
Proof
  Induct >> simp[] >> metis_tac[deliver1_inv]
QED

Theorem tick_inv[local]:
  sock_inv L A s ⇒ sock_inv L A (tick s)
Proof
  rw[tick_def] >> CASE_TAC >> fs[deliver_def] >>
  irule FOLDL_deliver1_inv >> simp[]
QED

Theorem ticks_inv[local]:
  ∀k s. sock_inv L A s ⇒ sock_inv L A (ticks k s)
Proof
  Induct >> simp[ticks_def] >> metis_tac[tick_inv]
QED

(* The fd an answer to «sock_accept» hands out *)
Definition acc_new_def:
  acc_new n (out : word8 list) =
    if n = ExtCall «sock_accept» ∧ out ≠ [] ∧ HD out = 1w
    then [bytes_fd (TAKE 8 (TL out))] else []
End

Theorem sock_read_inv[local]:
  sock_read c n s = SOME (r, s') ∧ sock_inv L A s ⇒ sock_inv L A s'
Proof
  rw[sock_read_def, AllCaseEqs()] >> fs[sock_inv_def, is_listener_def, is_conn_def] >>
  metis_tac[]
QED

Theorem sock_write_inv[local]:
  sock_write c bs s = SOME s' ∧ sock_inv L A s ⇒ sock_inv L A s'
Proof
  rw[sock_write_def, AllCaseEqs()] >> fs[sock_inv_def, is_listener_def, is_conn_def] >>
  metis_tac[]
QED

Theorem sock_accept_inv[local]:
  sock_accept l s = SOME (r, s') ∧ sock_inv L A s ⇒
  sock_inv L (A ++ (case r of SOME c => [c] | NONE => [])) s'
Proof
  rw[sock_accept_def, AllCaseEqs()] >> fs[sock_inv_def] >>
  fs[is_listener_def, is_conn_def] >> rpt strip_tac >> gvs[] >>
  TRY (res_tac >> NO_TAC) >>
  TRY (‘MEM c (c :: q)’ by simp[] >> res_tac >> NO_TAC) >>
  rename1 ‘ALOOKUP (AFUPDKEY l _ _) l' = SOME q'’ >>
  Cases_on ‘l' = l’ >> gvs[AFUPDKEY_ALOOKUP]
  >- (‘MEM c' (c :: q)’ by fs[] >> res_tac)
  >> Cases_on ‘ALOOKUP s.listeners l'’ >> gvs[] >> res_tac
QED

(* One call of #46's world keeps the invariant, with what it accepted *)
Theorem ssel_step_inv:
  ssel_call m conf bs s = SOME (FFIreturn out s') ∧ sock_inv L A s ⇒
  sock_inv L (A ++ acc_new (ExtCall m) out) s'
Proof
  rw[ssel_call_def, ssel_ffi_part_def] >> gvs[AllCaseEqs()]
  >~ [‘ffi_sock_select _ _ _ = _’]
  >- (gvs[ffi_sock_select_def, AllCaseEqs(), acc_new_def] >> metis_tac[ticks_inv])
  >~ [‘ffi_sock_write _ _ _ = _’]
  >- (gvs[ffi_sock_write_def, AllCaseEqs(), acc_new_def] >> metis_tac[sock_write_inv])
  >~ [‘ffi_sock_read _ _ _ = _’]
  >- (gvs[ffi_sock_read_def, AllCaseEqs(), acc_new_def] >> metis_tac[sock_read_inv])
  >~ [‘ffi_sock_accept _ _ _ = _’]
  >- (gvs[ffi_sock_accept_def, AllCaseEqs(), acc_new_def] >>
      drule_all sock_accept_inv >> simp[] >>
      ‘∀c. TAKE 8 (fd_bytes c) = fd_bytes c’ by simp[TAKE_LENGTH_TOO_LONG] >>
      simp[])
  >> gvs[ffi_sock_poll_def, acc_new_def] >> metis_tac[tick_inv]
QED

(* ------------------------------------------------------------------------
   The two oracles
   ------------------------------------------------------------------------ *)

Theorem sock_wait_sel_wait[local]:
  sock_wait fds s = sel_wait fds s
Proof
  simp[sock_wait_def, sel_wait_def, ffiSpikeSocketSelectTheory.any_ready_def]
QED

(* MAIN: they agree on every call but a select of a non-socket *)
Theorem oracle_agree:
  sock_inv L A s ∧
  (n = ExtCall «sock_select» ⇒ EVERY (λfd. fd = L ∨ MEM fd A) (bytes_fds conf)) ⇒
  ssel_oracle n s conf bs = sel_oracle n s conf bs
Proof
  strip_tac >> Cases_on ‘n’ >> simp[ssel_oracle_def, sel_oracle_def] >>
  rename1 ‘ssel_call m conf bs s’ >>
  ‘ssel_call m conf bs s = case sel_fn m of SOME f => f conf bs s | NONE => NONE’
    suffices_by (disch_then SUBST1_TAC >> CASE_TAC >> simp[]) >>
  Cases_on ‘m = «sock_select»’
  >- (gvs[] >>
      ‘sel_ok s (bytes_fds conf)’
        by (simp[sel_ok_def, EVERY_MEM] >> rpt strip_tac >>
            gvs[EVERY_MEM, sock_inv_def] >> first_x_assum drule >> strip_tac >>
            gvs[] >> metis_tac[]) >>
      simp[ssel_call_def, ssel_ffi_part_def, sel_fn_def,
           ffi_sock_select_def, ffi_select_def, sock_wait_sel_wait]) >>
  simp[ssel_call_def, ssel_ffi_part_def, sel_fn_def, socket_fn_def] >>
  rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   Along a run
   ------------------------------------------------------------------------ *)

(* Every select names only the listener and fds handed out before, given
   the answers of the run *)
Definition ok_calls_def:
  ok_calls L A [] anss = T ∧
  ok_calls L A ((n, c, b) :: cs) anss =
    ((n = ExtCall «sock_select» ⇒ EVERY (λfd. fd = L ∨ MEM fd A) (bytes_fds c)) ∧
     case anss of
     | INL out :: rest => ok_calls L (A ++ acc_new n out) cs rest
     | _ => T)
End

(* MAIN: along such a run, the two worlds answer the same *)
Theorem answers_agree:
  ∀cs A s. sock_inv L A s ∧ ok_calls L A cs (ffi_answers (ssel_ffi s) cs) ⇒
           ffi_answers (ssel_ffi s) cs = ffi_answers (select_ffi s) cs
Proof
  Induct >> simp[ffi_answers_def, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  rename1 ‘(n, c, b) :: cs’ >>
  gvs[ok_calls_def, ffi_answers_def, ssel_ffi_def, select_ffi_def] >>
  ‘ssel_oracle n s c b = sel_oracle n s c b’
    by (irule oracle_agree >> metis_tac[]) >>
  gvs[] >> CASE_TAC >> gvs[] >>
  rename1 ‘Oracle_return s' out’ >>
  first_x_assum irule >> qexists_tac ‘A ++ acc_new n out’ >> simp[] >>
  Cases_on ‘n’ >> gvs[sel_oracle_def, AllCaseEqs()] >>
  ‘ssel_call m c b s = SOME (FFIreturn out s')’
    by fs[ssel_oracle_def, AllCaseEqs()] >>
  drule_all ssel_step_inv >> simp[]
QED

(* ... and on every prefix of it *)
Theorem answers_agree_prefix:
  ∀cs A s. sock_inv L A s ∧ ok_calls L A cs (ffi_answers (ssel_ffi s) cs) ⇒
           ∀cs'. cs' ≼ cs ⇒
                 ffi_answers (ssel_ffi s) cs' = ffi_answers (select_ffi s) cs'
Proof
  Induct >> simp[ffi_answers_def, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  Cases >> simp[ffi_answers_def] >> PairCases_on ‘h’ >> strip_tac >> gvs[] >>
  rename1 ‘(n, c, b) :: cs’ >>
  gvs[ok_calls_def, ffi_answers_def, ssel_ffi_def, select_ffi_def] >>
  ‘ssel_oracle n s c b = sel_oracle n s c b’
    by (irule oracle_agree >> metis_tac[]) >>
  gvs[] >> CASE_TAC >> gvs[] >>
  rename1 ‘Oracle_return s' out’ >>
  first_x_assum irule >> simp[] >> qexists_tac ‘A ++ acc_new n out’ >> simp[] >>
  Cases_on ‘n’ >> gvs[sel_oracle_def, AllCaseEqs()] >>
  ‘ssel_call m c b s = SOME (FFIreturn out s')’
    by fs[ssel_oracle_def, AllCaseEqs()] >>
  drule_all ssel_step_inv >> simp[]
QED
