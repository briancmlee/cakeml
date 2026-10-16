(*
  Version-2 worlds whose schedules agree on their first k steps answer
  alike any sequence of calls with at most k polls (v2_answers_prefix).
  With ffiAgreeUpto, a program that polls fewer than k times in one of
  them behaves the same in the other: it cannot know the future.
*)
Theory peerV2Prefix
Ancestors
  llist ffi semantics ml_prog lifetimeWorld lifetimeFair EchoEpisodesSpec peerV2Sim peerEchoEpisodes
  ffiAgreeUpto
Libs
  preamble

Definition npolls_def:
  npolls (cs : (ffiname # word8 list # word8 list) list) =
    LENGTH (FILTER (λ(n, c, b). n = ExtCall «sock_poll») cs)
End

(* Two states that differ at most in their futures *)
Definition sbf_def:
  sbf (s1:sockets2) s2 ⇔ s1 with future := [||] = s2 with future := [||]
End

Definition fut_agree_def:
  fut_agree k f1 f2 ⇔ ∀i. i < k ⇒ fut_step f1 i = fut_step f2 i
End

Theorem sbf_fields:
  sbf s1 s2 ⇒
  s1.listening = s2.listening ∧ s1.clients = s2.clients ∧
  s1.open_fds = s2.open_fds ∧ s1.reserved = s2.reserved ∧ s1.alloc = s2.alloc
Proof
  rw[sbf_def] >>
  fs[lifetimeWorldTheory.sockets2_component_equality]
QED

Theorem sbf_eq:
  sbf s1 s2 ⇔ ∃f. s2 = s1 with future := f
Proof
  rw[sbf_def, EQ_IMP_THM, lifetimeWorldTheory.sockets2_component_equality] >> simp[]
QED

(* A call other than a poll does not look at the future, nor change it *)
Theorem v2_call_future:
  n ≠ «sock_poll» ⇒
  v2_call n conf bs (s with future := f) =
  OPTION_MAP (λ(out, s'). (out, s' with future := f)) (v2_call n conf bs s)
Proof
  rw[v2_call_def, socket2_fn_def] >>
  simp[ffi_sock_accept2_def, ffi_sock_read2_def, ffi_sock_write2_def,
       ffi_sock_close2_def, sock_accept2_def, sock_read2_def, sock_write2_def,
       sock_close2_def, client_of_def, update_client_def, used_fds_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> every_case_tac >> gvs[] >>
  simp[lifetimeWorldTheory.sockets2_component_equality]
QED

Theorem v2_call_future_same:
  n ≠ «sock_poll» ∧ v2_call n conf bs s = SOME (out, s') ⇒ s'.future = s.future
Proof
  rw[v2_call_def, socket2_fn_def, AllCaseEqs()] >>
  gvs[ffi_sock_accept2_def, ffi_sock_read2_def, ffi_sock_write2_def,
      ffi_sock_close2_def, sock_accept2_def, sock_read2_def, sock_write2_def,
      sock_close2_def, update_client_def, AllCaseEqs()]
QED

Theorem tick2_sbf:
  sbf s1 s2 ∧ fut_step s1.future 0 = fut_step s2.future 0 ⇒ sbf (tick2 s1) (tick2 s2)
Proof
  rw[sbf_eq] >> simp[tick2_def] >>
  qspec_then ‘s1.future’ strip_assume_tac llist_CASES >>
  qspec_then ‘f’ strip_assume_tac llist_CASES >>
  gvs[FOLDL_deliver2_with_future] >>
  TRY (qexists_tac ‘t’ >> simp[lifetimeWorldTheory.sockets2_component_equality] >> NO_TAC) >>
  TRY (qexists_tac ‘t'’ >> simp[] >> NO_TAC) >> qexists_tac ‘[||]’ >> simp[]
QED

Theorem fut_agree_tick2:
  fut_agree (SUC k) s1.future s2.future ⇒ fut_agree k (tick2 s1).future (tick2 s2).future
Proof
  rw[fut_agree_def] >>
  ‘∀s. fut_step (tick2 s).future i = fut_step s.future (SUC i)’
    by (gen_tac >> qspecl_then [‘1’, ‘s’, ‘i’] mp_tac ticks2_future >>
        REWRITE_TAC[ONE, ticks2_def] >> simp[ADD1]) >>
  simp[]
QED

Theorem is_ready2_sbf:
  sbf s1 s2 ⇒ is_ready2 s1 = is_ready2 s2
Proof
  rw[sbf_eq] >> rw[FUN_EQ_THM, is_ready2_def, client_of_def]
QED

(* MAIN *)
Theorem v2_answers_prefix:
  ∀cs s1 s2 k. sbf s1 s2 ∧ fut_agree k s1.future s2.future ∧ npolls cs ≤ k ⇒
               ffi_answers (lifetime_ffi s1) cs = ffi_answers (lifetime_ffi s2) cs
Proof
  Induct >> simp[ffi_answers_def, FORALL_PROD] >> rpt strip_tac >>
  rename1 ‘(n, conf, bs) :: cs’ >>
  simp[lifetime_ffi_def] >> Cases_on ‘n’ >>
  simp[socket2_oracle_v2_call, socket2_oracle_def] >>
  rename1 ‘ExtCall m’ >>
  Cases_on ‘m = «sock_poll»’
  >- (gvs[npolls_def] >> Cases_on ‘k’ >> fs[] >>
      simp[v2_call_def, socket2_fn_def, ffi_sock_poll2_def] >>
      IF_CASES_TAC >> simp[] >>
      ‘fut_step s1.future 0 = fut_step s2.future 0’ by fs[fut_agree_def] >>
      ‘sbf (tick2 s1) (tick2 s2)’ by metis_tac[tick2_sbf] >>
      imp_res_tac is_ready2_sbf >> simp[] >>
      REWRITE_TAC[GSYM lifetime_ffi_def] >>
      first_x_assum irule >> simp[npolls_def] >>
      qexists_tac ‘n’ >> simp[fut_agree_tick2]) >>
  ‘∃f. s2 = s1 with future := f’ by metis_tac[sbf_eq] >> gvs[] >>
  simp[v2_call_future] >>
  Cases_on ‘v2_call m conf bs s1’ >> simp[] >>
  rename1 ‘SOME p’ >> PairCases_on ‘p’ >> simp[] >>
  REWRITE_TAC[GSYM lifetime_ffi_def] >>
  first_x_assum irule >>
  imp_res_tac v2_call_future_same >>
  fs[npolls_def] >> conj_tac >- metis_tac[sbf_eq] >>
  qexists_tac ‘k’ >> simp[]
QED

Theorem npolls_prefix:
  cs ≼ l ⇒ npolls cs ≤ npolls l
Proof
  rw[IS_PREFIX_APPEND] >> simp[npolls_def, FILTER_APPEND]
QED

Theorem init_state_ffi[simp]:
  (init_state f).ffi = f
Proof
  simp[ml_progTheory.init_state_def]
QED

(* MAIN: a diverging run that polls at most k times in one version-2 world
   is also a run in any world whose schedule agrees on the first k steps *)
Theorem diverge_same_prefix:
  semantics_prog (init_state (lifetime_ffi s1)) init_env prog (Diverge io) ∧
  sbf s1 s2 ∧ fut_agree k s1.future s2.future ∧
  (∀evs. LPREFIX (fromList evs) io ⇒ npolls (calls_of evs) ≤ k) ⇒
  semantics_prog (init_state (lifetime_ffi s2)) init_env prog (Diverge io)
Proof
  strip_tac >>
  ‘init_state (lifetime_ffi s2) = init_state (lifetime_ffi s1) with ffi := lifetime_ffi s2’
    by simp[ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality] >>
  pop_assum SUBST1_TAC >> irule semantics_prog_upto >>
  REWRITE_TAC[init_state_ffi] >> rpt conj_tac >> TRY (simp[lifetime_ffi_def] >> NO_TAC) >>
  rw[agree_upto_def] >>
  irule v2_answers_prefix >> simp[] >> qexists_tac ‘k’ >> simp[] >>
  qpat_x_assum ‘semantics_prog _ _ _ (Diverge _)’ mp_tac >>
  simp[semanticsTheory.semantics_prog_def] >> strip_tac >>
  first_x_assum (qspec_then ‘k'’ strip_assume_tac) >>
  fs[ext_def, final_call_def, final_err_def] >>
  ‘LPREFIX (fromList ffi.io_events) io’
    by (fs[lprefix_lub_def] >> first_x_assum irule >> simp[] >>
        qexists_tac ‘k'’ >> simp[]) >>
  metis_tac[npolls_prefix, LESS_EQ_TRANS]
QED
