(*
  The L0 world facts about l1_main's listen, for any port conf (two
  bytes): it always returns, its fd is small and in use, and it keeps
  the fds already in use.  Generalises honestEchoL0Sem/Safe's lemmas
  about echo's port.
*)
Theory honestL1MainWorld
Ancestors
  honestL0 honestL0World honestL0WorldProps honestL0Rely
  honestL1Model honestL1PFRefine honestL1PFRound honestL1MainProg
Libs
  preamble

(* sys_listen always returns *)
Theorem sys_listen_at_SOME:
  LENGTH conf = 2 ⇒ ∃out w1 ev. sys_listen_at conf w = SOME (out, w1, ev)
Proof
  simp[sys_listen_at_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def] >>
  strip_tac >> every_case_tac >> gvs[]
QED

Theorem FOLDL_deliver_fd_limit[local]:
  ∀as w. (FOLDL l0_deliver w as).fd_limit = w.fd_limit
Proof
  Induct >> simp[used_deliver]
QED

(* The listener fd is small: below the fd limit, at most 2^31 *)
Theorem l1_listen_fd_small:
  l0_rely w ∧ sys_listen_at conf w = SOME (out, w1, ev) ∧ l1_listen_fd out = SOME k ⇒
  k < 2147483648
Proof
  rw[sys_listen_at_def, l0_do_def, l0_ffi_fn_def] >>
  gvs[AllCaseEqs(), l0_call_def]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[l1_listen_fd_def, l0_res_of_def] >>
      gvs[l0_listen_def, AllCaseEqs(), l0_alloc_def, l0_tick_def, FOLDL_deliver_fd_limit] >>
      gvs[l0_rely_def]) >>
  PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  gvs[enc_listen_fail_def, l1_listen_fd_def, l0_res_of_def, dec_res_def, AllCaseEqs()]
QED

(* The listener the program listens on is in use *)
Theorem listen_used_at:
  l0_rely w ∧ sys_listen_at conf w = SOME (out, w1, ev) ∧ l1_listen_fd out = SOME k ⇒
  MEM (n2w k : word64) (l0_used w1)
Proof
  rw[sys_listen_at_def, l0_do_def, l0_ffi_fn_def] >>
  gvs[AllCaseEqs(), l0_call_def]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[l1_listen_fd_def, l0_res_of_def] >>
      gvs[l0_listen_def, AllCaseEqs(), l0_used_def]) >>
  PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  gvs[enc_listen_fail_def, l1_listen_fd_def, l0_res_of_def, dec_res_def, AllCaseEqs()]
QED

(* The listen is on conf *)
Theorem listen_conf_at:
  sys_listen_at conf w = SOME (out, w1, ev) ⇒
  ∃bs. ev = IO_event (ExtCall «sys_listen») conf bs
Proof
  rw[sys_listen_at_def] >> drule l0_do_cases >> rw[]
QED

(* Listening keeps the fds in use *)
Theorem listen_used_mono_at:
  sys_listen_at conf w = SOME (out, w1, ev) ⇒ ∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)
Proof
  rw[sys_listen_at_def, l0_do_def, l0_ffi_fn_def] >>
  gvs[AllCaseEqs(), l0_call_def, l0_listen_def] >>
  ‘MEM g (l0_used (l0_tick «sys_listen» w))’ by simp[] >>
  pop_assum mp_tac >> PURE_REWRITE_TAC [l0_used_def] >> simp[] >> rw[] >> simp[]
QED

(* Listening keeps the environment's promises *)
Theorem listen_rely_at:
  l0_rely w ∧ sys_listen_at conf w = SOME (out, w1, ev) ⇒ l0_rely w1
Proof
  rw[sys_listen_at_def] >> metis_tac[honestL1PFRefineTheory.l0_do_rely]
QED
