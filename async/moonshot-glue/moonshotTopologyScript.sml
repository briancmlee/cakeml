(*
  Moonshot step 12: topology_stmt (moonshotStep12Stmts).  The three
  programs' port clauses give moonshotPairGlue.topology over the run's
  episodes (sys_rl):
   - a Connected episode was opened by a connect to its port
     (role_connect), so connects_only / no_connects fix it;
   - an Accepted episode's port is its listener's (role_listen, from
     accepts_known, W4), and a listener's port is a successful listen's
     conf, so listens_only fixes it;
   - a process outside the system makes no calls (proc_events_out).
*)
Theory moonshotTopology
Ancestors
  moonshotStep12Stmts moonshotWorldFacts moonshotSysGlue moonshotProxyGlue
  moonshotPairGlue proxyL0StmtsCopy l0sys l0sysEpisodes l0sysInv l0sysStep l0sysRun
  Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* A process outside the system makes no calls *)

Theorem proc_events_out:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ LENGTH ps ≤ k ⇒ proc_events k rs = []
Proof
  strip_tac >> drule sys_steps_EL >> strip_tac >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  ‘∀d. 0 + d ≤ LENGTH rs ⇒
       hist_inv (EL 0 ss) (ghost ss rs (K []) 0) (EL (0 + d) ss) (ghost ss rs (K []) (0 + d))’
    by (match_mp_tac hist_run >> simp[]) >>
  ‘EL 0 ss = s0’ by (Cases_on ‘ss’ >> fs[]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ LENGTH (EL t ss).procs = LENGTH ps’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[hist_inv_def] >>
        fs[sys_init_def]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ proc_events k (TAKE t rs) = []’ suffices_by
    (disch_then (qspec_then ‘LENGTH rs’ mp_tac) >> simp[]) >>
  Induct >- simp[proc_events_def] >>
  strip_tac >> ‘t < LENGTH rs’ by simp[] >> fs[] >>
  simp[ADD1, TAKE_SUC_SNOC, proc_events_SNOC] >>
  Cases_on ‘EL t rs’ >> simp[] >> rw[] >>
  ‘LENGTH (EL t ss).procs = LENGTH ps’ by fs[] >>
  qpat_x_assum ‘∀t. t < _ ⇒ sys_step _ _ _’ (qspec_then ‘t’ mp_tac) >>
  fs[sys_step_def]
QED

(*---------------------------------------------------------------------------*)
(* Roles and the events that made them *)

Theorem role_connect:
  l0_ep_role j evs = SOME (Connected p) ⇒ ∃ev f. MEM ev evs ∧ ev_new ev = SOME (f, INL p)
Proof
  strip_tac >> drule role_lt >> strip_tac >> drule ep_pos_thm >> strip_tac >>
  drule (cj 1 role_of_ep) >> disch_then (qspec_then ‘p’ mp_tac) >> gvs[] >> strip_tac >>
  qexistsl_tac [‘EL (ep_pos evs j) evs’, ‘f’] >> fs[ep_at_def, EL_MEM]
QED

Theorem role_listen:
  l0_ep_role j evs = SOME (Accepted p) ∧ accepts_known evs ⇒
  ∃conf bs k. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ∧
              l0_ev_res bs = SOME (Ok k) ∧ p = w22n conf
Proof
  strip_tac >> drule role_lt >> strip_tac >> drule ep_pos_thm >> strip_tac >>
  qabbrev_tac ‘q = ep_pos evs j’ >>
  drule role_at >> qpat_x_assum ‘ep_idx _ _ = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘l0_ep_role _ _ = _’ (fn th => REWRITE_TAC [th]) >>
  ‘ev_new (EL q evs) ≠ NONE ∧ q < LENGTH evs’ by fs[ep_at_def] >>
  Cases_on ‘ev_new (EL q evs)’ >> fs[] >> rename1 ‘ev_new _ = SOME x’ >>
  PairCases_on ‘x’ >> Cases_on ‘x1’ >> fs[moonshotProxyGlueTheory.ev_role_def] >> rename1 ‘INR l’ >>
  ‘ALOOKUP (FOLDL lsn_step [] (TAKE q evs)) l ≠ NONE’
    by (qpat_x_assum ‘accepts_known _’ mp_tac >> rewrite_tac[accepts_known_def] >>
        disch_then irule >> simp[] >> metis_tac[]) >>
  Cases_on ‘ALOOKUP (FOLDL lsn_step [] (TAKE q evs)) l’ >> fs[] >> strip_tac >> rveq >>
  drule lsn_port >> simp[] >> strip_tac >> drule ev_listen_listen >> strip_tac >> rveq >>
  qexistsl_tac [‘conf’, ‘bs’, ‘k’] >> simp[] >> metis_tac[MEM_TAKE]
QED

Theorem new_INL_connect:
  ev_new ev = SOME (f, INL p) ⇒ ∃conf bs. ev = IO_event (ExtCall «sys_connect») conf bs
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[ev_new_def, LET_THM] >> every_case_tac >> gvs[]
QED

Theorem w22n_pbytes:
  p < 65536 ⇒ w22n (pbytes p) = p
Proof
  strip_tac >> ‘pbytes p = n2w2 p’ by simp[pbytes_def, n2w2_def] >>
  simp[w22n_n2w2]
QED

(*---------------------------------------------------------------------------*)
(* The ports *)

Theorem accepted_port:
  l0_ep_role j evs = SOME (Accepted p) ∧ accepts_known evs ∧ listens_only q evs ∧ q < 65536 ⇒
  p = q
Proof
  strip_tac >> drule_all role_listen >> strip_tac >>
  qpat_x_assum ‘listens_only _ _’ mp_tac >> rewrite_tac[listens_only_def] >>
  disch_then drule_all >> strip_tac >> rveq >> simp[w22n_pbytes]
QED

Theorem connected_port:
  l0_ep_role j evs = SOME (Connected p) ∧ connects_only q evs ⇒ p = q
Proof
  strip_tac >> drule role_connect >> strip_tac >>
  qpat_x_assum ‘connects_only _ _’ mp_tac >> rewrite_tac[connects_only_def] >>
  disch_then drule_all >> simp[]
QED

Theorem no_connects_connected:
  no_connects evs ⇒ l0_ep_role j evs ≠ SOME (Connected p)
Proof
  rpt strip_tac >> drule role_connect >> strip_tac >> drule new_INL_connect >> strip_tac >>
  rveq >> fs[no_connects_def] >> metis_tac[]
QED

Theorem topology_stmt_holds:
  topology_stmt
Proof
  rewrite_tac[topology_stmt_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘l0sys_run _ _’ mp_tac >> rewrite_tac[l0sys_run_def] >> strip_tac >>
  ‘LENGTH (moonshot_sys cprog pprog kprog a b c N rqs) = 3’ by simp[moonshot_sys_def] >>
  ‘∀k. 3 ≤ k ⇒ proc_events k rs = []’
    by (rpt strip_tac >> irule proc_events_out >> metis_tac[]) >>
  ‘∀k. k < 3 ⇒ accepts_known (proc_events k rs)’
    by (rpt strip_tac >> irule l0sys_accepts_known >> metis_tac[]) >>
  fs[client_ix_def, proxy_ix_def, kv_ix_def] >>
  ‘∀k j r. l0_ep_role j (proc_events k rs) = SOME r ⇒ k < 3’
    by (rpt strip_tac >> CCONTR_TAC >>
        ‘proc_events k rs = []’ by simp[] >> fs[l0_ep_role_def, ep_roles_def]) >>
  simp[topology_def, sys_rl_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (‘k < 3’ by metis_tac[] >>
      ‘k = 0 ∨ k = 1 ∨ k = 2’ by simp[] >> rveq
      >- (‘p = c’ by metis_tac[accepted_port] >> simp[])
      >- (‘p = a’ by metis_tac[accepted_port] >> simp[])
      >- (‘p = b’ by metis_tac[accepted_port] >> simp[])) >>
  ‘k < 3’ by metis_tac[] >>
  ‘k = 0 ∨ k = 1 ∨ k = 2’ by simp[] >> rveq
  >- (‘p = a’ by metis_tac[connected_port] >> simp[])
  >- (‘p = b’ by metis_tac[connected_port] >> simp[]) >>
  metis_tac[no_connects_connected]
QED
