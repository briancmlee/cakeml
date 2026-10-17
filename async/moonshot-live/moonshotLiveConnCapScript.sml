(*
  G3, system side: the counted connect episodes (conns_ok, accepts_lt's
  count) are at most the Connected episodes of the process's trace, the
  count honest-ffi's proxy_conn_cap_run bounds by 2^62 on every finite
  prefix of proxy_run_io (proxyLiveLift.proxy_conn_cap_run_thm,
  spike/proxy-asks-l0 @ 66a541c81).
*)
Theory moonshotLiveConnCap
Ancestors
  moonshotLiveAccepts moonshotLiveCompose moonshotLiveProjInf moonshotLiveStmts moonshotLiveExcuse
  moonshotLiveWorldDrains l0sysFair l0sysStep l0sysInv l0sysInvCall l0sysEpisodes l0sys
  honestL0World honestL0 honestL0Rely moonshotLiveObs Marshalling
Libs
  preamble

Theorem filter_zip_le:
  ∀l1 l2. LENGTH l1 = LENGTH l2 ∧ (∀x y. P (x, y) ⇒ Q x) ⇒
          LENGTH (FILTER P (ZIP (l1, l2))) ≤ LENGTH (FILTER Q l1)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘l2’ >> simp[] >> strip_tac >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> impl_tac >- metis_tac[] >>
  rw[] >> metis_tac[]
QED

(* MAIN *)
Theorem conns_ok_le_connected:
  l0sys_irun ps ss rs ∧ cl < LENGTH ps ⇒
  conns_ok p ss rs cl n ≤
  LENGTH (FILTER (λr. ∃p. r = Connected p) (ep_roles [] (ptr rs cl n)))
Proof
  strip_tac >>
  ‘sinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_sinv_css] >>
  ‘cl < LENGTH (ss n).procs’ by metis_tac[irun_procs_length] >>
  ‘pk (GENLIST rs n) (ss n) (run_css ss rs n) cl’ by fs[sinv_def] >>
  ‘pinv (ptr rs cl n) (EL cl (ss n).procs) (run_css ss rs n cl)’ by fs[pk_def, ptr_def] >>
  ‘LENGTH (ep_roles [] (ptr rs cl n)) = LENGTH (run_css ss rs n cl)’
    by fs[pinv_def, LENGTH_ep_roles] >>
  rewrite_tac[conns_ok_def] >> irule filter_zip_le >> simp[FORALL_PROD] >> metis_tac[]
QED

(* The plug-in: a cap on the Connected episodes of every finite prefix of a
   trace tr that every ptr rs cl n is a prefix of (l0sys_proj_inf) caps
   conns_ok at every instant (proxy_conn_cap_run_thm's conclusion, with
   tr = proxy_run_io b hw k w4 pre and cap = 2 ** 62) *)
Theorem conns_ok_cap:
  l0sys_irun ps ss rs ∧ cl < LENGTH ps ∧
  (∀evs. LPREFIX (fromList evs) tr ⇒
         LENGTH (FILTER (λr. ∃p. r = Connected p) (ep_roles [] evs)) ≤ cap) ∧
  (∀n. LPREFIX (fromList (ptr rs cl n)) tr) ⇒
  ∀n. conns_ok p ss rs cl n ≤ cap
Proof
  rpt strip_tac >> irule LESS_EQ_TRANS >>
  qexists_tac ‘LENGTH (FILTER (λr. ∃p. r = Connected p) (ep_roles [] (ptr rs cl n)))’ >>
  conj_tac >- (irule conns_ok_le_connected >> metis_tac[]) >>
  first_x_assum irule >> first_x_assum (qspec_then ‘n’ ACCEPT_TAC)
QED

(* ------------------------------------------------------------------------
   Under (A): G3' counts only the connect episodes that did not fail at once
   (honest-ffi's proxy_conn_kept_cap_run, spike/proxy-r3, SHA to come).
   TEMPORARY COPY of its conn_kept_def (text agreed 2026-10-17); remove
   when the lines merge.
   ------------------------------------------------------------------------ *)

Definition conn_kept_def:
  conn_kept (IO_event (ExtCall n) conf bl) =
    ((∃f p. ev_new (IO_event (ExtCall n) conf bl) = SOME (f, INL p)) ∧
     ((∃v. dec_res (MAP SND bl) = SOME (Ok v)) ∨
      (∃x. dec_res (MAP SND bl) = SOME (Fail E_INPROGRESS x)))) ∧
  conn_kept _ = F
End

(* A connect that opened a socket appended a channel *)
Theorem connect_new_len:
  l0_rely w ∧ l0_call «sys_connect» conf bts w = SOME (FFIreturn out w1) ∧
  ev_new (IO_event (ExtCall «sys_connect») conf (ZIP (bts, out))) = SOME (f, INL q) ∧
  LENGTH out = LENGTH bts ⇒
  LENGTH w1.chans = LENGTH w.chans + 1
Proof
  strip_tac >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[upd_lchan_def, fail_def] >>
  drule_then (qspecl_then [‘0’, ‘e’] mp_tac) enc_err_val_dec >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘ev_new _ = _’ mp_tac >> asm_simp_tac (srw_ss()) [ev_new_def, MAP_ZIP, LET_THM]
QED

(* A connect whose new channel is not broken returned Ok or E_INPROGRESS *)
Theorem connect_kept_out:
  l0_rely w ∧ l0_call «sys_connect» conf bts w = SOME (FFIreturn out w1) ∧
  LENGTH w1.chans = LENGTH w.chans + 1 ∧ ¬(EL (LENGTH w.chans) w1.chans).broken ⇒
  (∃v. dec_res out = SOME (Ok v)) ∨ (∃x. dec_res out = SOME (Fail E_INPROGRESS x))
Proof
  strip_tac >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> qpat_x_assum ‘l0_connect _ _ = _’ mp_tac >>
  simp[l0_connect_def, AllCaseEqs(), LET_THM, fail_def] >> strip_tac >>
  gvs[upd_lchan_def, EL_LUPDATE, EL_APPEND2, fresh_lchan_def] >>
  ‘w2n f < 256 ** 8’ by (mp_tac (Q.ISPEC ‘f : word64’ w2n_lt) >> simp[])
  >- (disj1_tac >> qexists_tac ‘w2n f’ >>
      qpat_x_assum ‘w2n f < _’ mp_tac >>
      mp_tac (Q.INST [‘r’ |-> ‘Ok (w2n (f : word64))’, ‘rest’ |-> ‘[]’] dec_enc_res) >> simp[l0_res_ok_def]) >>
  disj2_tac >>
  drule_then (qspecl_then [‘w2n f’, ‘E_INPROGRESS’] mp_tac) enc_err_val_dec >>
  impl_tac >- first_assum ACCEPT_TAC >> metis_tac[]
QED

(* If the new channel is broken after the call, it is broken in the next
   state (born_broken's form) *)
Theorem step_born_broken:
  sys_step s (Call k «sys_connect» conf bts out) s' ∧
  l0_call «sys_connect» conf bts (EL k s.procs) = SOME (FFIreturn out w1) ∧
  LENGTH w1.chans = LENGTH (EL k s.procs).chans + 1 ∧
  (EL (LENGTH (EL k s.procs).chans) w1.chans).broken ⇒
  LENGTH (EL k s.procs).chans < LENGTH (EL k s'.procs).chans ∧
  (EL (LENGTH (EL k s.procs).chans) (EL k s'.procs).chans).broken
Proof
  simp[sys_step_def, LET_THM, unblock_def] >> strip_tac >> gvs[EL_LUPDATE]
QED

Theorem ev_role_new_chans_len:
  LENGTH (ev_role lst ev) = LENGTH (new_chans w ev)
Proof
  simp[ev_role_def, new_chans_def] >> every_case_tac >> simp[]
QED

(* The step: what a step adds to conns_ok is a conn_kept event *)
Theorem conns_ok_kept_step:
  l0sys_irun ps ss rs ∧ cl < LENGTH ps ⇒
  conns_ok p ss rs cl (SUC n) ≤
  conns_ok p ss rs cl n +
  LENGTH (FILTER conn_kept (case rs n of
                            | Call k' nm conf bts out =>
                                if k' = cl then [IO_event (ExtCall nm) conf (ZIP (bts, out))] else []
                            | _ => []))
Proof
  strip_tac >>
  qabbrev_tac ‘P = λm (r, c). r = Connected p ∧ ∀t. t < m ⇒ ¬born_broken ss rs t cl c’ >>
  ‘∀m. conns_ok p ss rs cl m =
       LENGTH (FILTER (P m) (ZIP (ep_roles [] (ptr rs cl m), run_css ss rs m cl)))’
    by simp[conns_ok_def, Abbr ‘P’] >>
  ‘∀x. P (SUC n) x ⇒ P n x’ by (simp[Abbr ‘P’, FORALL_PROD] >> rw[]) >>
  ‘∀m. LENGTH (ep_roles [] (ptr rs cl m)) = LENGTH (run_css ss rs m cl)’
    by (gen_tac >>
        ‘sinv (GENLIST rs m) (ss m) (run_css ss rs m)’ by metis_tac[irun_sinv_css] >>
        ‘cl < LENGTH (ss m).procs’ by metis_tac[irun_procs_length] >>
        ‘pk (GENLIST rs m) (ss m) (run_css ss rs m) cl’ by fs[sinv_def] >>
        ‘pinv (ptr rs cl m) (EL cl (ss m).procs) (run_css ss rs m cl)’ by fs[pk_def, ptr_def] >>
        fs[pinv_def, LENGTH_ep_roles]) >>
  ntac 2 (pop_assum mp_tac) >> pop_assum (fn th => rewrite_tac[th]) >> rpt strip_tac >>
  Cases_on ‘∃nm conf bts out. rs n = Call cl nm conf bts out’
  >- (fs[] >>
      qabbrev_tac ‘ev = IO_event (ExtCall nm) conf (ZIP (bts, out))’ >>
      qabbrev_tac ‘w = EL cl (ss n).procs’ >>
      ‘ptr rs cl (SUC n) = ptr rs cl n ++ [ev]’ by simp[ptr_SUC, Abbr ‘ev’] >>
      ‘run_css ss rs (SUC n) cl = run_css ss rs n cl ++ new_chans w ev’
        by simp[run_css_def, step_css_def, call_css_def, APPLY_UPDATE_THM, Abbr ‘w’, Abbr ‘ev’] >>
      simp[ep_roles_SNOC] >>
      qmatch_goalsub_abbrev_tac ‘ev_role lst ev’ >>
      ‘LENGTH (ev_role lst ev) = LENGTH (new_chans w ev)’ by simp[ev_role_new_chans_len] >>
      ‘LENGTH (ep_roles [] (ptr rs cl n)) = LENGTH (run_css ss rs n cl)’ by simp[] >>
      ‘ZIP (ep_roles [] (ptr rs cl n) ++ ev_role lst ev, run_css ss rs n cl ++ new_chans w ev) =
       ZIP (ep_roles [] (ptr rs cl n), run_css ss rs n cl) ++ ZIP (ev_role lst ev, new_chans w ev)’
        by (irule (GSYM ZIP_APPEND) >> simp[]) >>
      pop_assum SUBST1_TAC >> rewrite_tac[FILTER_APPEND, LENGTH_APPEND] >>
      ‘LENGTH (FILTER (P (SUC n)) (ZIP (ep_roles [] (ptr rs cl n), run_css ss rs n cl))) ≤
       LENGTH (FILTER (P n) (ZIP (ep_roles [] (ptr rs cl n), run_css ss rs n cl)))’
        by (irule LENGTH_FILTER_LEQ_MONO >> first_assum ACCEPT_TAC) >>
      ‘LENGTH (FILTER (P (SUC n)) (ZIP (ev_role lst ev, new_chans w ev))) ≤
       LENGTH (FILTER conn_kept [ev])’
        suffices_by (qpat_x_assum ‘LENGTH (FILTER (P (SUC n)) _) ≤ _’ mp_tac >>
                     Cases_on ‘conn_kept ev’ >> simp[]) >>
      Cases_on ‘ev_new ev’ >- simp[ev_role_def, new_chans_def] >>
      rename1 ‘ev_new ev = SOME x’ >> PairCases_on ‘x’ >> Cases_on ‘x1’
      >~ [‘INR l’] >- simp[ev_role_def, new_chans_def, Abbr ‘P’] >>
      rename1 ‘ev_new ev = SOME (f, INL q)’ >>
      simp[ev_role_def, new_chans_def] >> simp[Abbr ‘P’] >>
      IF_CASES_TAC >> simp[] >>
      ‘conn_kept ev’ suffices_by simp[] >> pop_assum strip_assume_tac >> rveq >>
      ‘nm = «sys_connect»’ by (drule ev_new_INL_ev >> simp[Abbr ‘ev’]) >> rveq >>
      ‘l0_rely w ∧ ∃w1. l0_call «sys_connect» conf bts w = SOME (FFIreturn out w1)’
        by (drule_all irun_call >> simp[unblock_def, Abbr ‘w’]) >>
      ‘LENGTH out = LENGTH bts’ by (drule_all irun_call_len >> simp[]) >>
      ‘LENGTH w1.chans = LENGTH w.chans + 1’
        by (irule connect_new_len >> simp[] >> qexistsl_tac [‘bts’, ‘conf’, ‘f’, ‘out’, ‘p’] >>
            fs[Abbr ‘ev’]) >>
      ‘¬(EL (LENGTH w.chans) w1.chans).broken’
        by (strip_tac >>
            ‘sys_step (ss n) (rs n) (ss (SUC n))’ by fs[l0sys_irun_def] >>
            ‘cl < LENGTH (ss n).procs’ by metis_tac[irun_procs_length] >>
            qpat_x_assum ‘∀t. t < SUC n ⇒ _’ (qspec_then ‘n’ mp_tac) >> simp[born_broken_def] >>
            qpat_x_assum ‘rs n = _’ (fn th => fs[th]) >>
            drule step_born_broken >> simp[Abbr ‘w’]) >>
      ‘(∃v. dec_res out = SOME (Ok v)) ∨ (∃x. dec_res out = SOME (Fail E_INPROGRESS x))’
        by (irule connect_kept_out >> simp[] >> metis_tac[]) >>
      simp[Abbr ‘ev’, conn_kept_def, MAP_ZIP] >> fs[Abbr ‘ev’] >> metis_tac[]) >>
  ‘ptr rs cl (SUC n) = ptr rs cl n’ by (simp[ptr_SUC] >> Cases_on ‘rs n’ >> fs[] >> rw[]) >>
  ‘run_css ss rs (SUC n) cl = run_css ss rs n cl’
    by (simp[run_css_def] >> Cases_on ‘rs n’ >> fs[step_css_def, call_css_def, APPLY_UPDATE_THM] >>
        rw[] >> fs[]) >>
  ‘(case rs n of Call k' nm conf bts out =>
      if k' = cl then [IO_event (ExtCall nm) conf (ZIP (bts, out))] else [] | _ => []) = []’
    by (Cases_on ‘rs n’ >> fs[] >> rw[]) >>
  simp[] >> irule LENGTH_FILTER_LEQ_MONO >> first_assum ACCEPT_TAC
QED

(* MAIN: conns_ok counts no more than the conn_kept events *)
Theorem conns_ok_le_kept:
  l0sys_irun ps ss rs ∧ cl < LENGTH ps ⇒
  ∀n. conns_ok p ss rs cl n ≤ LENGTH (FILTER conn_kept (ptr rs cl n))
Proof
  strip_tac >> Induct
  >- simp[conns_ok_def, ptr_def, proc_events_def, run_css_def, ep_roles_def] >>
  drule_all conns_ok_kept_step >> disch_then (qspecl_then [‘p’, ‘n’] assume_tac) >>
  simp[ptr_SUC, FILTER_APPEND] >> decide_tac
QED

(* The plug-in for G3' (proxy_conn_kept_cap_run's conclusion, with
   tr = proxy_run_io b hw k w4 pre and cap = 2 ** 62) *)
Theorem conns_ok_kept_cap:
  l0sys_irun ps ss rs ∧ cl < LENGTH ps ∧
  (∀evs. LPREFIX (fromList evs) tr ⇒ LENGTH (FILTER conn_kept evs) ≤ cap) ∧
  (∀n. LPREFIX (fromList (ptr rs cl n)) tr) ⇒
  ∀n. conns_ok p ss rs cl n ≤ cap
Proof
  rpt strip_tac >> irule LESS_EQ_TRANS >>
  qexists_tac ‘LENGTH (FILTER conn_kept (ptr rs cl n))’ >>
  conj_tac >- (irule conns_ok_le_kept >> metis_tac[]) >>
  first_x_assum irule >> first_x_assum (qspec_then ‘n’ ACCEPT_TAC)
QED
