(*
  G3, system side: the counted connect episodes (conns_ok, accepts_lt's
  count) are at most the Connected episodes of the process's trace, the
  count honest-ffi's proxy_conn_cap_run bounds by 2^62 on every finite
  prefix of proxy_run_io (proxyLiveLift.proxy_conn_cap_run_thm,
  spike/proxy-asks-l0 @ 66a541c81).
*)
Theory moonshotLiveConnCap
Ancestors
  moonshotLiveAccepts moonshotLiveCompose moonshotLiveProjInf moonshotLiveStmts l0sysFair
  l0sysStep l0sysInv l0sysEpisodes
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
