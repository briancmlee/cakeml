(*
  Moonshot step 9, item 5, part 1: the proxy's handle-layer guarantee
  (proxy_hl_claim_holds), carried by E1 (l1_of_hl) to the honest L1's own
  run: proxy_l1_claim, as client_l1_claim_holds for the client.
*)
Theory proxyL1Claim
Ancestors
  moonshotProxyLive proxyHLStmts honestL1EPTransfer honestL1EPRefine moonshotClientSpec
  endpointSpecForms moonshotProxySafe moonshotProxyRel e1TraceUpto
Libs
  preamble

Theorem proxy_l1_claim_holds:
  proxy_l1_claim pprog pifds
Proof
  simp[proxy_l1_claim_def] >> rpt gen_tac >> strip_tac >>
  qspecl_then [‘proxy_world lfd a’,
               ‘λlv W. proxy_guar_hl b hw lfd lv (pifds lfd b hw) (pprog lfd b hw) W’,
               ‘lfd’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘a’, ‘pol_never’, ‘w0’, ‘calls’] mp_tac
    (Q.GENL [‘P’, ‘G’, ‘lfd’, ‘ifds’, ‘m’, ‘a’, ‘pol’, ‘w0’, ‘calls’] l1_of_hl) >>
  simp[] >> impl_tac >- (
    conj_tac
    >- (rpt strip_tac >> mp_tac proxy_hl_claim_holds >> simp[proxy_hl_claim_def] >>
        disch_then irule >> simp[run_rely_def] >> metis_tac[]) >>
    qspecl_then [‘lfd’, ‘a’, ‘pol_never’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘w0’, ‘calls’] mp_tac
      (Q.GENL [‘lfd’, ‘a’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘calls’] honestL1EPRefineTheory.pew_props) >>
    simp[proxy_world_def, ep_server_world_def, pew_def]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Gap 2 for the proxy (step 9 item 5 (e)): R1's client-count premise holds
   outright, from the proxy's own accept cap (2 · pairs ≤ cbound = 2^63):
   the handle layer's counter is the number of handles issued, at most two
   per pair, in every proxy world, hence in the world built from the run.
   ------------------------------------------------------------------------ *)

Theorem pew_proxy_world:
  proxy_world lfd a (pew lfd a pol ifds m w0 calls)
Proof
  qspecl_then [‘lfd’, ‘a’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘calls’] mp_tac
    (Q.GENL [‘lfd’, ‘a’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘calls’] honestL1EPRefineTheory.pew_props) >>
  simp[proxy_world_def, ep_server_world_def, pew_def]
QED

Theorem proxy_ehst_nxt:
  proxy_world lfd a W0 ⇒
  (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)).nxt ≤ cbound
Proof
  strip_tac >> drule PS_prel_n >>
  disch_then (strip_assume_tac o REWRITE_RULE [prel_def] o SPEC_ALL) >>
  qpat_x_assum ‘LENGTH (FLAT _) = _’ (SUBST1_TAC o SYM) >>
  irule LESS_EQ_TRANS >> irule_at Any LENGTH_phds_le >> first_assum ACCEPT_TAC
QED

Theorem proxy_ecm_bound:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. erounds lfd pol_never (pifds lfd b hw) (pprog lfd b hw) (w0, einit) n ≠ NONE) ⇒
  ∀n. SND (ecm lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0 n) + 1 < dimword (:64)
Proof
  strip_tac >> irule ecm_bound >> simp[] >>
  qexistsl_tac [‘a’, ‘ARB’] >> gen_tac >>
  qspecl_then [‘lfd’, ‘a’, ‘pol_never’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘w0’, ‘ARB’] assume_tac
    (Q.GENL [‘lfd’, ‘a’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘calls’] pew_proxy_world) >>
  drule proxy_ehst_nxt >>
  disch_then (qspecl_then [‘n’, ‘elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0’, ‘hw’, ‘b’]
                mp_tac) >>
  simp[cbound_def, dimword_def]
QED

(* proxy_l1_claim without the client-count premise *)
Theorem proxy_l1_guar:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. erounds lfd pol_never (pifds lfd b hw) (pprog lfd b hw) (w0, einit) n ≠ NONE) ⇒
  proxy_guar_hl b hw lfd (elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0)
    (pifds lfd b hw) (pprog lfd b hw) (pew lfd a pol_never (pifds lfd b hw) (pprog lfd b hw) w0 calls)
Proof
  strip_tac >> mp_tac proxy_l1_claim_holds >> REWRITE_TAC [proxy_l1_claim_def] >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule proxy_ecm_bound >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
