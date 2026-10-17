(*
  Moonshot step 9, item 5, part 1: the proxy's handle-layer guarantee
  (proxy_hl_claim_holds), carried by E1 (l1_of_hl) to the honest L1's own
  run: proxy_l1_claim, as client_l1_claim_holds for the client.
*)
Theory proxyL1Claim
Ancestors
  moonshotProxyLive proxyHLStmts honestL1EPTransfer honestL1EPRefine moonshotClientSpec
  endpointSpecForms
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
