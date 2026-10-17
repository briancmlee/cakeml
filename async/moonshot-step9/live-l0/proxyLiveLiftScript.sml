(*
  The proxy's liveness parts of l0_proxy_claim (proxyL0Stmts, rev 10),
  STATED over m4-server's run (proxyL0Run): from the start proxy_start
  and E1's rounds never failing (totality), on the proxy's whole trace
  proxy_run_io and its pairing proxy_pr, under the claim's live-block
  hypotheses (F1_io, F2, accepts_below):
   - proxy_live_run: proxy_live_l0 (relay, conditional on draining);
   - proxy_pairs_run: under accepts_lt (2 ** 62 + 1), proxy_pairs_l0
     (every front gets a backend).  Without it the (2^62 + 1)-th accept
     waits in L1's acq forever (the program's accept cap is 2^62 pairs),
     unpaired and unexcused;
   - conn_live_run: under accepts_lt (2 ** 62 + 1) (plain prefix form, as
     moonshot-live's accepts_lt_lift concludes; at most 2^62 accepts,
     which implies the claim's 2 ** 62 form), conn_live_l0.
  K is L1's write timeout pf_sendwait (D23), as l0_proxy_claim's header
  has it.  Statements only; proofs to come.
*)
Theory proxyLiveLift
Ancestors
  proxyL0Run proxyL0Stmts honestL1BStmts honestL1PFModel e1DriverLoop
  moonshotProxyLive moonshotProxySafe moonshotProxyRel proxyHLStmts
Libs
  preamble

Overload PS[local] = “λlfd b hw lv W0 n. pstate lfd b hw (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)”

(* ------------------------------------------------------------------------
   The handle layer's pairing, without connect fairness: an accepted front
   gets a backend that the history connected, or connects return no socket
   without bound
   ------------------------------------------------------------------------ *)

Theorem proxy_pairs_hl:
  proxy_world lfd a W0 ∧
  MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw)
            (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))) ⇒
  (∃c n'. ppair lfd b hw lv W0 hd = SOME c ∧
          MEM c (hl_conn_handles (hl_pairs (pprog lfd b hw)
                   (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n')))) ∨
  ∀k. ∃n'. k ≤ hl_nosock (hl_pairs (pprog lfd b hw)
                            (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n'))
Proof
  strip_tac >>
  drule PS_prel_n >> disch_then (qspecl_then [‘n’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  ‘∃p. MEM p (PS lfd b hw lv W0 n).pc ∧ p.fh = hd’
    by (drule prel_acc >> disch_then (fn th => fs[GSYM th])) >>
  qpat_x_assum ‘MEM p _’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 ‘i < LENGTH (PS lfd b hw lv W0 n).pc’ >>
  ‘∀m. n ≤ m ⇒ i < LENGTH (PS lfd b hw lv W0 m).pc’
    by (rpt strip_tac >> irule (cj 1 pkeep_EL) >>
        qexists_tac ‘(PS lfd b hw lv W0 n).pc’ >> simp[] >>
        irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  Cases_on ‘∃m c. n ≤ m ∧ (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c’
  >- (disj1_tac >> pop_assum strip_assume_tac >>
      ‘i < LENGTH (PS lfd b hw lv W0 m).pc’ by simp[] >>
      qexistsl_tac [‘c’, ‘m’] >> conj_tac
      >- (drule ppair_SOME >> disch_then (fn th => REWRITE_TAC [th]) >>
          qexistsl_tac [‘m’, ‘i’] >> simp[] >>
          mp_tac (Q.INST [‘n'’ |-> ‘m’] PS_slot_const) >>
          impl_tac >- asm_rewrite_tac [] >> strip_tac >> gvs[]) >>
      drule PS_prel_n >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
      qpat_x_assum ‘prel _ (PS _ _ _ _ _ m) _ _ _ _’
        (fn th => REWRITE_TAC [REWRITE_RULE [prel_def] th]) >>
      qexists_tac ‘EL i (PS lfd b hw lv W0 m).pc’ >> simp[EL_MEM]) >>
  disj2_tac >> irule proxy_connect_forever >>
  conj_tac >- (qexistsl_tac [‘i’, ‘n’] >> asm_rewrite_tac [] >> rpt strip_tac >>
                Cases_on ‘(EL i (PS lfd b hw lv W0 m).pc).bh’ >> fs[] >> metis_tac[]) >>
  qexists_tac ‘a’ >> first_assum ACCEPT_TAC
QED

(* The run and the live block's hypotheses *)
Definition proxy_live_hyps_def:
  proxy_live_hyps a b hw w0 pre w4 k ⇔
    a < 65536 ∧ b < 65536 ∧ proxy_start a w0 pre w4 k ∧
    (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
    F1_io (proxy_run_io b hw k w4 pre) ∧ F2 w0 ∧ accepts_below (proxy_run_io b hw k w4 pre)
End

Definition proxy_live_run_def:
  proxy_live_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ⇒
      proxy_live_l0 pf_sendwait (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) w0
                    (proxy_run_io b hw k w4 pre)
End

Definition proxy_pairs_run_def:
  proxy_pairs_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ∧ accepts_lt (2 ** 62 + 1) (proxy_run_io b hw k w4 pre) ⇒
      proxy_pairs_l0 pf_sendwait (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre))
                     (proxy_run_io b hw k w4 pre)
End

Definition conn_live_run_def:
  conn_live_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ∧ accepts_lt (2 ** 62 + 1) (proxy_run_io b hw k w4 pre) ⇒
      conn_live_l0 w0 (proxy_run_io b hw k w4 pre)
End
