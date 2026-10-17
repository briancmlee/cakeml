(*
  S2 on the PF run for ANY server m that uses the socket API correctly
  (asyncRunOkGen's uses_ok), polled through the live list (D26):
  honest-echo-live's honestEchoL0Obl.echo_S2 with the echo-specific steps
  replaced by their generic forms (hrun_sim_gl for hrun_sim_l, gen_grun_ok
  for echo_grun_ok).  The M4-level queue progress (echo's queue_progress_l,
  KV's kv_queue_progress_l) is a hypothesis, at the version-1 world GV1.

  MAIN: gen_sim, gen_S2.
*)
Theory honestL0GenS2
Ancestors
  honestL0GenSimLive honestEchoL0Obl
  honestL1PFObl honestL1PFConnRun honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel
  asyncHLSimRun asyncHLSimWorld asyncHLModel asyncM4Queue asyncM4AcceptSoon asyncRunOkGen
  asyncM4SockInv asyncM4GTrans asyncM4GRounds asyncM4Relabel asyncM4SockModel
  asyncM4Loop asyncM3World asyncCore asyncLevel1 alist
Libs
  preamble

Overload GLI[local] = “λm. asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel m))”
Overload GPSK[local] = “λm pol w0. psk (n2w lfdn) pol (GLI m) (srelabel m) w0”
Overload GV1[local] = “λm pol w0. v1of (n2w lfdn) (psk (n2w lfdn) pol (GLI m) (srelabel m) w0)”

(* The PF run hypotheses (honestEchoL0Obl's echo_run), for any uses_ok m *)
Definition gen_run_def:
  gen_run lfdn m pol w0 ⇔
    uses_ok lfdn m ∧
    run_ok (n2w lfdn) pol (GLI m) (srelabel m) w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
    (∀n. SND (pcm (n2w lfdn) pol (GLI m) (srelabel m) w0 n) + 1 < dimword (:64)) ∧
    lfdn < dimword (:64)
End

(* MAIN: echo_sim, for any uses_ok m *)
Theorem gen_sim:
  gen_run lfdn m pol w0 ⇒
  ∀n. rhist (n2w lfdn) pol (GLI m) (srelabel m) w0 n = ghist (GLI m) (srelabel m) (GV1 m pol w0) n ∧
      hsim (n2w lfdn) (gstate (GLI m) (srelabel m) (GV1 m pol w0) n) (hst (n2w lfdn) (GLI m) (srelabel m) (GPSK m pol w0) n) ∧
      SND (hst (n2w lfdn) (GLI m) (srelabel m) (GPSK m pol w0) n) = hs_of (rstate (n2w lfdn) pol (GLI m) (srelabel m) w0 n) ∧
      pv_rel (n2w lfdn) (FST (pcm (n2w lfdn) pol (GLI m) (srelabel m) w0 n))
             (rstate (n2w lfdn) pol (GLI m) (srelabel m) w0 n) (FST (hst (n2w lfdn) (GLI m) (srelabel m) (GPSK m pol w0) n)) ∧
      GENLIST (hdl (n2w lfdn)) (rstate (n2w lfdn) pol (GLI m) (srelabel m) w0 n).b.nxt =
        wacc (gperf (GLI m) (srelabel m) (GV1 m pol w0) n)
Proof
  PURE_REWRITE_TAC[gen_run_def] >> strip_tac >> gen_tac >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[run_ok_def, winv_def] >>
  drule_all psk_server_world >> strip_tac >>
  drule_all hrun_sim_gl >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_then (qspec_then ‘n’ assume_tac) prun_some >>
  Cases_on ‘prun (n2w lfdn) pol (GLI m) (srelabel m) w0 n’ >> rename1 ‘_ = (hh, x)’ >> PairCases_on ‘x’ >>
  drule_all l1pf_refines_hl >> strip_tac >>
  gvs[rhist_def, rstate_def, hs_of_def]
QED

(* Every Accept of the PF run is on its listener (its rounds succeed) *)
Theorem gen_round_accept_lfd:
  gen_run lfdn m pol w0 ∧
  MEM (Accept l) (new_actions (log_of (srelabel m)) (rhist (n2w lfdn) pol (GLI m) (srelabel m) w0 k)) ⇒
  l = n2w lfdn
Proof
  PURE_REWRITE_TAC[gen_run_def] >> strip_tac >>
  drule_then (qspec_then ‘k’ strip_assume_tac) prun_round >>
  gvs[pround_def, AllCaseEqs()] >>
  irule pacts_accept_lfd >> metis_tac[]
QED

(* An accept the M4 run performed after round n is an Accept of the PF run
   in some round k ≥ n *)
Theorem gen_wacc_grow_accept:
  gen_run lfdn m pol w0 ∧ ¬MEM c (wacc (gperf (GLI m) (srelabel m) (GV1 m pol w0) n)) ⇒
  ∀N. MEM c (wacc (gperf (GLI m) (srelabel m) (GV1 m pol w0) N)) ⇒
      ∃k. n ≤ k ∧ k < N ∧
          MEM (Accept (n2w lfdn)) (new_actions (log_of (srelabel m)) (rhist (n2w lfdn) pol (GLI m) (srelabel m) w0 k))
Proof
  strip_tac >> Induct >- simp[gperf_def, wacc_def] >>
  simp[gperf_SUC] >> strip_tac
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> simp[]) >>
  ‘n ≤ N’
    by (CCONTR_TAC >> qpat_x_assum ‘¬MEM _ _’ mp_tac >> simp[] >>
        irule wacc_mono >> qexists_tac ‘SUC N’ >> simp[gperf_SUC]) >>
  drule wacc_accept >> strip_tac >>
  ‘grun_ok (GLI m) (srelabel m) (GV1 m pol w0)’
    by (irule gen_grun_ok >> simp[v1of_def] >> qexists_tac ‘lfdn’ >> fs[gen_run_def]) >>
  ‘LENGTH (gres (GLI m) (srelabel m) (GV1 m pol w0) N) = LENGTH (gacts (GLI m) (srelabel m) (GV1 m pol w0) N)’ by simp[LENGTH_gres] >>
  ‘MEM (Accept l) (gacts (GLI m) (srelabel m) (GV1 m pol w0) N)’ by (gvs[MEM_ZIP] >> metis_tac[EL_MEM]) >>
  qexists_tac ‘N’ >> simp[] >>
  drule_then (qspec_then ‘N’ strip_assume_tac) gen_sim >>
  ‘MEM (Accept l) (new_actions (log_of (srelabel m)) (rhist (n2w lfdn) pol (GLI m) (srelabel m) w0 N))’
    by gvs[gacts_def] >>
  drule_all gen_round_accept_lfd >> strip_tac >> gvs[]
QED

(* MAIN: S2, given the M4 run's queue progress at (GV1 m pol w0) *)
Theorem gen_S2:
  gen_run lfdn m pol w0 ∧
  (∀c k n. queued (n2w lfdn) c k (gstate (GLI m) (srelabel m) (GV1 m pol w0) n) ⇒ ∃N. MEM c (wacc (gperf (GLI m) (srelabel m) (GV1 m pol w0) N))) ⇒
  S2 (n2w lfdn) pol (GLI m) (srelabel m) w0
Proof
  strip_tac >> simp[S2_def] >> rpt strip_tac >>
  drule_then (qspec_then ‘n’ strip_assume_tac) gen_sim >>
  ‘lfdn < dimword (:64)’ by fs[gen_run_def] >>
  qabbrev_tac ‘ps = rstate (n2w lfdn) pol (GLI m) (srelabel m) w0 n’ >>
  qabbrev_tac ‘cm = FST (pcm (n2w lfdn) pol (GLI m) (srelabel m) w0 n)’ >>
  Cases_on ‘hst (n2w lfdn) (GLI m) (srelabel m) (GPSK m pol w0) n’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hs = hs_of ps’ by fs[] >>
  ‘pv_rel (n2w lfdn) cm ps s2’ by fs[] >>
  ‘hsim0 (n2w lfdn) (gstate (GLI m) (srelabel m) (GV1 m pol w0) n) (s2, hs)’ by fs[hsim_def] >>
  ‘s2.listening = [(n2w lfdn, MAP (cl cm) ps.acq)]’ by fs[pv_rel_def] >>
  ‘hs.nxt = ps.b.nxt’ by simp[hs_of_def] >>
  qabbrev_tac ‘L = LENGTH s2.clients − ps.b.nxt’ >>
  ‘s2.listening = [(n2w lfdn, GENLIST (λi. ps.b.nxt + i) L)] ∧
   (gstate (GLI m) (srelabel m) (GV1 m pol w0) n).listeners =
     [(n2w lfdn, GENLIST (λi. hdl (n2w lfdn) (ps.b.nxt + i)) L)] ∧
   ps.b.nxt ≤ LENGTH s2.clients ∧ LENGTH s2.clients < dimword (:64)’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, Abbr ‘L’] >>
        rw[] >> fs[]) >>
  ‘L = LENGTH ps.acq’
    by (‘MAP (cl cm) ps.acq = GENLIST (λi. ps.b.nxt + i) L’ by fs[] >>
        pop_assum (mp_tac o Q.AP_TERM ‘LENGTH’) >> simp[]) >>
  ‘0 < L’ by (Cases_on ‘ps.acq’ >> fs[]) >>
  (* the M4 queue's head is the next handle *)
  ‘queued (n2w lfdn) (hdl (n2w lfdn) ps.b.nxt) 0 (gstate (GLI m) (srelabel m) (GV1 m pol w0) n)’
    by (simp[queued_def, lq_def] >> Cases_on ‘ps.acq’ >> fs[GENLIST_CONS]) >>
  ‘∃N. MEM (hdl (n2w lfdn) ps.b.nxt) (wacc (gperf (GLI m) (srelabel m) (GV1 m pol w0) N))’
    by (qpat_x_assum ‘∀c k n. queued _ _ _ _ ⇒ _’ drule >> simp[]) >>
  (* it was not handed out by round n *)
  ‘¬MEM (hdl (n2w lfdn) ps.b.nxt) (wacc (gperf (GLI m) (srelabel m) (GV1 m pol w0) n))’
    by (qpat_x_assum ‘GENLIST _ _ = wacc _’ (SUBST1_TAC o SYM) >>
        simp[MEM_GENLIST] >> rpt strip_tac >>
        rename1 ‘_ = hdl (n2w lfdn) j’ >>
        qspecl_then [‘j’, ‘ps.b.nxt’, ‘LENGTH s2.clients’, ‘n2w lfdn’] mp_tac
          (Q.GENL [‘j1’, ‘j2’, ‘k’, ‘lfd’] hdl_neq) >>
        simp[Abbr ‘L’]) >>
  drule_all gen_wacc_grow_accept >> strip_tac >> metis_tac[]
QED
