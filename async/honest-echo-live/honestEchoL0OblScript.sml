(*
  The echo's obligations for R1-live (design/47 B): the PF echo,
  m = srelabel (server lfdn) polled through interest [n2w lfdn], meets S1
  (honestL1PFObl, for every such server) and S2.

  No new reasoning about the server: the PF run's history is the handle
  layer's in the version-2 world psk (R1-safe, l1pf_refines_hl), which is
  the M4 loop's in the version-1 world v1of psk (close-v2-sim, hrun_sim),
  with the worlds related (hsim).  M4's liveness lemmas (asyncM4AcceptSoon)
  then speak about the PF run's actions.
*)
Theory honestEchoL0Obl
Ancestors
  honestL1PFObl honestL1PFConnRun honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel
  asyncHLSimRun asyncHLSimWorld asyncHLModel asyncM4AcceptSoon asyncM4Queue
  asyncM4EchoRunOk asyncM4SockInv asyncM4GTrans asyncM4GRounds asyncM4Relabel asyncM4SockModel
  asyncM4Loop asyncM3World asyncCore asyncLevel1 alist
Libs
  preamble

Overload ES = “srelabel (server lfdn)”
Overload EI = “interest [n2w lfdn : word64]”

(* The PF echo's run hypotheses *)
Definition echo_run_def:
  echo_run lfdn pol w0 ⇔
    run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
    (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64)) ∧
    lfdn < dimword (:64)
End

Overload PSK = “psk (n2w lfdn) pol EI ES w0”
Overload V1 = “v1of (n2w lfdn) (psk (n2w lfdn) pol EI ES w0)”

(* ------------------------------------------------------------------------
   The three runs agree
   ------------------------------------------------------------------------ *)

(* The PF echo's history is the M4 echo's in v1of psk; its handle table is
   the handle layer's, whose state the M4 state simulates *)
Theorem echo_sim:
  echo_run lfdn pol w0 ⇒
  ∀n. rhist (n2w lfdn) pol EI ES w0 n = ghist EI ES V1 n ∧
      hsim (n2w lfdn) (gstate EI ES V1 n) (hst (n2w lfdn) EI ES PSK n) ∧
      SND (hst (n2w lfdn) EI ES PSK n) = hs_of (rstate (n2w lfdn) pol EI ES w0 n) ∧
      pv_rel (n2w lfdn) (FST (pcm (n2w lfdn) pol EI ES w0 n))
             (rstate (n2w lfdn) pol EI ES w0 n) (FST (hst (n2w lfdn) EI ES PSK n)) ∧
      GENLIST (hdl (n2w lfdn)) (rstate (n2w lfdn) pol EI ES w0 n).b.nxt =
        wacc (gperf EI ES V1 n)
Proof
  PURE_REWRITE_TAC[echo_run_def] >> strip_tac >> gen_tac >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[run_ok_def, winv_def] >>
  drule_all psk_server_world >> strip_tac >>
  drule_all hrun_sim >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_then (qspec_then ‘n’ assume_tac) prun_some >>
  Cases_on ‘prun (n2w lfdn) pol EI ES w0 n’ >> rename1 ‘_ = (hh, x)’ >> PairCases_on ‘x’ >>
  drule_all l1pf_refines_hl >> strip_tac >>
  gvs[rhist_def, rstate_def, hs_of_def]
QED

(* ------------------------------------------------------------------------
   S2
   ------------------------------------------------------------------------ *)

(* A successful round accepts only on the listener *)
Theorem pacts_accept_lfd:
  ∀acts w ps rs evs ws'.
    pacts lfd (w, ps) acts = SOME (rs, evs, ws') ∧ MEM (Accept l) acts ⇒ l = lfd
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> TRY (gvs[pdo_def, AllCaseEqs()] >> NO_TAC) >>
  PairCases_on ‘ws1’ >> metis_tac[]
QED

(* An accept performed pairs an Accept with its result *)
Theorem wacc_accept:
  ∀ps. MEM c (wacc ps) ⇒ ∃l. MEM (Accept l, Accepted (SOME c)) ps
Proof
  Induct >> simp[wacc_def, FORALL_PROD] >> rpt gen_tac >> every_case_tac >>
  rw[] >> metis_tac[]
QED

(* Every Accept of the PF echo is on its listener (its rounds succeed) *)
Theorem round_accept_lfd:
  echo_run lfdn pol w0 ∧
  MEM (Accept l) (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 k)) ⇒
  l = n2w lfdn
Proof
  PURE_REWRITE_TAC[echo_run_def] >> strip_tac >>
  drule_then (qspec_then ‘k’ strip_assume_tac) prun_round >>
  gvs[pround_def, AllCaseEqs()] >>
  irule pacts_accept_lfd >> metis_tac[]
QED

(* An accept the M4 run performed after round n is an Accept of the PF echo
   in some round k ≥ n *)
Theorem wacc_grow_accept:
  echo_run lfdn pol w0 ∧ ¬MEM c (wacc (gperf EI ES V1 n)) ⇒
  ∀N. MEM c (wacc (gperf EI ES V1 N)) ⇒
      ∃k. n ≤ k ∧ k < N ∧
          MEM (Accept (n2w lfdn)) (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 k))
Proof
  strip_tac >> Induct >- simp[gperf_def, wacc_def] >>
  simp[gperf_SUC] >> strip_tac
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> simp[]) >>
  ‘n ≤ N’
    by (CCONTR_TAC >> qpat_x_assum ‘¬MEM _ _’ mp_tac >> simp[] >>
        irule wacc_mono >> qexists_tac ‘SUC N’ >> simp[gperf_SUC]) >>
  drule wacc_accept >> strip_tac >>
  ‘grun_ok EI ES V1’ by (irule echo_grun_ok >> fs[echo_run_def, v1of_def]) >>
  ‘LENGTH (gres EI ES V1 N) = LENGTH (gacts EI ES V1 N)’ by simp[LENGTH_gres] >>
  ‘MEM (Accept l) (gacts EI ES V1 N)’ by (gvs[MEM_ZIP] >> metis_tac[EL_MEM]) >>
  qexists_tac ‘N’ >> simp[] >>
  drule_then (qspec_then ‘N’ strip_assume_tac) echo_sim >>
  ‘MEM (Accept l) (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 N))’
    by gvs[gacts_def] >>
  drule_all round_accept_lfd >> strip_tac >> gvs[]
QED

(* MAIN: the PF echo meets S2 *)
Theorem echo_S2:
  echo_run lfdn pol w0 ⇒ S2 (n2w lfdn) pol EI ES w0
Proof
  strip_tac >> simp[S2_def] >> rpt strip_tac >>
  drule_then (qspec_then ‘n’ strip_assume_tac) echo_sim >>
  ‘lfdn < dimword (:64)’ by fs[echo_run_def] >>
  qabbrev_tac ‘ps = rstate (n2w lfdn) pol EI ES w0 n’ >>
  qabbrev_tac ‘cm = FST (pcm (n2w lfdn) pol EI ES w0 n)’ >>
  Cases_on ‘hst (n2w lfdn) EI ES PSK n’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hs = hs_of ps’ by fs[] >>
  ‘pv_rel (n2w lfdn) cm ps s2’ by fs[] >>
  ‘hsim0 (n2w lfdn) (gstate EI ES V1 n) (s2, hs)’ by fs[hsim_def] >>
  ‘s2.listening = [(n2w lfdn, MAP (cl cm) ps.acq)]’ by fs[pv_rel_def] >>
  ‘hs.nxt = ps.b.nxt’ by simp[hs_of_def] >>
  qabbrev_tac ‘L = LENGTH s2.clients − ps.b.nxt’ >>
  ‘s2.listening = [(n2w lfdn, GENLIST (λi. ps.b.nxt + i) L)] ∧
   (gstate EI ES V1 n).listeners =
     [(n2w lfdn, GENLIST (λi. hdl (n2w lfdn) (ps.b.nxt + i)) L)] ∧
   ps.b.nxt ≤ LENGTH s2.clients ∧ LENGTH s2.clients < dimword (:64)’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, Abbr ‘L’] >>
        rw[] >> fs[]) >>
  ‘L = LENGTH ps.acq’
    by (‘MAP (cl cm) ps.acq = GENLIST (λi. ps.b.nxt + i) L’ by fs[] >>
        pop_assum (mp_tac o Q.AP_TERM ‘LENGTH’) >> simp[]) >>
  ‘0 < L’ by (Cases_on ‘ps.acq’ >> fs[]) >>
  (* the M4 queue's head is the next handle *)
  ‘queued (n2w lfdn) (hdl (n2w lfdn) ps.b.nxt) 0 (gstate EI ES V1 n)’
    by (simp[queued_def, lq_def] >> Cases_on ‘ps.acq’ >> fs[GENLIST_CONS]) >>
  ‘∃N. MEM (hdl (n2w lfdn) ps.b.nxt) (wacc (gperf EI ES V1 N))’
    by (qspecl_then [‘V1’, ‘lfdn’, ‘hdl (n2w lfdn) ps.b.nxt’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘c’] queue_progress) >>
        impl_tac >- simp[v1of_def] >> metis_tac[]) >>
  (* it was not handed out by round n *)
  ‘¬MEM (hdl (n2w lfdn) ps.b.nxt) (wacc (gperf EI ES V1 n))’
    by (qpat_x_assum ‘GENLIST _ _ = wacc _’ (SUBST1_TAC o SYM) >>
        simp[MEM_GENLIST] >> rpt strip_tac >>
        rename1 ‘_ = hdl (n2w lfdn) j’ >>
        qspecl_then [‘j’, ‘ps.b.nxt’, ‘LENGTH s2.clients’, ‘n2w lfdn’] mp_tac
          (Q.GENL [‘j1’, ‘j2’, ‘k’, ‘lfd’] hdl_neq) >>
        simp[Abbr ‘L’]) >>
  drule_all wacc_grow_accept >> strip_tac >> metis_tac[]
QED
