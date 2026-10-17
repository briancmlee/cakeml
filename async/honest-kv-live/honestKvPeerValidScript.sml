(*
  From the peer's validity on the trace's channel to the M4 client's
  validity that kv_S3w_f asks for.  For f connected (FConn f) in round a
  and never again, client j = cl (pcm (SUC a)) f of psk is the M4
  connection hdl j: what it sent by step k is what L1 fetched on f
  (psk_sent2, client_since), and every handle L1 maps to f after round a
  is hdl j (pv_rel, hsim0, client_stable).

  MAIN: kv_tbl_client, kv_client_valid, kv_S3w_conn.
*)
Theory honestKvPeerValid
Ancestors
  honestKvReadSoonPF honestKvReadSoonM honestL0GenS2 honestKvL0Obl
  honestEchoL0SrvOut asyncHLEchoSpec2 honestL1PFInput honestL1PFClient
  honestL1PFOutLive honestL1PFStream
  honestL0GenSimLive honestEchoL0Obl
  honestL1PFObl honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel
  asyncHLSimTick asyncHLSimRun asyncHLSimWorld asyncHLModel EchoSpec2
  asyncM4GTrans asyncM4GRounds asyncM3World asyncCore asyncLevel1
  HttpSpec alist
Libs
  preamble

Overload KV1[local] = “v1of (n2w lfdn) (psk (n2w lfdn) pol KI KS w0)”
Overload KPSK[local] = “psk (n2w lfdn) pol KI KS w0”

Theorem pars_add[local]:
  ∀a. pars lfd pol ifds m w0 0 (k + a) =
      pars lfd pol ifds m w0 0 k ++ pars lfd pol ifds m w0 k a
Proof
  gen_tac >> rewrite_tac[pars_def] >> ‘k + a = a + k’ by simp[] >> pop_assum SUBST1_TAC >>
  rewrite_tac[GENLIST_APPEND, FLAT_APPEND] >> simp[] >> AP_TERM_TAC >> simp[GENLIST_FUN_EQ]
QED

(* A handle L1 maps to f is the M4 connection of f's client *)
Theorem kv_tbl_client:
  kv_run lfdn pol w0 ∧ ALOOKUP (rstate (n2w lfdn) pol KI KS w0 r).b.tbl h = SOME f ⇒
  h = hdl (n2w lfdn) (cl (FST (pcm (n2w lfdn) pol KI KS w0 r)) f) ∧
  cl (FST (pcm (n2w lfdn) pol KI KS w0 r)) f < dimword (:64) − 1
Proof
  strip_tac >>
  drule kv_gen_run >> strip_tac >>
  drule_then (qspec_then ‘r’ strip_assume_tac) gen_sim >>
  qabbrev_tac ‘ps = rstate (n2w lfdn) pol KI KS w0 r’ >>
  qabbrev_tac ‘cm = FST (pcm (n2w lfdn) pol KI KS w0 r)’ >>
  Cases_on ‘hst (n2w lfdn) KI KS KPSK r’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hs = hs_of ps’ by fs[] >>
  ‘pv_rel (n2w lfdn) cm ps s2’ by fs[] >>
  ‘hsim0 (n2w lfdn) (gstate KI KS KV1 r) (s2, hs)’ by fs[hsim_def] >>
  ‘∃j. j < ps.b.nxt ∧ h = hdl (n2w lfdn) j ∧ ALOOKUP s2.open_fds f = SOME j’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, hs_of_def] >> metis_tac[]) >>
  ‘ALOOKUP s2.open_fds f = SOME (cl cm f)’
    by (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> simp[pv_rel_def] >> strip_tac >>
        first_x_assum drule >> simp[]) >>
  ‘j = cl cm f’ by fs[] >>
  ‘j < LENGTH s2.clients’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, hs_of_def]) >>
  ‘LENGTH s2.clients < dimword (:64) − 1’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def] >> strip_tac >>
        Cases_on ‘s2.clients’ >> fs[]) >>
  conj_tac >- simp[] >>
  qpat_x_assum ‘j < LENGTH s2.clients’ mp_tac >>
  qpat_x_assum ‘LENGTH s2.clients < _’ mp_tac >> simp[]
QED

(* MAIN: f's client's M4 connection only ever sent what L1 fetched on f,
   so it is valid if every fetched prefix is *)
Theorem kv_client_valid:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧
  MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 a) ∧
  (∀k. a < k ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 k)) ∧
  cl (FST (pcm (n2w lfdn) pol KI KS w0 (SUC a))) f < dimword (:64) − 1 ∧
  (∀M. ∃rqs. EVERY valid_brequest rqs ∧
             fdata f (rlogs (n2w lfdn) pol KI KS w0 a M) ≼
             HttpSpec$bytes (FLAT (MAP print_brequest rqs))) ⇒
  ∀k. ∃rqs. EVERY valid_brequest rqs ∧
            sent_upto (hdl (n2w lfdn) (cl (FST (pcm (n2w lfdn) pol KI KS w0 (SUC a))) f)) k KV1 ≼
            HttpSpec$bytes (FLAT (MAP print_brequest rqs))
Proof
  strip_tac >> gen_tac >>
  ‘oassm (n2w lfdn) pol KI KS w0’ by fs[oassm_def, kv_run_def] >>
  qabbrev_tac ‘j = cl (FST (pcm (n2w lfdn) pol KI KS w0 (SUC a))) f’ >>
  ‘l0_rely w0 ∧ fds_lt w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   ∀n. SND (pcm (n2w lfdn) pol KI KS w0 n) + 1 < dimword (:64)’
    by fs[kv_run_def, run_ok_def, winv_def] >>
  drule_all psk_server_world >> strip_tac >>
  ‘sent_upto (hdl (n2w lfdn) j) k KV1 = cdata j (pars (n2w lfdn) pol KI KS w0 0 k)’
    by (qspecl_then [‘KPSK’, ‘lfdn’, ‘j’, ‘k’] mp_tac
          (Q.GENL [‘s2’, ‘lfdn’, ‘j’, ‘n’] sent2_rn) >>
        impl_tac >- simp[] >> disch_then (SUBST1_TAC o SYM) >>
        simp[psk_sent2]) >>
  ‘cdata j (pars (n2w lfdn) pol KI KS w0 0 (a + k)) =
   fdata f (rlogs (n2w lfdn) pol KI KS w0 a k)’
    by (drule client_since >> disch_then drule >> disch_then (qspec_then ‘k’ mp_tac) >>
        impl_tac >- simp[] >> simp[Abbr ‘j’]) >>
  ‘cdata j (pars (n2w lfdn) pol KI KS w0 0 k) ≼ cdata j (pars (n2w lfdn) pol KI KS w0 0 (a + k))’
    by (‘a + k = k + a’ by simp[] >> pop_assum SUBST1_TAC >>
        simp[pars_add, cdata_append]) >>
  qpat_x_assum ‘∀M. ∃rqs. _’ (qspec_then ‘k’ strip_assume_tac) >>
  qexists_tac ‘rqs’ >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘fdata f (rlogs (n2w lfdn) pol KI KS w0 a k)’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  metis_tac[]
QED

(* MAIN: S3w at f, for f connected in round a and never again, if every
   prefix of what L1 fetched on f is a prefix of printed valid requests *)
Theorem kv_S3w_conn:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧
  MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 a) ∧
  (∀k. a < k ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 k)) ∧
  (∀M. ∃rqs. EVERY valid_brequest rqs ∧
             fdata f (rlogs (n2w lfdn) pol KI KS w0 a M) ≼
             HttpSpec$bytes (FLAT (MAP print_brequest rqs))) ∧
  a < n ∧ (∀k. n ≤ k ⇒ ¬fetched_at (n2w lfdn) pol KI KS w0 k f) ⇒
  ∃n'. n ≤ n' ∧ inb_of (rstate (n2w lfdn) pol KI KS w0 n') f = []
Proof
  strip_tac >>
  ‘oassm (n2w lfdn) pol KI KS w0’ by fs[oassm_def, kv_run_def] >>
  irule kv_S3w_f >> simp[] >> qexists_tac ‘SUC a’ >> simp[] >>
  rpt strip_tac >>
  drule_all kv_tbl_client >> strip_tac >>
  ‘ALOOKUP (FST (pcm (n2w lfdn) pol KI KS w0 r)) f =
   SOME (cl (FST (pcm (n2w lfdn) pol KI KS w0 (SUC a))) f)’
    by (drule client_stable >> disch_then drule >>
        disch_then (qspecl_then [‘r − a’, ‘r’] mp_tac) >>
        impl_tac
        >- (rpt conj_tac >> TRY (simp[] >> NO_TAC) >> rpt strip_tac >>
            qpat_x_assum ‘∀k. a < k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
        simp[]) >>
  ‘cl (FST (pcm (n2w lfdn) pol KI KS w0 r)) f =
   cl (FST (pcm (n2w lfdn) pol KI KS w0 (SUC a))) f’
    by simp[cl_def] >>
  qpat_x_assum ‘h = _’ SUBST1_TAC >>
  qpat_x_assum ‘cl _ f = _’ (fn th => REWRITE_TAC[th] >> assume_tac th) >>
  irule kv_client_valid >> fs[]
QED
