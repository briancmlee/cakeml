(*
  KV reads soon on the PF run: an fd L1 holds with input pending is read
  by KV again, provided what the M4 connection's client sent is always a
  prefix of printed valid requests.  honestEchoL0Obl's echo_read_soon for
  KV: gen_sim (honestL0GenS2) for echo_sim, honestKvReadSoonM's
  kv_read_soon_l for read_soon_live (no bound on the rounds; no
  end-of-file premise).

  MAIN: kv_gen_run, kv_read_soon_pf.
*)
Theory honestKvReadSoonPF
Ancestors
  honestKvReadSoonM honestL0GenS2 honestKvL0Obl
  honestL0GenSimLive honestEchoL0Obl
  honestL1PFObl honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel
  asyncHLSimTick asyncHLSimRun asyncHLSimWorld asyncHLModel asyncRunOkGen
  asyncServerVLiveL asyncM4LiveWorld asyncKvModel asyncM4SockInv asyncM4GTrans asyncM4GRounds
  asyncM4Relabel asyncM4SockModel asyncM4Loop asyncM3World asyncCore asyncLevel1
  HttpSpec alist
Libs
  preamble

Overload KV1[local] = “v1of (n2w lfdn) (psk (n2w lfdn) pol KI KS w0)”
Overload KPSK[local] = “psk (n2w lfdn) pol KI KS w0”

Theorem kv_gen_run:
  kv_run lfdn pol w0 ⇒ gen_run lfdn (kv_server lfdn) pol w0
Proof
  rw[kv_run_def, gen_run_def, kv_server_uses_ok]
QED

(* The version-1 world of the PF KV run is a fresh fair M4 world *)
Theorem kv_v1_world:
  kv_run lfdn pol w0 ⇒
  KV1.listeners = [(n2w lfdn, [])] ∧ KV1.conns = [] ∧ sched_wf KV1
Proof
  PURE_REWRITE_TAC[kv_run_def] >> strip_tac >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[run_ok_def, winv_def] >>
  drule_all psk_server_world >> strip_tac >>
  rpt conj_tac >- simp[v1of_def] >- simp[v1of_def] >>
  irule v1of_sched_wf >> simp[]
QED

(* MAIN: an fd L1 holds with input pending is read by KV again *)
Theorem kv_read_soon_pf:
  kv_run lfdn pol w0 ∧
  ALOOKUP (rstate (n2w lfdn) pol KI KS w0 m).b.tbl h = SOME f ∧
  inb_of (rstate (n2w lfdn) pol KI KS w0 m) f ≠ [] ∧
  (∀k. ∃rqs. EVERY valid_brequest rqs ∧
             sent_upto h k KV1 ≼ HttpSpec$bytes (FLAT (MAP print_brequest rqs))) ⇒
  ∃i kk. MEM (Read h kk) (new_actions (log_of KS) (rhist (n2w lfdn) pol KI KS w0 (m + i)))
Proof
  strip_tac >>
  drule kv_gen_run >> strip_tac >>
  drule_then (qspec_then ‘m’ strip_assume_tac) gen_sim >>
  ‘lfdn < dimword (:64)’ by fs[kv_run_def] >>
  qabbrev_tac ‘ps = rstate (n2w lfdn) pol KI KS w0 m’ >>
  qabbrev_tac ‘cm = FST (pcm (n2w lfdn) pol KI KS w0 m)’ >>
  Cases_on ‘hst (n2w lfdn) KI KS KPSK m’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hs = hs_of ps’ by fs[] >>
  ‘pv_rel (n2w lfdn) cm ps s2’ by fs[] >>
  ‘hsim0 (n2w lfdn) (gstate KI KS KV1 m) (s2, hs)’ by fs[hsim_def] >>
  (* f's handle is the j-th, and client j has f's input *)
  ‘∃j. j < ps.b.nxt ∧ h = hdl (n2w lfdn) j ∧ ALOOKUP s2.open_fds f = SOME j’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, hs_of_def] >> metis_tac[]) >>
  ‘(EL j s2.clients).incoming = inb_of ps f’
    by (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> simp[pv_rel_def] >> strip_tac >>
        first_x_assum drule >> strip_tac >> gvs[]) >>
  ‘j < LENGTH s2.clients’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, hs_of_def]) >>
  (* the M4 connection hdl j, with the same input, was handed out *)
  ‘MEM (hdl (n2w lfdn) j) (MAP FST (gstate KI KS KV1 m).conns)’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, MEM_GENLIST] >>
        metis_tac[]) >>
  ‘∃cn. ALOOKUP (gstate KI KS KV1 m).conns (hdl (n2w lfdn) j) = SOME cn’
    by (Cases_on ‘ALOOKUP (gstate KI KS KV1 m).conns (hdl (n2w lfdn) j)’ >>
        fs[ALOOKUP_NONE]) >>
  ‘cn.incoming = inb_of ps f’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def] >> strip_tac >>
        TRY (fs[] >> NO_TAC) >>
        qpat_x_assum ‘∀j cn. _ ∧ ALOOKUP _ _ = SOME cn ⇒ _’
          (qspecl_then [‘j’, ‘cn’] mp_tac) >> simp[]) >>
  ‘MEM (hdl (n2w lfdn) j) (wacc (gperf KI KS KV1 m))’
    by (qpat_x_assum ‘GENLIST _ _ = wacc _’ (SUBST1_TAC o SYM) >> simp[MEM_GENLIST] >>
        metis_tac[]) >>
  drule kv_v1_world >> strip_tac >>
  qspecl_then [‘KV1’, ‘lfdn’, ‘hdl (n2w lfdn) j’, ‘m’, ‘cn’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’, ‘cn’] kv_read_soon_l) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
  strip_tac >> fs[reads_c_def] >>
  drule_then (qspec_then ‘m + i’ strip_assume_tac) gen_sim >>
  qexistsl_tac [‘i’, ‘k’] >> gvs[gacts_def]
QED

Theorem kv_run_hyp:
  kv_run lfdn pol w0 ⇒ run_hyp (n2w lfdn) pol KI KS w0
Proof
  PURE_REWRITE_TAC[kv_run_def, run_hyp_def] >> strip_tac >> fs[winv_def]
QED

(* MAIN: S3w at one fd f (echo_S3w's induction): from a round n0 on, if
   every handle L1 maps to f has a client that only ever sent a prefix of
   printed valid requests, then once f is no longer fetched its inbox
   empties.  (S3w for all fds is false for KV: after an invalid request
   its handler never reads that handle again.) *)
Theorem kv_S3w_f:
  kv_run lfdn pol w0 ∧ n0 ≤ n ∧
  (∀r h. n0 ≤ r ∧ ALOOKUP (rstate (n2w lfdn) pol KI KS w0 r).b.tbl h = SOME f ⇒
         ∀k. ∃rqs. EVERY valid_brequest rqs ∧
                   sent_upto h k KV1 ≼ HttpSpec$bytes (FLAT (MAP print_brequest rqs))) ∧
  (∀k. n ≤ k ⇒ ¬fetched_at (n2w lfdn) pol KI KS w0 k f) ⇒
  ∃n'. n ≤ n' ∧ inb_of (rstate (n2w lfdn) pol KI KS w0 n') f = []
Proof
  strip_tac >> drule kv_run_hyp >> strip_tac >>
  ‘run_ok (n2w lfdn) pol KI KS w0’ by fs[run_hyp_def] >>
  ‘∀L r. n ≤ r ∧ LENGTH (inb_of (rstate (n2w lfdn) pol KI KS w0 r) f) = L ⇒
         ∃n'. n ≤ n' ∧ inb_of (rstate (n2w lfdn) pol KI KS w0 n') f = []’
    suffices_by metis_tac[LESS_EQ_REFL] >>
  completeInduct_on ‘L’ >> rpt strip_tac >>
  Cases_on ‘inb_of (rstate (n2w lfdn) pol KI KS w0 r) f = []’ >- metis_tac[] >>
  drule_all run_held >> strip_tac >>
  ‘∀k. ∃rqs. EVERY valid_brequest rqs ∧
             sent_upto h k KV1 ≼ HttpSpec$bytes (FLAT (MAP print_brequest rqs))’
    by (qpat_x_assum ‘∀r h. n0 ≤ r ∧ _ ⇒ _’ irule >> qexists_tac ‘r’ >> simp[]) >>
  qspecl_then [‘lfdn’, ‘pol’, ‘w0’, ‘r’, ‘h’, ‘f’] mp_tac
    (Q.GENL [‘lfdn’, ‘pol’, ‘w0’, ‘m’, ‘h’, ‘f’] kv_read_soon_pf) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on ‘inb_of (rstate (n2w lfdn) pol KI KS w0 (r + i)) f = []’
  >- (qexists_tac ‘r + i’ >> simp[]) >>
  ‘ALOOKUP (rstate (n2w lfdn) pol KI KS w0 (r + i)).b.tbl h = SOME f’
    by (drule run_tbl_keep >> disch_then drule >> disch_then (qspec_then ‘i’ irule) >>
        simp[]) >>
  ‘¬fetched_at (n2w lfdn) pol KI KS w0 (r + i) f’ by simp[] >>
  ‘LENGTH (inb_of (rstate (n2w lfdn) pol KI KS w0 (SUC (r + i))) f) <
   LENGTH (inb_of (rstate (n2w lfdn) pol KI KS w0 (r + i)) f)’
    by (irule run_read_shrinks >> metis_tac[]) >>
  ‘LENGTH (inb_of (rstate (n2w lfdn) pol KI KS w0 (r + i)) f) ≤ L’
    by (drule run_inb_drop >> disch_then (qspecl_then [‘r’, ‘f’, ‘i’] mp_tac) >>
        simp[] >> strip_tac >> simp[LENGTH_DROP]) >>
  qpat_x_assum ‘∀m. m < L ⇒ _’ (qspec_then
    ‘LENGTH (inb_of (rstate (n2w lfdn) pol KI KS w0 (SUC (r + i))) f)’ mp_tac) >>
  impl_tac >- fs[] >> disch_then (qspec_then ‘SUC (r + i)’ mp_tac) >> fs[]
QED
