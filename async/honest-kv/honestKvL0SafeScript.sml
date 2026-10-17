(*
  P4 (design/46), step E: the key-value server's raw L0 trace on the
  honest L1 is safe (kv_safe_l0), from the version-2 theorem kv2_safe_if.

  Every finite prefix evs of the run is looked at on its own
  (kv_safeG_prefixes).  rtm E evs is the first round boundary at or past
  evs; the guard (D40) held in every round before it (a failed guard
  freezes the run: prun_frozen), so R1 applies to the world psk_upto N
  truncated at N = rtm E evs (upto_world).  A raw prefix pre inside round i
  is paired with the v2 instant SUC i (tm = rtm E); raw episode j with v2
  episode j (step D, the identity) for j < 2^64 − 1, through handle j
  (run_pair, hdl_v2_bytes_if).  A raw episode j ≥ 2^64 − 1 is never handed
  out, so it sent nothing (sent_unhanded); a v2 episode c ≥ 2^64 − 1 read
  nothing (accepted_bound_if).  kv_server_view_safe moves the v2 safety to
  the raw prefix.

  kv_run_safe: any loop interest under ifds_sub (D26: the program's live).
  kv_run_safe_live: the program's live interest.
*)
Theory honestKvL0Safe
Ancestors
  words llist rich_list HttpSpec HttpKvSpec asyncKvOrderGen asyncKvModel asyncKvEof
  asyncTranscript asyncServer asyncRunOkGen asyncM4GTrans asyncM4LiveInterest
  asyncHLModel asyncHLSimRunGen asyncProto2Model asyncKv2Bridge asyncKv2Safe
  EchoSpec2 honestL1Steps honestL1PFModel honestL1PFRefine honestL1PFProg honestL1PFSpec
  honestEchoL0Spec honestEchoL0Trace honestEchoL0Run honestEchoL0Safe
  honestHttpKvL0Spec
  honestKvL0View honestKvL0Trunc honestKvL0Count honestKvL0Run honestKvL0Pair
Libs
  preamble

(* ------------------------------------------------------------------------
   Safety, prefix by prefix
   ------------------------------------------------------------------------ *)

Theorem kv_safe_l0_G:
  kv_safe_l0 io ⇔ kv_safeG l0_read l0_sent io
Proof
  ‘∀rss order evs x y. precedes_l0 rss order evs x y ⇔
                       precedesG l0_read l0_sent rss order evs x y’
    by simp[FORALL_PROD, precedes_l0_def, precedesG_def] >>
  simp[kv_safe_l0_def, kv_safeG_def, is_order_l0_def, is_ord_def]
QED

(* Safety looks only at finite prefixes *)
Theorem kv_safeG_prefixes:
  (∀evs. LPREFIX (fromList evs) io ⇒ kv_safeG Rd Wr (fromList evs)) ⇒ kv_safeG Rd Wr io
Proof
  strip_tac >> rewrite_tac[kv_safeG_def] >> rpt strip_tac >>
  first_x_assum (drule_then (mp_tac o REWRITE_RULE [kv_safeG_def])) >>
  disch_then (qspecl_then [‘evs’, ‘rss’, ‘rests’] mp_tac) >>
  impl_tac >- fs[] >> simp[]
QED

(* The empty trace is safe *)
Theorem kv_safeG_nil:
  (∀c. Rd c [] = [] ∧ Wr c [] = []) ⇒ kv_safeG Rd Wr (fromList [])
Proof
  rw[kv_safeG_def] >> gvs[LPREFIX_fromList, from_toList] >>
  qexists_tac ‘[]’ >> simp[is_ord_def, earlier_def] >>
  simp[COUNT_LIST_def]
QED

(* ------------------------------------------------------------------------
   The run's events, round boundaries
   ------------------------------------------------------------------------ *)

Definition pevs_def:
  pevs lfd hw ifds m ws0 i = FST (SND (SND (honestL1PFSpec$prun lfd hw ifds m ws0 i)))
End

Theorem FLAT_GENLIST_le[local]:
  ∀d n. FLAT (GENLIST f n) ≼ FLAT (GENLIST f (n + d))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[GSYM ADD_SUC, GENLIST, SNOC_APPEND] >>
  rw[rich_listTheory.IS_PREFIX_APPEND] >> simp[]
QED

Theorem FLAT_GENLIST_mono:
  i ≤ j ⇒ FLAT (GENLIST f i) ≼ FLAT (GENLIST f j)
Proof
  strip_tac >> qspecl_then [‘j − i’, ‘i’] mp_tac FLAT_GENLIST_le >> simp[]
QED

Theorem pevs_mono:
  (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ⇒
  ∀i j. i ≤ j ⇒ pevs lfd hw ifds m ws0 i ≼ pevs lfd hw ifds m ws0 j
Proof
  rpt strip_tac >> drule prun_FLAT >> strip_tac >>
  simp[pevs_def] >> pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule FLAT_GENLIST_mono >> simp[]
QED

(* Once the guard fails, the run no longer changes *)
Theorem prun_frozen:
  (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ∧
  ¬hdl_room lfd (SND (FST (SND (prun lfd hw ifds m ws0 i))))
     (naccepts (new_actions (log_of m) (FST (prun lfd hw ifds m ws0 i)))) ⇒
  ∀d. prun lfd hw ifds m ws0 (i + d) = prun lfd hw ifds m ws0 i
Proof
  strip_tac >> Induct >> simp[] >>
  drule prun_SUC >> disch_then (qspec_then ‘i + d’ mp_tac) >>
  asm_simp_tac (srw_ss()) [ADD_CLAUSES]
QED

(* The first round boundary at or past evs *)
Definition rtm_def:
  rtm (E : num -> 'a list) evs = LEAST i. evs ≼ E i
End

Theorem rtm_spec:
  evs ≼ E n ⇒ evs ≼ E (rtm E evs) ∧ rtm E evs ≤ n ∧ ∀i. i < rtm E evs ⇒ ¬(evs ≼ E i)
Proof
  strip_tac >> simp[rtm_def] >> numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> simp[] >> CCONTR_TAC >> fs[NOT_LESS_EQUAL] >> metis_tac[]
QED

Theorem rtm_mono:
  evs ≼ E n ∧ evs' ≼ evs ⇒ rtm E evs' ≤ rtm E evs
Proof
  strip_tac >> drule rtm_spec >> strip_tac >>
  ‘evs' ≼ E (rtm E evs)’ by metis_tac[IS_PREFIX_TRANS] >>
  drule rtm_spec >> simp[]
QED

Theorem rtm_round:
  (∀i j. i ≤ j ⇒ E i ≼ E j) ∧ evs ≼ E n ∧ rtm E evs = SUC i ⇒
  E i ≼ evs ∧ evs ≼ E (SUC i)
Proof
  strip_tac >> drule rtm_spec >> strip_tac >>
  ‘evs ≼ E (SUC i)’ by metis_tac[] >>
  ‘¬(evs ≼ E i)’ by (first_x_assum irule >> simp[]) >>
  ‘E i ≼ E (SUC i)’ by (first_x_assum irule >> simp[]) >>
  metis_tac[prefixes_is_prefix_total]
QED

(* Before the first boundary past evs, every round had room *)
Theorem rtm_room:
  (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ∧
  evs ≼ pevs lfd hw ifds m ws0 n ∧ rtm (pevs lfd hw ifds m ws0) evs = SUC M ⇒
  ∀i h ws evs' logs. i ≤ M ∧ prounds_t lfd hw ifds m ws0 i = SOME (h, ws, evs', logs) ⇒
    hdl_room lfd (SND ws) (naccepts (new_actions (log_of m) h))
Proof
  rpt strip_tac >> CCONTR_TAC >>
  ‘prun lfd hw ifds m ws0 i = (h, ws, evs', logs)’ by simp[prun_def] >>
  ‘∀d. prun lfd hw ifds m ws0 (i + d) = prun lfd hw ifds m ws0 i’
    by (irule prun_frozen >> simp[]) >>
  ‘pevs lfd hw ifds m ws0 (SUC M) = pevs lfd hw ifds m ws0 i’
    by (simp[pevs_def] >> first_x_assum (qspec_then ‘SUC M − i’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o MATCH_MP rtm_spec) >>
  qpat_x_assum ‘rtm _ _ = SUC M’ (fn th => fs[th]) >>
  ‘evs ≼ pevs lfd hw ifds m ws0 i’
    by (qpat_x_assum ‘pevs _ _ _ _ _ (SUC M) = _’ (fn th =>
          qpat_x_assum ‘evs ≼ pevs _ _ _ _ _ (SUC M)’ (fn th2 =>
            ACCEPT_TAC (REWRITE_RULE [th] th2)))) >>
  qpat_x_assum ‘∀i. i < SUC M ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Along the run of any server that writes only through handles it was
   handed
   ------------------------------------------------------------------------ *)

Theorem prun_ri_gen:
  writes_accepted m ∧ ri lfd m ([], ws0, []) ∧ (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ⇒
  ∀n. ri lfd m (FST (prun lfd hw ifds m ws0 n), FST (SND (prun lfd hw ifds m ws0 n)),
                pevs lfd hw ifds m ws0 n)
Proof
  rpt strip_tac >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘prounds_t lfd hw ifds m ws0 n’ >> simp[prun_def, pevs_def] >>
  PairCases_on ‘x’ >> simp[] >> metis_tac[ri_gen]
QED

(* honestEchoL0Safe's unhanded_sn, for any such server *)
Theorem unhanded_sn_gen:
  writes_accepted m ∧ ri lfd m ([], ws0, []) ⇒
  ∀n h w ps evs logs.
    prounds_t lfd hw ifds m ws0 n = SOME (h, (w, ps), evs, logs) ⇒
    ∀j. ps.b.nxt ≤ j ⇒ ep_sn j (0, []) evs = []
Proof
  strip_tac >> Induct >- (simp[prounds_t_def] >> rw[] >> simp[ep_fold_def]) >>
  rpt gen_tac >> simp[prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds m ws0 n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’, ‘x3’, ‘x4’] mp_tac) >> simp[] >> strip_tac >>
  ‘ri lfd m (x0, (x1, x2), x3)’ by metis_tac[ri_gen] >>
  IF_CASES_TAC >> simp[] >- (
    simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
    qabbrev_tac ‘acts = new_actions (log_of m) x0’ >>
    ‘x2.b.nxt + naccepts acts < dimword (:64)’ by gvs[hdl_room_def] >>
    qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
    Cases_on ‘l0_ep_st (0, []) x3’ >> rename1 ‘l0_ep_st _ x3 = (kk, opn)’ >> gvs[] >>
    ‘x2.b.nxt + naccepts acts < dimword (:64)’ by fs[] >>
    drule_all pround_acc >> strip_tac >>
    rpt strip_tac >> simp[ep_fold_APPEND] >>
    TRY (conj_tac >- (first_x_assum irule >> fs[])) >>
    qpat_x_assum ‘pround _ _ _ _ _ = _’
      (fn th => mp_tac (Q.INST [‘k’ |-> ‘kk’]
                         (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] pround_sn) th))) >>
    rpt (impl_tac >- fs[]) >> disch_then irule >> fs[]) >>
  rw[] >> gvs[]
QED

(* A raw episode past the handle space sent nothing *)
Theorem sent_unhanded:
  writes_accepted m ∧ ri lfd m ([], ws0, []) ∧ (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ∧
  pre ≼ pevs lfd hw ifds m ws0 n ∧ dimword (:64) − 1 ≤ j ⇒
  l0_sent j pre = []
Proof
  strip_tac >>
  drule_all prun_ri_gen >> disch_then (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘prounds_t lfd hw ifds m ws0 n’ >- metis_tac[] >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >>
  ‘prun lfd hw ifds m ws0 n = (x0, (x1, x2), x3, x4)’ by simp[prun_def] >>
  simp[pevs_def] >> rewrite_tac[ri_def] >> strip_tac >>
  ‘ep_sn j (0, []) x3 = []’
    by (mp_tac unhanded_sn_gen >> impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then drule >> disch_then irule >>
        qpat_x_assum ‘x2.b.nxt < _’ mp_tac >> qpat_x_assum ‘_ ≤ j’ mp_tac >> simp[]) >>
  ‘ep_sn j (0, []) pre ≼ ep_sn j (0, []) x3’
    by (irule ep_fold_prefix >> fs[pevs_def]) >>
  gvs[l0_sent_fold]
QED

(* MAIN, per round: raw episode j inside round i against handle j after
   rounds SUC i (read) and i (sent) *)
Theorem run_pair:
  writes_accepted m ∧ ri lfd m ([], ws0, []) ∧ (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ∧
  hdl_room lfd (SND (FST (SND (prun lfd hw ifds m ws0 i))))
    (naccepts (new_actions (log_of m) (FST (prun lfd hw ifds m ws0 i)))) ∧
  pevs lfd hw ifds m ws0 i ≼ pre ∧ pre ≼ pevs lfd hw ifds m ws0 (SUC i) ∧
  hdln (w2n lfd) j < dimword (:64) ⇒
  hread (hdl lfd j) (trans m (FST (prun lfd hw ifds m ws0 (SUC i)))) ≼ l0_read j pre ∧
  l0_sent j pre ≼ hwritten (hdl lfd j) (trans m (FST (prun lfd hw ifds m ws0 i)))
Proof
  strip_tac >>
  drule_all prun_ri_gen >> strip_tac >>
  ‘ri lfd m (FST (prun lfd hw ifds m ws0 i), FST (SND (prun lfd hw ifds m ws0 i)),
             pevs lfd hw ifds m ws0 i) ∧
   ri lfd m (FST (prun lfd hw ifds m ws0 (SUC i)), FST (SND (prun lfd hw ifds m ws0 (SUC i))),
             pevs lfd hw ifds m ws0 (SUC i))’ by simp[] >>
  qpat_x_assum ‘∀n. ri _ _ _’ kall_tac >>
  qpat_assum ‘∀n. prounds_t _ _ _ _ _ _ ≠ NONE’
    (mp_tac o Q.SPEC ‘i’ o Q.GEN ‘n’ o MATCH_MP prun_SUC) >>
  qpat_assum ‘hdl_room _ _ _’ (fn th => rewrite_tac[th]) >> strip_tac >>
  Cases_on ‘prun lfd hw ifds m ws0 i’ >> rename1 ‘_ = (h, r)’ >>
  PairCases_on ‘r’ >> rename1 ‘_ = (h, (w, ps), evs, logs)’ >>
  PairCases_on ‘ws'’ >>
  fs[pevs_def] >>
  ‘hread (hdl lfd j) (texec m (h ++ [snap'])) ≼ l0_read j pre ∧
   l0_sent j pre ≼ hwritten (hdl lfd j) (trans m h)’
    by (irule (SIMP_RULE std_ss [l1hdl_hdl] round_pair) >>
        rpt (first_assum (irule_at Any)) >> fs[]) >>
  simp[] >>
  ‘hread (hdl lfd j) (texec m (h ++ [snap'])) = hread (hdl lfd j) (trans m (h ++ [snap']))’
    by (irule hread_texec >> qpat_x_assum ‘ri _ _ (h ++ _, _, _)’ mp_tac >>
        simp[ri_def]) >>
  fs[]
QED

(* ------------------------------------------------------------------------
   The truncated v2 world
   ------------------------------------------------------------------------ *)

(* MAIN: with room in every round up to M, the world truncated at SUC M is
   well formed and its handle loop has L1's history up to round SUC M *)
Theorem upto_world:
  writes_accepted m ∧ ri lfd m ([], (w1, pinit), []) ∧
  l0_rely w1 ∧ fds_lt w1 ∧ MEM lfd (l0_used w1) ∧
  (∀n. prounds_t lfd hw ifds m (w1, pinit) n ≠ NONE) ∧
  (∀i h ws evs logs. i ≤ M ∧ prounds_t lfd hw ifds m (w1, pinit) i = SOME (h, ws, evs, logs) ⇒
     hdl_room lfd (SND ws) (naccepts (new_actions (log_of m) h))) ⇒
  (psk_upto (SUC M) lfd (pol_self hw) ifds m w1).listening = [(lfd, [])] ∧
  (psk_upto (SUC M) lfd (pol_self hw) ifds m w1).clients = [] ∧
  (psk_upto (SUC M) lfd (pol_self hw) ifds m w1).open_fds = [] ∧
  alloc_ok (psk_upto (SUC M) lfd (pol_self hw) ifds m w1).alloc ∧
  sched_wf2 (psk_upto (SUC M) lfd (pol_self hw) ifds m w1) ∧
  ∀t. t ≤ SUC M ⇒
      hhist lfd ifds m (psk_upto (SUC M) lfd (pol_self hw) ifds m w1) t =
      FST (prun lfd hw ifds m (w1, pinit) t)
Proof
  strip_tac >>
  ‘∀n'. n' ≤ SUC M ⇒ SND (pcm lfd (pol_self hw) ifds m w1 n') + 1 < dimword (:64)’
    by (match_mp_tac prounds_t_pcm_bound >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC, first_assum MATCH_ACCEPT_TAC]) >>
  ‘sched_wf2 (psk_upto (SUC M) lfd (pol_self hw) ifds m w1)’
    by (irule psk_upto_sched_wf2 >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac
  >- simp[psk_upto_def, psk_def]
  >- simp[psk_upto_def, psk_def]
  >- simp[psk_upto_def, psk_def]
  >- simp[psk_upto_def, psk_def, run_alloc_ok]
  >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  ‘hhist lfd ifds m (psk_upto (SUC M) lfd (pol_self hw) ifds m w1) t =
   hhist lfd ifds m (psk lfd (pol_self hw) ifds m w1) t’
    by (drule psk_upto_hst >> simp[]) >>
  pop_assum SUBST1_TAC >>
  ‘prounds lfd (pol_self hw) ifds m (w1, pinit) t = SOME (prun lfd hw ifds m (w1, pinit) t)’
    by (‘prounds_t lfd hw ifds m (w1, pinit) t = prounds lfd (pol_self hw) ifds m (w1, pinit) t’
          by (irule prounds_t_prounds >> rpt strip_tac >>
              qpat_x_assum ‘∀i h ws evs logs. i ≤ M ∧ _ ⇒ _’ irule >>
              qexistsl [‘evs’, ‘i’, ‘logs’] >> conj_tac
              >- (qpat_x_assum ‘i < t’ mp_tac >> qpat_x_assum ‘t ≤ SUC M’ mp_tac >> simp[]) >>
              first_assum ACCEPT_TAC) >>
        pop_assum (fn th => rewrite_tac[GSYM th]) >>
        simp[prun_def] >> Cases_on ‘prounds_t lfd hw ifds m (w1, pinit) t’ >> simp[] >>
        metis_tac[]) >>
  Cases_on ‘prun lfd hw ifds m (w1, pinit) t’ >> PairCases_on ‘r’ >>
  mp_tac (Q.SPECL [‘SUC M’, ‘w1’, ‘pol_self hw’]
            (Q.GENL [‘N’, ‘w0’, ‘pol’] l1pf_refines_hl_upto)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The key-value server
   ------------------------------------------------------------------------ *)

Theorem kv_writes_accepted:
  writes_accepted (srelabel (kv_server k))
Proof
  irule uses_ok_writes_accepted >> qexists_tac ‘k’ >> simp[kv_server_uses_ok]
QED

Theorem hdln_small[local]:
  k < dimword (:64) − 1 ∧ j < dimword (:64) − 1 ⇒ hdln k j < dimword (:64)
Proof
  rw[hdln_def]
QED

(* MAIN: every finite prefix of the run is safe *)
Theorem kv_prefix_safe:
  ifds_sub (n2w k) ifds ∧ k < dimword (:64) − 1 ∧
  l0_rely w1 ∧ fds_lt w1 ∧ MEM (n2w k) (l0_used w1) ∧
  ri (n2w k) (srelabel (kv_server k)) ([], (w1, pinit), []) ∧
  (∀n. prounds_t (n2w k) hw ifds (srelabel (kv_server k)) (w1, pinit) n ≠ NONE) ∧
  evs ≼ pevs (n2w k) hw ifds (srelabel (kv_server k)) (w1, pinit) n ⇒
  kv_safeG l0_read l0_sent (fromList evs)
Proof
  strip_tac >>
  qabbrev_tac ‘m = srelabel (kv_server k)’ >>
  qabbrev_tac ‘E = pevs (n2w k) hw ifds m (w1, pinit)’ >>
  ‘writes_accepted m’ by simp[Abbr ‘m’, kv_writes_accepted] >>
  ‘∀i j. i ≤ j ⇒ E i ≼ E j’
    by (simp[Abbr ‘E’] >> match_mp_tac pevs_mono >> first_assum ACCEPT_TAC) >>
  ‘E 0 = []’ by simp[Abbr ‘E’, pevs_def] >>
  Cases_on ‘rtm E evs’
  >- (‘evs = []’
        by (qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o MATCH_MP rtm_spec) >> gvs[]) >>
      qpat_x_assum ‘evs = []’ SUBST1_TAC >> irule kv_safeG_nil >>
      simp[l0_read_def, l0_sent_def, l0_accepted_def]) >>
  rename1 ‘rtm E evs = SUC M’ >>
  ‘∀i h ws evs' logs. i ≤ M ∧ prounds_t (n2w k) hw ifds m (w1, pinit) i = SOME (h, ws, evs', logs) ⇒
     hdl_room (n2w k) (SND ws) (naccepts (new_actions (log_of m) h))’
    by (match_mp_tac rtm_room >> fs[Abbr ‘E’]) >>
  qspecl_then [‘m’, ‘n2w k’, ‘w1’, ‘hw’, ‘ifds’, ‘M’] mp_tac
    (Q.GENL [‘m’, ‘lfd’, ‘w1’, ‘hw’, ‘ifds’, ‘M’] upto_world) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qabbrev_tac ‘s2 = psk_upto (SUC M) (n2w k) (pol_self hw) ifds m w1’ >>
  ‘k < dimword (:64)’ by fs[] >>
  ‘w2n (n2w k : word64) = k’ by simp[] >>
  qspecl_then [‘KP2i k ifds s2’, ‘gtrace2i (kv_server k) k ifds s2’, ‘rtm E’,
               ‘λj. if j < dimword (:64) − 1 then SOME j else NONE’, ‘ep_read’, ‘ep_written’,
               ‘l0_read’, ‘l0_sent’, ‘fromList evs’]
    mp_tac (Q.GENL [‘vtr’, ‘io2’, ‘tm’, ‘e’, ‘RD2’, ‘WR2’, ‘RD1’, ‘WR1’, ‘io1’]
              kv_server_view_safe) >>
  disch_then match_mp_tac >> BETA_TAC >>
  rpt conj_tac
  >- (* the v2 trace grows *)
     (rpt strip_tac >> irule FLAT_GENLIST_mono >> simp[])
  >- (* the v2 trace's instants are its prefixes *)
     (gen_tac >> simp[rounds_LPREFIX])
  >- (* the pairing of instants is monotone *)
     (simp[LPREFIX_fromList, from_toList] >>
      rpt strip_tac >> irule rtm_mono >> metis_tac[IS_PREFIX_TRANS])
  >- (* the pairing is injective *)
     rw[]
  >- (* raw episodes past the handles sent nothing *)
     (simp[LPREFIX_fromList, from_toList] >>
      rpt strip_tac >> irule (INST_TYPE [alpha |-> “:unit option”] sent_unhanded) >> simp[] >>
      qexistsl [‘hw’, ‘ifds’, ‘n2w k’, ‘m’, ‘n’, ‘(w1, pinit)’] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      irule IS_PREFIX_TRANS >> qexists_tac ‘evs’ >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum ‘evs ≼ E n’ mp_tac >> simp[Abbr ‘E’])
  >- (* paired episodes: a prefix inside round i is paired with v2 instant SUC i *)
     (simp[LPREFIX_fromList, from_toList] >> rpt gen_tac >> strip_tac >>
      ‘evs' ≼ E n’
        by (irule IS_PREFIX_TRANS >> qexists_tac ‘evs’ >> conj_tac >> first_assum ACCEPT_TAC) >>
      ‘rtm E evs' ≤ SUC M’
        by (qpat_x_assum ‘rtm E evs = SUC M’ (SUBST1_TAC o SYM) >> irule rtm_mono >>
            conj_tac >- (qexists_tac ‘n’ >> first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
      Cases_on ‘rtm E evs'’
      >- (‘evs' = []’
            by (qpat_x_assum ‘evs' ≼ E n’ (mp_tac o CONJUNCT1 o MATCH_MP rtm_spec) >>
                qpat_x_assum ‘rtm E evs' = 0’ SUBST1_TAC >>
                qpat_x_assum ‘E 0 = []’ SUBST1_TAC >> simp[]) >>
          qpat_x_assum ‘evs' = []’ SUBST1_TAC >>
          simp[ep_read_def, ep_written_def, accepted_fds_def, l0_sent_def, l0_read_def, l0_accepted_def]) >>
      rename1 ‘rtm E evs' = SUC i’ >>
      ‘i ≤ M’ by (qpat_x_assum ‘SUC i ≤ SUC M’ mp_tac >> simp[]) >>
      ‘E i ≼ evs' ∧ evs' ≼ E (SUC i)’
        by (irule rtm_round >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, qexists_tac ‘n’ >> first_assum ACCEPT_TAC]) >>
      ‘pevs (n2w k) hw ifds m (w1,pinit) i ≼ evs' ∧
       evs' ≼ pevs (n2w k) hw ifds m (w1,pinit) (SUC i)’
        by (qpat_x_assum ‘E i ≼ evs'’ mp_tac >> qpat_x_assum ‘evs' ≼ E (SUC i)’ mp_tac >>
            simp[Abbr ‘E’]) >>
      ‘hdl_room (n2w k) (SND (FST (SND (prun (n2w k) hw ifds m (w1,pinit) i))))
         (naccepts (new_actions (log_of m) (FST (prun (n2w k) hw ifds m (w1,pinit) i))))’
        by (Cases_on ‘prounds_t (n2w k) hw ifds m (w1,pinit) i’
            >- (qpat_x_assum ‘∀n. prounds_t _ _ _ _ _ n ≠ NONE’ (qspec_then ‘i’ mp_tac) >>
                asm_rewrite_tac[]) >>
            rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
            ‘prun (n2w k) hw ifds m (w1,pinit) i = (x0,(x1,x2),x3,x4)’ by simp[prun_def] >>
            pop_assum SUBST1_TAC >> simp_tac std_ss [] >>
            qpat_x_assum ‘∀i h ws evs' logs. _’
              (qspecl_then [‘i’, ‘x0’, ‘(x1,x2)’, ‘x3’, ‘x4’] mp_tac) >>
            impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp_tac std_ss []) >>
      ‘hdln (w2n (n2w k : word64)) j < dimword (:64)’
        by (qpat_assum ‘w2n _ = k’ SUBST1_TAC >> qpat_x_assum ‘j < _’ mp_tac >>
            qpat_x_assum ‘k < dimword (:64) − 1’ mp_tac >> rw[hdln_def]) >>
      qspecl_then [‘m’, ‘n2w k’, ‘(w1,pinit)’, ‘hw’, ‘ifds’, ‘i’, ‘evs'’, ‘j’] mp_tac
        (Q.GENL [‘m’, ‘lfd’, ‘ws0’, ‘hw’, ‘ifds’, ‘i’, ‘pre’, ‘j’] run_pair) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      ‘srelabel (kv_server k) = m’ by simp[Abbr ‘m’] >>
      qspecl_then [‘k’, ‘ifds’, ‘s2’, ‘j’, ‘SUC i’] mp_tac
        (Q.GENL [‘lfdn’, ‘ifds’, ‘s2’, ‘j’, ‘n’] hdl_v2_bytes_if) >>
      qspecl_then [‘k’, ‘ifds’, ‘s2’, ‘j’, ‘i’] mp_tac
        (Q.GENL [‘lfdn’, ‘ifds’, ‘s2’, ‘j’, ‘n’] hdl_v2_bytes_if) >>
      qpat_x_assum ‘srelabel _ = m’ (fn th => rewrite_tac [th]) >>
      impl_tac
      >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, qpat_x_assum ‘j < _’ mp_tac >> simp[]]) >>
      strip_tac >>
      impl_tac
      >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, qpat_x_assum ‘j < _’ mp_tac >> simp[]]) >>
      strip_tac >>
      ‘hhist (n2w k) ifds m s2 (SUC i) = FST (prun (n2w k) hw ifds m (w1,pinit) (SUC i)) ∧
       hhist (n2w k) ifds m s2 i = FST (prun (n2w k) hw ifds m (w1,pinit) i)’
        by (conj_tac >> qpat_x_assum ‘∀t. t ≤ SUC M ⇒ _’ irule >>
            qpat_x_assum ‘i ≤ M’ mp_tac >> simp[]) >>
      qpat_x_assum ‘hread _ (trans m (hhist _ _ _ _ (SUC i))) = _’
        (fn th => rewrite_tac [GSYM th]) >>
      qpat_x_assum ‘hwritten _ (trans m (hhist _ _ _ _ i)) = _’
        (fn th => rewrite_tac [GSYM th]) >>
      qpat_x_assum ‘hhist _ _ _ _ (SUC i) = _’ (fn th => rewrite_tac [th]) >>
      qpat_x_assum ‘hhist _ _ _ _ i = _’ (fn th => rewrite_tac [th]) >>
      conj_tac >> first_assum ACCEPT_TAC)
  >- (* v2 episodes past the handles read nothing *)
     (rpt strip_tac >>
      ‘¬(c < dimword (:64) − 1)’ by (strip_tac >> first_x_assum (qspec_then ‘c’ mp_tac) >> simp[]) >>
      qspecl_then [‘k’, ‘kv_server k’, ‘s2’, ‘ifds’] mp_tac
        (Q.GENL [‘lfdn’, ‘m’, ‘s2’, ‘ifds’] accepted_bound_if) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[kv_server_uses_ok, kv_server_eof_last]]) >>
      disch_then (qspec_then ‘t’ mp_tac) >> qpat_x_assum ‘¬(c < _)’ mp_tac >> simp[ep_read_def])
  >- (* finitely many raw episodes read *)
     (simp[LPREFIX_fromList, from_toList] >> rpt strip_tac >> qexists_tac ‘COUNT_LIST (LENGTH (l0_accepted evs'))’ >>
      rw[MEM_COUNT_LIST] >> CCONTR_TAC >> fs[l0_read_def])
  >- (* what was sent grows *)
     (rpt strip_tac >> simp[l0_sent_fold] >> irule ep_fold_prefix >> simp[]) >>
  (* the v2 safety *)
  mp_tac (Q.INST [‘lfdn’ |-> ‘k’] kv2_safe_if) >> simp[kv_safe2_G]
QED

(* MAIN: the run of the key-value server past the listen is safe, for any
   loop interest under ifds_sub *)
Theorem kv_run_safe:
  ifds_sub (n2w k) ifds ∧ k < dimword (:64) − 1 ∧
  l0_rely w1 ∧ fds_lt w1 ∧ MEM (n2w k) (l0_used w1) ∧
  ri (n2w k) (srelabel (kv_server k)) ([], (w1, pinit), []) ∧
  (∀n. prounds_t (n2w k) hw ifds (srelabel (kv_server k)) (w1, pinit) n ≠ NONE) ⇒
  kv_safe_l0 (LFLATTEN (LGENLIST (λi. fromList
    (pround_evs (n2w k) hw ifds (srelabel (kv_server k)) (w1, pinit) i)) NONE))
Proof
  strip_tac >> rewrite_tac[kv_safe_l0_G] >> irule kv_safeG_prefixes >>
  rpt strip_tac >> drule LPREFIX_rounds_any >> strip_tac >>
  mp_tac (Q.SPECL [‘ifds’, ‘k’, ‘w1’, ‘hw’, ‘SUC n’, ‘evs’]
            (Q.GENL [‘ifds’, ‘k’, ‘w1’, ‘hw’, ‘n’, ‘evs’] kv_prefix_safe)) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[pevs_def] >>
  drule prun_FLAT >> disch_then (fn th => rewrite_tac[GSYM th]) >>
  first_assum ACCEPT_TAC
QED

(* The program's live interest (D26) *)
Theorem kv_run_safe_live:
  k < dimword (:64) − 1 ∧
  l0_rely w1 ∧ fds_lt w1 ∧ MEM (n2w k) (l0_used w1) ∧
  ri (n2w k) (srelabel (kv_server k)) ([], (w1, pinit), []) ∧
  (∀n. prounds_t (n2w k) hw (live [n2w k] (log_of (srelabel (kv_server k))))
         (srelabel (kv_server k)) (w1, pinit) n ≠ NONE) ⇒
  kv_safe_l0 (LFLATTEN (LGENLIST (λi. fromList
    (pround_evs (n2w k) hw (live [n2w k] (log_of (srelabel (kv_server k))))
       (srelabel (kv_server k)) (w1, pinit) i)) NONE))
Proof
  strip_tac >> irule kv_run_safe >> simp[ifds_sub_live]
QED
