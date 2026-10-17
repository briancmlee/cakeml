(*
  P4 (design/46), HTTP: the HTTP server's raw L0 trace on the honest L1 is
  safe (http_safe_l0), from the version-2 theorem http2_safe_if, by the
  route of honestKvL0Safe (whose generic lemmas it reuses: rtm, pevs,
  upto_world, run_pair, sent_unhanded).

  hdl_v2_bytes_gen: honestKvL0Pair's hdl_v2_bytes_if for any server that
  uses only accepted fds and stops at EOF.
  http_view_safe: the per-episode transfer (simpler than KV's: no order
  across episodes).  A raw episode paired with v2 episode c read at least
  what c read at the paired instant and sent at most what c wrote then.
  http_prefix_safe: every finite prefix of the run is safe.
  http_run_safe: any loop interest under ifds_sub; http_run_safe_live: the
  program's live interest (D26).
*)
Theory honestHttpL0Safe
Ancestors
  words llist rich_list HttpSpec HttpSpecBodies HttpSpecBodies2
  asyncTranscript asyncServer asyncRunOkGen asyncM4GTrans asyncM4LiveInterest
  asyncHLModel asyncHLSimWorld asyncHLSimRunGen asyncProto asyncProtoSafe asyncProtoB
  asyncProtoViaB asyncProtoEof asyncProto2 asyncProto2Model asyncHttpServerB
  EchoSpec2 honestL1Steps honestL1PFModel honestL1PFRefine honestL1PFProg honestL1PFSpec
  honestEchoL0Spec honestEchoL0Trace honestEchoL0Run honestEchoL0Safe
  honestHttpKvL0Spec
  honestKvL0View honestKvL0Trunc honestKvL0Count honestKvL0Run honestKvL0Pair
  honestKvL0Safe
Libs
  preamble

(* ------------------------------------------------------------------------
   The HTTP server on version 2 (copies of cf-actions' asyncHttp2Safe,
   uncommitted there; remove at merge)
   ------------------------------------------------------------------------ *)

Theorem http_safe_b2_proto_copy[local]:
  http_safe_b2 files io ⇔ proto_safe2 P_b (print_response o bhandle files) io
Proof
  simp[http_safe_b2_def, brequests_def, bresponses_def, no_full_brequest_def,
       proto_safe2_def, preqs_def, presps_def, no_full_def, P_b_def]
QED

Theorem http2_safe_if_copy[local]:
  ifds_sub (n2w lfdn) ifds ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  http_safe_b2 files (gtrace2i (http_server_b files lfdn) lfdn ifds s2)
Proof
  strip_tac >> REWRITE_TAC[http_safe_b2_proto_copy, http_server_b_proto] >>
  irule proto2_safe_if >> simp[proto_ok_b]
QED

Theorem http_server_ok:
  uses_ok lfdn (http_server_b files lfdn) ∧ srv_eof_last (http_server_b files lfdn)
Proof
  simp[http_server_b_proto, uses_ok_def, proto_server_uses_accepted,
       proto_server_eof_last, proto_ok_b]
QED

Theorem http_writes_accepted:
  writes_accepted (srelabel (http_server_b files k))
Proof
  irule uses_ok_writes_accepted >> qexists_tac ‘k’ >> simp[http_server_ok]
QED

(* ------------------------------------------------------------------------
   Handle j against v2 episode j, for any server
   ------------------------------------------------------------------------ *)

(* MAIN: honestKvL0Pair's hdl_v2_bytes_if for any server that uses only
   accepted fds and stops at EOF *)
Theorem hdl_v2_bytes_gen:
  uses_ok lfdn m ∧ srv_eof_last m ∧ ifds_sub (n2w lfdn) ifds ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ j < dimword (:64) − 1 ⇒
  hwritten (hdl (n2w lfdn) j) (trans (srelabel m) (hhist (n2w lfdn) ifds (srelabel m) s2 n)) =
    ep_written j (FLAT (GENLIST (hround_events (n2w lfdn) ifds (srelabel m) s2) (SUC n))) ∧
  hread (hdl (n2w lfdn) j) (trans (srelabel m) (hhist (n2w lfdn) ifds (srelabel m) s2 n)) =
    ep_read j (FLAT (GENLIST (hround_events (n2w lfdn) ifds (srelabel m) s2) n))
Proof
  strip_tac >>
  drule_all hrun_sim_if >>
  disch_then (qspec_then ‘n’ (fn th => REWRITE_TAC [CONJUNCT1 th])) >>
  qpat_assum ‘uses_ok _ _’ (fn th => REWRITE_TAC [MATCH_MP hwritten_bytes th,
                                                  MATCH_MP hread_bytes th]) >>
  ‘∀k. ep_read j (FLAT (GENLIST (hround_events (n2w lfdn) ifds (srelabel m) s2) k)) =
         bytes_read_from (hdl (n2w lfdn) j)
           (FLAT (GENLIST (grounds_events ifds (srelabel m) (v1of (n2w lfdn) s2)) k)) ∧
       ep_written j (FLAT (GENLIST (hround_events (n2w lfdn) ifds (srelabel m) s2) k)) =
         bytes_written_to (hdl (n2w lfdn) j)
           (FLAT (GENLIST (grounds_events ifds (srelabel m) (v1of (n2w lfdn) s2)) k))’
    by (gen_tac >> irule ep_rounds_if >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  qspecl_then [‘m’, ‘lfdn’, ‘v1of (n2w lfdn) s2’, ‘hdl (n2w lfdn) j’, ‘n’, ‘ifds’]
    mp_tac (Q.GENL [‘m’, ‘lfdn’, ‘s0’, ‘c’, ‘n’, ‘ifds’] gen_rounds_bytes) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[v1of_def]]) >>
  strip_tac >> fs[HttpSpecTheory.bytes_def]
QED

(* ------------------------------------------------------------------------
   The per-episode transfer
   ------------------------------------------------------------------------ *)

Theorem bresponses_mono[local]:
  rs ≼ rs' ⇒ bresponses files rs ≼ bresponses files rs'
Proof
  rw[IS_PREFIX_APPEND, bresponses_def] >> simp[MAP_APPEND, HttpSpecTheory.bytes_def]
QED

(* MAIN: v2 safety moves to a raw trace io1 whose episodes are paired (e)
   with v2 episodes at instants tm of the v2 trace io2 *)
Theorem http_view_safe:
  (∀evs j. LPREFIX (fromList evs) io1 ∧ e j = NONE ⇒ l0_sent j evs = []) ∧
  (∀evs j c. LPREFIX (fromList evs) io1 ∧ e j = SOME c ⇒
     ep_read c (vtr (tm evs)) ≼ l0_read j evs ∧
     l0_sent j evs ≼ ep_written c (vtr (tm evs))) ∧
  (∀t. LPREFIX (fromList (vtr t)) io2) ∧
  http_safe_b2 files io2 ⇒
  http_safe_l0 files io1
Proof
  strip_tac >> rewrite_tac[http_safe_l0_def] >> rpt strip_tac >>
  Cases_on ‘e j’
  >- (‘l0_sent j evs = []’
        by (qpat_x_assum ‘∀evs j. _ ∧ e j = NONE ⇒ _’ irule >> conj_tac >> first_assum ACCEPT_TAC) >>
      pop_assum SUBST1_TAC >> simp[]) >>
  rename1 ‘e j = SOME c’ >>
  qpat_x_assum ‘∀evs j c. _ ∧ e j = SOME c ⇒ _’ (qspecl_then [‘evs’, ‘j’, ‘c’] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspec_then ‘ep_read c (vtr (tm evs))’ strip_assume_tac brequests_split >>
  rename1 ‘ep_read c _ = brequests rs2 ++ rest2’ >>
  ‘ep_written c (vtr (tm evs)) ≼ bresponses files rs2’
    by (qpat_x_assum ‘http_safe_b2 _ _’ (mp_tac o REWRITE_RULE [http_safe_b2_def]) >>
        disch_then irule >> rpt conj_tac
        >- (qexists_tac ‘rest2’ >> conj_tac >> first_assum ACCEPT_TAC)
        >- first_assum ACCEPT_TAC >>
        first_assum (qspec_then ‘tm evs’ ACCEPT_TAC)) >>
  ‘rs2 ≼ rs’
    by (irule brequests_prefix_mono >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexistsl [‘rest2’, ‘rest’] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_x_assum ‘ep_read c _ = _’ (SUBST1_TAC o SYM) >>
        qpat_x_assum ‘l0_read j evs = _’ (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘ep_written c (vtr (tm evs))’ >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘bresponses files rs2’ >>
  conj_tac >- (irule bresponses_mono >> first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   The HTTP server
   ------------------------------------------------------------------------ *)

(* MAIN: every finite prefix of the run is safe *)
Theorem http_prefix_safe:
  ifds_sub (n2w k) ifds ∧ k < dimword (:64) − 1 ∧
  l0_rely w1 ∧ fds_lt w1 ∧ MEM (n2w k) (l0_used w1) ∧
  ri (n2w k) (srelabel (http_server_b files k)) ([], (w1, pinit), []) ∧
  (∀n. prounds_t (n2w k) hw ifds (srelabel (http_server_b files k)) (w1, pinit) n ≠ NONE) ∧
  evs ≼ pevs (n2w k) hw ifds (srelabel (http_server_b files k)) (w1, pinit) n ⇒
  http_safe_l0 files (fromList evs)
Proof
  strip_tac >>
  qabbrev_tac ‘m = srelabel (http_server_b files k)’ >>
  qabbrev_tac ‘E = pevs (n2w k) hw ifds m (w1, pinit)’ >>
  ‘writes_accepted m’ by simp[Abbr ‘m’, http_writes_accepted] >>
  ‘uses_ok k (http_server_b files k) ∧ srv_eof_last (http_server_b files k)’
    by simp[http_server_ok] >>
  ‘∀i j. i ≤ j ⇒ E i ≼ E j’
    by (simp[Abbr ‘E’] >> match_mp_tac pevs_mono >> first_assum ACCEPT_TAC) >>
  ‘E 0 = []’ by simp[Abbr ‘E’, pevs_def] >>
  Cases_on ‘rtm E evs’
  >- (‘evs = []’
        by (qpat_x_assum ‘evs ≼ E n’ (mp_tac o CONJUNCT1 o MATCH_MP rtm_spec) >>
            qpat_x_assum ‘rtm E evs = 0’ SUBST1_TAC >>
            qpat_x_assum ‘E 0 = []’ SUBST1_TAC >> simp[]) >>
      qpat_x_assum ‘evs = []’ SUBST1_TAC >>
      simp[http_safe_l0_def, LPREFIX_fromList, from_toList, l0_sent_def, l0_accepted_def]) >>
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
  qspecl_then [‘fromList evs’, ‘λj. if j < dimword (:64) − 1 then SOME j else NONE’,
               ‘λt. FLAT (GENLIST (hround_events (n2w k) ifds m s2) t)’, ‘rtm E’,
               ‘gtrace2i (http_server_b files k) k ifds s2’, ‘files’]
    mp_tac (Q.GENL [‘io1’, ‘e’, ‘vtr’, ‘tm’, ‘io2’, ‘files’] http_view_safe) >>
  disch_then match_mp_tac >> BETA_TAC >>
  rpt conj_tac
  >- (* raw episodes past the handles sent nothing *)
     (simp[LPREFIX_fromList, from_toList] >> rpt strip_tac >>
      qspecl_then [‘m’, ‘n2w k’, ‘(w1, pinit)’, ‘hw’, ‘ifds’, ‘evs'’, ‘n’, ‘j’] mp_tac
        (Q.GENL [‘m’, ‘lfd’, ‘ws0’, ‘hw’, ‘ifds’, ‘pre’, ‘n’, ‘j’] sent_unhanded) >>
      disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_x_assum ‘¬(j < _)’ mp_tac >> simp[]) >>
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
      ‘srelabel (http_server_b files k) = m’ by simp[Abbr ‘m’] >>
      qspecl_then [‘http_server_b files k’, ‘k’, ‘ifds’, ‘s2’, ‘j’, ‘SUC i’] mp_tac
        (Q.GENL [‘m’, ‘lfdn’, ‘ifds’, ‘s2’, ‘j’, ‘n’] hdl_v2_bytes_gen) >>
      qspecl_then [‘http_server_b files k’, ‘k’, ‘ifds’, ‘s2’, ‘j’, ‘i’] mp_tac
        (Q.GENL [‘m’, ‘lfdn’, ‘ifds’, ‘s2’, ‘j’, ‘n’] hdl_v2_bytes_gen) >>
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
  >- (* the v2 trace's instants are its prefixes *)
     (gen_tac >> simp[rounds_LPREFIX]) >>
  (* the v2 safety *)
  irule http2_safe_if_copy >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* MAIN: the run of the HTTP server past the listen is safe, for any loop
   interest under ifds_sub *)
Theorem http_run_safe:
  ifds_sub (n2w k) ifds ∧ k < dimword (:64) − 1 ∧
  l0_rely w1 ∧ fds_lt w1 ∧ MEM (n2w k) (l0_used w1) ∧
  ri (n2w k) (srelabel (http_server_b files k)) ([], (w1, pinit), []) ∧
  (∀n. prounds_t (n2w k) hw ifds (srelabel (http_server_b files k)) (w1, pinit) n ≠ NONE) ⇒
  http_safe_l0 files (LFLATTEN (LGENLIST (λi. fromList
    (pround_evs (n2w k) hw ifds (srelabel (http_server_b files k)) (w1, pinit) i)) NONE))
Proof
  strip_tac >> simp_tac std_ss [http_safe_l0_def] >> rpt strip_tac >>
  drule LPREFIX_rounds_any >> strip_tac >>
  mp_tac (Q.SPECL [‘ifds’, ‘k’, ‘w1’, ‘hw’, ‘files’, ‘SUC n’, ‘evs’]
            (Q.GENL [‘ifds’, ‘k’, ‘w1’, ‘hw’, ‘files’, ‘n’, ‘evs’] http_prefix_safe)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[pevs_def] >>
      drule prun_FLAT >> disch_then (fn th => rewrite_tac[GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  rewrite_tac[http_safe_l0_def] >> disch_then irule >>
  simp[LPREFIX_fromList, from_toList] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The program's live interest (D26) *)
Theorem http_run_safe_live:
  k < dimword (:64) − 1 ∧
  l0_rely w1 ∧ fds_lt w1 ∧ MEM (n2w k) (l0_used w1) ∧
  ri (n2w k) (srelabel (http_server_b files k)) ([], (w1, pinit), []) ∧
  (∀n. prounds_t (n2w k) hw (live [n2w k] (log_of (srelabel (http_server_b files k))))
         (srelabel (http_server_b files k)) (w1, pinit) n ≠ NONE) ⇒
  http_safe_l0 files (LFLATTEN (LGENLIST (λi. fromList
    (pround_evs (n2w k) hw (live [n2w k] (log_of (srelabel (http_server_b files k))))
       (srelabel (http_server_b files k)) (w1, pinit) i)) NONE))
Proof
  strip_tac >> irule http_run_safe >> simp[ifds_sub_live]
QED
