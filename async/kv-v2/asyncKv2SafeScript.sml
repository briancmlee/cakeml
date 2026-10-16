(*
  HttpKvSpec2's safety (per-episode linearizability) for the key-value
  server on the version-2 handle layer (kv2_safe).

  The proof is asyncKvSafe's kv_comp_safe (the order construction) with
  episodes for connections: the store's answered queries in its order,
  then the complete requests not queried yet, episode by episode; commit
  points at round starts.  The bridge to the model, at every round
  boundary, is asyncKv2Bridge (episode j is handle hdln lfdn j of the
  model run in the renamed world); a query's handle is turned back into
  its episode by unh.

  The construction is asyncKvOrderGen's kv_safeG_rounds, shared with
  asyncKvSafe's kv_comp_safe (design/43's unification): kv_safe2 is
  kv_safeG at ep_read / ep_written (kv_safe2_G), and this file supplies
  the per-episode round facts (keys: episodes, model fds hdln lfdn j).
*)
Theory asyncKv2Safe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses ffiSpikeSocketFFI asyncM3World
  asyncM4GRounds asyncM4SockInv asyncM4SockModel asyncM4GTrans asyncRunOkGen
  EchoSpec EchoSpec2 HttpSpec HttpSpecBodies HttpKvSpec HttpKvSpec2
  asyncHttpParse asyncHttpParseH asyncHttpParseB asyncWithStore
  asyncServerWithK asyncKvHandler asyncKvModel asyncKvOrder asyncKvLabel
  asyncKvTraceLemmas socketV2FFI socketV2Fair asyncHLModel asyncHLSimWorld
  asyncHLSimTick asyncHLEpisodes asyncHLEchoSpec2 asyncProtoEof
  asyncHLEofGen asyncHLSimRunGen asyncHLSimTraceGen asyncProto2Model
  asyncKvEof asyncKv2Bridge asyncKvOrderGen llist ffi
Libs
  preamble

(* ------------------------------------------------------------------------
   Lists (as in asyncKvSafe, where these are local)
   ------------------------------------------------------------------------ *)

Theorem prefix_MAP[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ MAP f l1 ≼ MAP f l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem read_on_fd[local]:
  ∀tr. FLAT (read fd tr) ≠ [] ⇒ EXISTS (on_fd fd) tr
Proof
  Induct >> simp[read_def] >> PairCases >> simp[] >>
  every_case_tac >> rw[] >> gvs[GSYM read_def, on_fd_def]
QED

(* ------------------------------------------------------------------------
   Episodes and handles
   ------------------------------------------------------------------------ *)

(* A handle's episode *)
Definition unh_def:
  unh (lfdn:num) (fd:num) = if fd < lfdn then fd else fd − 1
End

Theorem unh_hdln[local]:
  unh lfdn (hdln lfdn j) = j
Proof
  rw[unh_def, hdln_def]
QED

Theorem hdln_11[local]:
  hdln lfdn j = hdln lfdn j' ⇔ j = j'
Proof
  rw[hdln_def] >> simp[]
QED

(* ------------------------------------------------------------------------
   kv_safe2 is asyncKvOrderGen's kv_safeG per episode
   ------------------------------------------------------------------------ *)

Theorem is_order2_ord:
  is_order2 rss order ⇔ is_ord rss order
Proof
  simp[is_order2_def, is_ord_def]
QED

Theorem precedes2_G:
  precedes2 rss order evs x y ⇔ precedesG ep_read ep_written rss order evs x y
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >> simp[precedes2_def, precedesG_def]
QED

(* MAIN: kv_safe2 is the instance per episode *)
Theorem kv_safe2_G:
  kv_safe2 io ⇔ kv_safeG ep_read ep_written io
Proof
  simp[kv_safe2_def, kv_safeG_def, is_order2_ord, precedes2_G]
QED

(* ------------------------------------------------------------------------
   The model, round by round
   ------------------------------------------------------------------------ *)

Overload KHH1 = “λlfdn s2 k. MAP sfs (ghist (interest [n2w lfdn : word64])
                                (srelabel (kv_server lfdn)) (v1of (n2w lfdn) s2) k)”
Overload KG1 = “λlfdn s2 k. kv_queries lfdn (KHH1 lfdn s2 k)”

Theorem kv2_rounds_serves[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ⇒
  MAP SND (FILTER (λq. FST q = fd) (KG1 lfdn s2 k)) ≼
    parse_all_b (FLAT (read fd (KT1 lfdn s2 k))) ∧
  written fd (KT1 lfdn s2 k) ≼ MAP print_response (fd_answers fd (KG1 lfdn s2 k))
Proof
  strip_tac >> irule kv_server_serves >>
  ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
    by simp[v1of_def] >>
  metis_tac[gen_fresh, kv_server_uses_ok]
QED

Theorem kv2_rounds_mono[local]:
  k1 ≤ k2 ⇒ KG1 lfdn s2 k1 ≼ KG1 lfdn s2 k2 ∧ KP2 lfdn s2 k1 ≼ KP2 lfdn s2 k2
Proof
  strip_tac >> conj_tac
  >- (‘KHH1 lfdn s2 k1 = TAKE k1 (KHH1 lfdn s2 k2)’
        by simp[GSYM MAP_TAKE, ghist_TAKE] >>
      pop_assum SUBST1_TAC >> simp[kv_queries_TAKE]) >>
  rw[IS_PREFIX_APPEND] >>
  qexists_tac ‘FLAT (GENLIST (λi. hround_events (n2w lfdn) (interest [n2w lfdn])
                                    (srelabel (kv_server lfdn)) s2 (i + k1)) (k2 − k1))’ >>
  ‘k2 = (k2 − k1) + k1’ by simp[] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >> simp[]
QED

Theorem kv2_rounds_handle[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ∧ MEM q (KG1 lfdn s2 k) ⇒
  ∃j. j < dimword (:64) − 1 ∧ FST q = hdln lfdn j
Proof
  strip_tac >>
  ‘MAP SND (FILTER (λq'. FST q' = FST q) (KG1 lfdn s2 k)) ≼
   parse_all_b (FLAT (read (FST q) (KT1 lfdn s2 k)))’
    by metis_tac[kv2_rounds_serves] >>
  ‘FLAT (read (FST q) (KT1 lfdn s2 k)) ≠ []’
    by (strip_tac >> fs[parse_all_b_NIL] >>
        fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  drule read_on_fd >> strip_tac >>
  irule kv2_query_handle >> simp[] >> metis_tac[]
QED

Theorem kv2_rounds_bytes_all[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  ∀k j. j < dimword (:64) − 1 ⇒
        ep_written j (KP2 lfdn s2 (SUC k)) =
          HttpSpec$bytes (FLAT (written (hdln lfdn j) (KT1 lfdn s2 k))) ∧
        ep_read j (KP2 lfdn s2 k) =
          HttpSpec$bytes (FLAT (read (hdln lfdn j) (KT1 lfdn s2 k)))
Proof
  metis_tac[kv2_rounds_bytes]
QED

(* ------------------------------------------------------------------------
   The theorem
   ------------------------------------------------------------------------ *)

(* MAIN: per-episode linearizability for the key-value server on the
   handle layer, in every fair version-2 world with one listener *)
Theorem kv2_safe:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  kv_safe2 (gtrace2 (kv_server lfdn) lfdn s2)
Proof
  strip_tac >> REWRITE_TAC[kv_safe2_G] >>
  ‘uses_ok lfdn (kv_server lfdn) ∧ srv_eof_last (kv_server lfdn)’
    by simp[kv_server_uses_ok, kv_server_eof_last] >>
  (* episodes that did anything are below dimword (:64) − 1 *)
  ‘∀k. LENGTH (accepted_fds (KP2 lfdn s2 k)) < dimword (:64) − 1’
    by (qspecl_then [‘lfdn’, ‘kv_server lfdn’, ‘s2’] mp_tac
          (Q.GENL [‘lfdn’, ‘m’, ‘s2’] accepted_bound_gen) >>
        impl_tac >- fs[] >> simp[]) >>
  ‘∀j evs. LENGTH (accepted_fds evs) ≤ j ⇒ ep_read j evs = [] ∧ ep_written j evs = []’
    by rw[ep_read_def, ep_written_def] >>
  ‘∀k q. MEM q (KG1 lfdn s2 k) ⇒ ∃j. j < dimword (:64) − 1 ∧ FST q = hdln lfdn j’
    by (rpt strip_tac >> irule kv2_rounds_handle >> simp[] >> metis_tac[]) >>
  mp_tac kv2_rounds_bytes_all >> impl_tac >- fs[] >> strip_tac >>
  qspecl_then [‘ep_read’, ‘ep_written’,
               ‘hround_events (n2w lfdn) (interest [n2w lfdn]) (srelabel (kv_server lfdn)) s2’,
               ‘KG1 lfdn s2’,
               ‘λk j. if j < dimword (:64) − 1 then FLAT (read (hdln lfdn j) (KT1 lfdn s2 k))
                      else ""’,
               ‘λk j. if j < dimword (:64) − 1 then written (hdln lfdn j) (KT1 lfdn s2 k)
                      else []’,
               ‘unh lfdn’, ‘hdln lfdn’] mp_tac
    (Q.GENL [‘RD’, ‘WR’, ‘EV’, ‘G’, ‘RS’, ‘WS’, ‘kmap’, ‘kinv’] kv_safeG_rounds) >>
  impl_tac >- (
    simp[kv_rounds_def] >> rpt conj_tac
    >- (gen_tac >> simp[hround_events_alt] >> rpt (pairarg_tac >> gvs[]))
    >- metis_tac[kv2_rounds_mono]
    >- metis_tac[ep_read_mono, ep_written_mono]
    >- simp[ep_written_def, accepted_fds_def]
    >- (rpt gen_tac >> Cases_on ‘j < dimword (:64) − 1’ >> simp[] >>
        qpat_assum ‘∀k. LENGTH (accepted_fds _) < _’ (qspec_then ‘SUC k’ assume_tac) >>
        qpat_assum ‘∀k. LENGTH (accepted_fds _) < _’ (qspec_then ‘k’ assume_tac) >>
        qpat_assum ‘∀j evs. _ ⇒ ep_read _ _ = [] ∧ _’
          (qspecl_then [‘j’, ‘KP2 lfdn s2 (SUC k)’] mp_tac) >>
        qpat_assum ‘∀j evs. _ ⇒ ep_read _ _ = [] ∧ _’
          (qspecl_then [‘j’, ‘KP2 lfdn s2 k’] mp_tac) >> fs[HttpSpecTheory.bytes_def])
    >- (rw[] >> TRY (metis_tac[kv2_rounds_serves] >> NO_TAC) >>
        ‘FILTER (λq. FST q = hdln lfdn j) (KG1 lfdn s2 k) = []’
          by (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
              qpat_x_assum ‘∀k q. MEM q (KG1 _ _ _) ⇒ ∃j. _’ drule >>
              strip_tac >> gvs[hdln_11]) >>
        simp[])
    >- simp[unh_hdln]
    >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[unh_hdln]) >>
    gen_tac >> qexists_tac ‘COUNT_LIST (dimword (:64) − 1)’ >>
    simp[all_distinct_count_list, MEM_COUNT_LIST] >> rpt strip_tac >>
    CCONTR_TAC >>
    ‘LENGTH (accepted_fds evs) ≤ LENGTH (accepted_fds (KP2 lfdn s2 k))’
      by (qpat_x_assum ‘evs ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >>
          simp[accepted_fds_APPEND]) >>
    qpat_x_assum ‘∀k. LENGTH (accepted_fds _) < _’ (qspec_then ‘k’ mp_tac) >>
    strip_tac >>
    ‘ep_read c evs = []’ suffices_by fs[] >>
    qpat_assum ‘∀j evs. _ ⇒ ep_read _ _ = [] ∧ _’ (qspecl_then [‘c’, ‘evs’] mp_tac) >>
    fs[]) >>
  simp[]
QED
