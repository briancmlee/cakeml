(*
  KvSpec from its peer form, for fd-disciplined programs: the
  useful direction of kv_peer_equiv, restricted as v1_instance_disc is.
  An instance of peerV1Disc.  Liveness: v1_live, for the
  as-many-replies-as-requests relation.  Safety: kv_safe is about all
  connections at once, so it is carried over from the renamed trace R
  (episode j on fd n2w j) by renaming its order back: prefix by prefix,
  fd c_j's bytes are fd n2w j's in R (kv_bytes_prefix), and other fds have
  none in R (kv_ren_none).
*)
Theory peerV1Kv
Ancestors
  llist rich_list ffi semantics EchoSpec HttpGetSpec HttpSpec KvSpec
  peerSpecForms peerInstances peerServers peerBufferKv
  peerV1Run peerV1Inst peerV1Proj peerV1Disc
Libs
  preamble

(* ------------------------------------------------------------------------
   Bytes of a renamed prefix
   ------------------------------------------------------------------------ *)

Theorem opened_fds_prefix[local]:
  evs1 ≼ evs ⇒ opened_fds evs1 ≼ opened_fds evs
Proof
  rw[IS_PREFIX_APPEND] >> simp[opened_fds_def]
QED

Theorem LPREFIX_prefix[local]:
  LPREFIX (fromList evs) io ∧ evs1 ≼ evs ⇒ LPREFIX (fromList evs1) io
Proof
  strip_tac >> irule LPREFIX_TRANS >> first_assum (irule_at Any) >>
  simp[LPREFIX_fromList, from_toList]
QED

Theorem v1_run_trace_kv[local]:
  v1_tr lfd ll0 s1 s2 prog io ∧ LPREFIX (fromList evs) io ⇒
  EVERY v1_event evs ∧
  (∀pre ev post c. evs = pre ++ ev :: post ∧
                   (event_written c ev ≠ [] ∨ event_read c ev ≠ []) ⇒
                   MEM c (opened_fds pre)) ∧
  ALL_DISTINCT (opened_fds evs) ∧ LENGTH (opened_fds evs) ≤ dimword (:64)
Proof
  rw[v1_tr_def] >> drule_all v1_trace >> strip_tac >>
  gvs[ALL_DISTINCT_TAKE, LENGTH_TAKE]
QED

(* MAIN: at every prefix, the j-th opened fd's bytes are fd n2w j's in the
   renamed prefix *)
Theorem kv_bytes_prefix:
  v1_tr lfd ll0 s1 s2 prog io ∧ LPREFIX (fromList evs) io ∧ evs1 ≼ evs ∧
  j < LENGTH (opened_fds evs) ⇒
  bytes_written_to (n2w j) (ren_evs 0 [] evs1) = bytes_written_to (EL j (opened_fds evs)) evs1 ∧
  bytes_read_from (n2w j) (ren_evs 0 [] evs1) = bytes_read_from (EL j (opened_fds evs)) evs1
Proof
  strip_tac >>
  ‘LPREFIX (fromList evs1) io’ by metis_tac[LPREFIX_prefix] >>
  drule_all v1_run_trace_kv >> strip_tac >>
  qpat_x_assum ‘LPREFIX (fromList evs) io’ assume_tac >>
  drule_all v1_run_trace_kv >> strip_tac >>
  ‘opened_fds evs1 ≼ opened_fds evs’ by simp[opened_fds_prefix] >>
  Cases_on ‘j < LENGTH (opened_fds evs1)’
  >- (‘EL j (opened_fds evs1) = EL j (opened_fds evs)’ by metis_tac[is_prefix_el] >>
      pop_assum (SUBST1_TAC o SYM) >> simp[bytes_written_to_def, bytes_read_from_def] >>
      qabbrev_tac ‘c = EL j (opened_fds evs1)’ >>
      ‘(∀pre ev post. evs1 = pre ++ ev::post ∧ event_written c ev ≠ [] ⇒ MEM c (opened_fds pre)) ∧
       (∀pre ev post. evs1 = pre ++ ev::post ∧ event_read c ev ≠ [] ⇒ MEM c (opened_fds pre))’
        by metis_tac[] >>
      conj_tac
      >- (mp_tac (Q.INST [‘pr’ |-> ‘event_written’, ‘evs’ |-> ‘evs1’] proj_v1) >>
          impl_tac >- fs[proj_ok_written, Abbr ‘c’] >> simp[])
      >> mp_tac (Q.INST [‘pr’ |-> ‘event_read’, ‘evs’ |-> ‘evs1’] proj_v1) >>
      impl_tac >- fs[proj_ok_read, Abbr ‘c’] >> simp[]) >>
  ‘¬MEM (EL j (opened_fds evs)) (opened_fds evs1)’
    by (strip_tac >> fs[MEM_EL, IS_PREFIX_APPEND] >> gvs[] >>
        rename1 ‘EL m (opened_fds evs1)’ >>
        ‘EL m (opened_fds evs1 ++ l') = EL m (opened_fds evs1)’ by simp[EL_APPEND1] >>
        ‘j = m’ by (qspecl_then [‘opened_fds evs1 ++ l'’, ‘j’, ‘m’] mp_tac ALL_DISTINCT_EL_IMP >>
                    simp[]) >>
        fs[]) >>
  ‘j < dimword (:64)’ by decide_tac >>
  simp[bytes_written_to_def, bytes_read_from_def] >> rpt conj_tac
  >- (mp_tac (Q.INST [‘pr’ |-> ‘event_written’, ‘evs’ |-> ‘evs1’, ‘k’ |-> ‘0’, ‘opn’ |-> ‘[]’]
                (SPEC_ALL proj_ren_beyond)) >> simp[proj_ok_written] >> strip_tac >>
      irule proj_unopened >> simp[] >> metis_tac[])
  >> mp_tac (Q.INST [‘pr’ |-> ‘event_read’, ‘evs’ |-> ‘evs1’, ‘k’ |-> ‘0’, ‘opn’ |-> ‘[]’]
               (SPEC_ALL proj_ren_beyond)) >> simp[proj_ok_read] >> strip_tac >>
  irule proj_unopened >> simp[] >> metis_tac[]
QED

(* The same, for any fd of an episode *)
Theorem kv_bytes_fd:
  v1_tr lfd ll0 s1 s2 prog io ∧ LPREFIX (fromList evs) io ∧ evs1 ≼ evs ∧
  w2n d < LENGTH (opened_fds evs) ⇒
  bytes_written_to d (ren_evs 0 [] evs1) = bytes_written_to (EL (w2n d) (opened_fds evs)) evs1 ∧
  bytes_read_from d (ren_evs 0 [] evs1) = bytes_read_from (EL (w2n d) (opened_fds evs)) evs1
Proof
  strip_tac >> drule_all (Q.INST [‘j’ |-> ‘w2n (d:word64)’] kv_bytes_prefix) >> simp[]
QED

(* Other fds have no bytes in the renamed trace *)
Theorem kv_ren_none:
  v1_tr lfd ll0 s1 s2 prog io ∧ LPREFIX (fromList evs) io ∧
  LENGTH (opened_fds evs) ≤ w2n d ⇒
  bytes_written_to d (ren_evs 0 [] evs) = [] ∧ bytes_read_from d (ren_evs 0 [] evs) = []
Proof
  strip_tac >> drule_all v1_run_trace_kv >> strip_tac >>
  ‘w2n d < dimword (:64)’ by simp[w2n_lt] >>
  simp[bytes_written_to_def, bytes_read_from_def] >> conj_tac
  >- (mp_tac (Q.INST [‘pr’ |-> ‘event_written’, ‘j’ |-> ‘w2n (d:word64)’, ‘k’ |-> ‘0’, ‘opn’ |-> ‘[]’]
                (SPEC_ALL proj_ren_beyond)) >> simp[proj_ok_written])
  >> mp_tac (Q.INST [‘pr’ |-> ‘event_read’, ‘j’ |-> ‘w2n (d:word64)’, ‘k’ |-> ‘0’, ‘opn’ |-> ‘[]’]
               (SPEC_ALL proj_ren_beyond)) >> simp[proj_ok_read]
QED

(* ------------------------------------------------------------------------
   Renaming an order back
   ------------------------------------------------------------------------ *)

(* The replies, with an order renamed injectively on its connections *)
Theorem replies_rename:
  (∀x. MEM x order' ⇒ rss (g (FST x)) = rss' (FST x)) ∧
  (∀x. MEM x order' ⇒ (g (FST x) = g d ⇔ FST x = d)) ⇒
  replies rss (MAP (λ(d, i). (g d, i)) order') (g d) = replies rss' order' d
Proof
  rw[replies_def] >>
  ‘MAP (λ(d,i). EL i (rss d)) (MAP (λ(d,i). (g d,i)) order') =
   MAP (λ(d,i). EL i (rss' d)) order'’
    by (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >> simp[FORALL_PROD] >>
        rw[] >> res_tac >> fs[]) >>
  simp[] >>
  qabbrev_tac ‘kl = kv_run (λk. NONE) (MAP (λ(d,i). EL i (rss' d)) order')’ >>
  ‘LENGTH order' = LENGTH kl’ by simp[Abbr ‘kl’] >>
  simp[ZIP_MAP, FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
  REWRITE_TAC[ETA_AX] >> AP_TERM_TAC >> simp[FILTER_EQ, MEM_ZIP, PULL_EXISTS] >> rw[] >>
  ‘MEM (EL n order') order'’ by simp[EL_MEM] >>
  Cases_on ‘EL n order'’ >> simp[] >>
  qpat_x_assum ‘∀x. MEM x order' ⇒ (g _ = g d ⇔ _)’ drule >> simp[]
QED

Theorem no_full_brequest_nil:
  no_full_brequest []
Proof
  rw[no_full_brequest_def] >> strip_tac >> fs[brequests_nil]
QED

(* MAIN: kv_safe of the renamed prefix gives kv_safe's clause at the prefix *)
Theorem kv_safe_of_ren:
  v1_run_ok lfd a sk prog io ∧ LPREFIX (fromList evs) io ∧
  kv_safe (fromList (ren_evs 0 [] evs)) ∧
  (∀c. EVERY valid_brequest (rss c) ∧ no_full_brequest (rests c) ∧
       bytes_read_from c evs = brequests (rss c) ++ rests c) ⇒
  ∃order.
    is_order rss order ∧
    (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
           precedes rss order evs x y ⇒ earlier order x y) ∧
    ∀c. bytes_written_to c evs ≼ reply_bytes (replies rss order c)
Proof
  strip_tac >>
  ‘v1_tr lfd sk.sched sk (v2of1 lfd sk) prog io’ by metis_tac[v1_run_ok_tr] >>
  drule_all v1_run_trace_kv >> strip_tac >>
  ‘∀c. ¬MEM c (opened_fds evs) ⇒ bytes_written_to c evs = [] ∧ bytes_read_from c evs = []’
    by metis_tac[v1_bytes] >>
  qabbrev_tac ‘os = opened_fds evs’ >>
  qabbrev_tac ‘rtr = ren_evs 0 [] evs’ >>
  ‘∀evs1 j. evs1 ≼ evs ∧ j < LENGTH os ⇒
     bytes_written_to (n2w j) (ren_evs 0 [] evs1) = bytes_written_to (EL j os) evs1 ∧
     bytes_read_from (n2w j) (ren_evs 0 [] evs1) = bytes_read_from (EL j os) evs1’
    by (rpt gen_tac >> strip_tac >> simp[Abbr ‘os’] >> irule kv_bytes_prefix >>
        simp[] >> metis_tac[]) >>
  qabbrev_tac ‘g = λd:word64. EL (w2n d) os’ >>
  qabbrev_tac ‘rss' = λd:word64. if w2n d < LENGTH os then rss (g d) else []’ >>
  qabbrev_tac ‘rests' = λd:word64. if w2n d < LENGTH os then rests (g d) else []’ >>
  (* the renamed trace's reads *)
  ‘∀d. bytes_read_from d rtr = brequests (rss' d) ++ rests' d’
    by (rw[Abbr ‘rss'’, Abbr ‘rests'’, Abbr ‘g’]
        >- (rename1 ‘w2n dd < LENGTH os’ >>
            simp[Abbr ‘rtr’] >>
            ‘bytes_read_from (n2w (w2n dd)) (ren_evs 0 [] evs) =
             bytes_read_from (EL (w2n dd) os) evs’ by metis_tac[IS_PREFIX_REFL] >>
            fs[])
        >> fs[NOT_LESS] >> simp[Abbr ‘rtr’] >>
        qpat_x_assum ‘Abbrev (os = _)’ (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
        gvs[] >> drule_all kv_ren_none >> simp[brequests_def, HttpGetSpecTheory.bytes_def]) >>
  qpat_x_assum ‘KvSpec$kv_safe _’ (mp_tac o REWRITE_RULE[kv_safe_def]) >>
  disch_then (qspecl_then [‘rtr’, ‘rss'’, ‘rests'’] mp_tac) >>
  impl_tac
  >- (simp[] >> rw[Abbr ‘rss'’, Abbr ‘rests'’, no_full_brequest_nil]) >>
  strip_tac >> rename1 ‘is_order rss' order'’ >>
  (* the order's connections are episodes *)
  ‘∀x. MEM x order' ⇒ w2n (FST x) < LENGTH os’
    by (rpt strip_tac >> Cases_on ‘x’ >> drule_all is_order_MEM >>
        rw[Abbr ‘rss'’] >> CCONTR_TAC >> fs[]) >>
  ‘∀x d. MEM x order' ∧ w2n d < LENGTH os ⇒ (g (FST x) = g d ⇔ FST x = d)’
    by (rw[Abbr ‘g’] >> eq_tac >> rw[] >>
        ‘w2n (FST x) = w2n d’ by metis_tac[ALL_DISTINCT_EL_IMP] >> fs[]) >>
  ‘∀x. MEM x order' ⇒ rss (g (FST x)) = rss' (FST x)’ by rw[Abbr ‘rss'’] >>
  qexists_tac ‘MAP (λ(d, i). (g d, i)) order'’ >>
  ‘∀j. j < LENGTH os ⇒
       replies rss (MAP (λ(d, i). (g d, i)) order') (EL j os) = replies rss' order' (n2w j)’
    by (rpt strip_tac >>
        ‘j < dimword (:64)’ by decide_tac >>
        ‘w2n (n2w j : word64) = j’ by simp[] >>
        ‘EL j os = g (n2w j : word64)’ by simp[Abbr ‘g’] >>
        pop_assum SUBST1_TAC >>
        irule replies_rename >> metis_tac[]) >>
  rpt conj_tac
  >- ((* an order of rss *)
      rw[is_order_def] >> Cases_on ‘MEM c os’
      >- (‘∃j. j < LENGTH os ∧ c = EL j os’ by metis_tac[MEM_EL] >> gvs[] >>
          qpat_x_assum ‘is_order rss' _’
            (mp_tac o Q.SPEC ‘n2w j : word64’ o REWRITE_RULE[is_order_def]) >>
          ‘j < dimword (:64)’ by fs[] >>
          simp[Abbr ‘rss'’, Abbr ‘g’] >> disch_then (SUBST1_TAC o SYM) >>
          simp[FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
          ‘(λ(p1:word64, p2:num). p2) = SND’ by simp[FUN_EQ_THM, FORALL_PROD] >>
          pop_assum SUBST1_TAC >>
          AP_TERM_TAC >> simp[FILTER_EQ, FORALL_PROD] >> rpt strip_tac >>
          qpat_x_assum ‘∀x. MEM x order' ⇒ w2n (FST x) < _’
            (qspec_then ‘(p_1, p_2)’ mp_tac) >> simp[] >> strip_tac >>
          eq_tac >> rw[] >> simp[] >>
          ‘w2n p_1 = j’ by metis_tac[ALL_DISTINCT_EL_IMP] >>
          metis_tac[n2w_w2n]) >>
      ‘rss c = []’ by metis_tac[brequests_nil, APPEND_eq_NIL] >>
      simp[COUNT_LIST_def, FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD,
           FILTER_MAP, combinTheory.o_DEF] >>
      rpt strip_tac >>
      ‘w2n p_1 < LENGTH os’
        by (qpat_x_assum ‘∀x. MEM x order' ⇒ w2n (FST x) < _’
              (qspec_then ‘(p_1, p_2)’ mp_tac) >> simp[]) >>
      qpat_x_assum ‘Abbrev (g = _)’ (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      gvs[] >> metis_tac[EL_MEM])
  >- ((* real time *)
      simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
      rename1 ‘precedes _ _ _ (g da, ia) (g db, ib)’ >>
      ‘da ≠ db’ by (strip_tac >> fs[]) >>
      ‘earlier order' (da, ia) (db, ib)’ suffices_by
        (strip_tac >>
         qpat_x_assum ‘earlier order' _ _’ (strip_assume_tac o REWRITE_RULE[earlier_def]) >>
         simp[earlier_def] >>
         qexistsl_tac [‘MAP (λ(d,i). (g d,i)) l1’, ‘MAP (λ(d,i). (g d,i)) l2’,
                       ‘MAP (λ(d,i). (g d,i)) l3’] >> simp[]) >>
      ‘MEM (da, ia) order' ∧ MEM (db, ib) order'’ by fs[] >>
      ‘w2n da < LENGTH os ∧ w2n db < LENGTH os’ by metis_tac[FST] >>
      qpat_x_assum ‘∀x y. MEM x order' ∧ _ ⇒ earlier _ _ _’ irule >> simp[] >>
      fs[precedes_def] >> qexists_tac ‘ren_evs 0 [] evs1’ >>
      ‘∀d. w2n d < LENGTH os ⇒
           bytes_written_to d (ren_evs 0 [] evs1) = bytes_written_to (g d) evs1 ∧
           bytes_read_from d (ren_evs 0 [] evs1) = bytes_read_from (g d) evs1’
        by (rpt gen_tac >> strip_tac >> simp[Abbr ‘g’, Abbr ‘os’] >>
            irule kv_bytes_fd >> simp[] >> metis_tac[]) >>
      ‘replies rss (MAP (λ(d,i). (g d,i)) order') (g da) = replies rss' order' da’
        by (first_assum (mp_tac o SPEC “w2n (da : word64)”) >>
            impl_tac >- fs[] >>
            qpat_assum ‘Abbrev (g = _)’ (fn th => REWRITE_TAC[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
            simp[wordsTheory.n2w_w2n]) >>
      ‘rss' db = rss (g db)’ by simp[Abbr ‘rss'’] >>
      simp[Abbr ‘rtr’, ren_evs_prefix] >> fs[]) >>
  (* what is written *)
  rw[] >> Cases_on ‘MEM c os’ >- (
    ‘∃j. j < LENGTH os ∧ c = EL j os’ by metis_tac[MEM_EL] >> gvs[] >>
    ‘bytes_written_to (n2w j) rtr = bytes_written_to (EL j os) evs’
      by (simp[Abbr ‘rtr’] >> metis_tac[IS_PREFIX_REFL]) >>
    metis_tac[]) >>
  simp[]
QED

(* MAIN: a disciplined program meeting the peer key-value spec with
   version 1's calls meets KvSpec in every version-1 server world that
   connects at most M clients *)
Theorem kv_spec_of_peer_disc:
  v1_disciplined lfd prog ∧
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
    ep_kv_guar prog ∧
  server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
       kv_safe io ∧ kv_live sk io
Proof
  strip_tac >> drule_all v1_endpoint_run >> strip_tac >>
  qexists_tac ‘io’ >> fs[ep_kv_guar_def] >> conj_tac
  >- (rw[kv_safe_def] >> irule kv_safe_of_ren >> simp[] >>
      fs[sym_safe_def, always_def] >> metis_tac[]) >>
  rw[kv_live_def] >>
  mp_tac (BETA_RULE (Q.INST [‘P’ |-> ‘λx y. ∀rs. EVERY valid_brequest rs ∧ brequests rs ≼ x ⇒
                                  ∃ans. LENGTH ans = LENGTH rs ∧ reply_bytes ans ≼ y’] v1_live)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
      >- (rpt strip_tac >>
          qpat_x_assum ‘∀rs. _ ⇒ ∃ans. _ ∧ reply_bytes ans ≼ y’ (qspec_then ‘rs'’ mp_tac) >>
          impl_tac >- (simp[] >> irule IS_PREFIX_TRANS >> qexists_tac ‘x’ >> simp[]) >>
          strip_tac >> qexists_tac ‘ans’ >> simp[] >> irule IS_PREFIX_TRANS >>
          qexists_tac ‘y’ >> simp[]) >>
      rpt strip_tac >> fs[brequests_nil] >> TRY (qexists_tac ‘[]’) >>
      simp[reply_bytes_def, HttpGetSpecTheory.bytes_def]) >>
  disch_then (qspecl_then [‘c’, ‘n’] strip_assume_tac) >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED
