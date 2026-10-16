(*
  HttpKvSpec to its endpoint form, for fd-disciplined programs: the ⇒
  direction of the disciplined kv_sym_equiv (endpointV1Kv has ⇐).
  An instance of endpointV1ConvRun via endpointV1ReqConv: liveness is per
  request list, for Rel rs y = "as many replies as requests are a prefix
  of y".  Safety: kv_safe is about all connections at once, so it is
  carried over to the renamed trace R (episode j on fd n2w j) by renaming
  the run's order: fd c_j is fd n2w j of R (endpointV1Kv's kv_bytes_prefix,
  kv_ren_none, replies_rename, in the other direction: kv_sym_safe).
*)
Theory endpointV1KvConv
Ancestors
  llist rich_list ffi semantics EchoSpec HttpSpec HttpSpecBodies HttpKvSpec EchoSpec2
  endpointSpecForms endpointInstances endpointServers endpointBufferKv
  endpointBufferHttp endpointV1Sim endpointV1Run endpointV1Inst endpointV1Proj
  endpointV1Conv endpointV1Kv endpointV1ConvRun endpointV1ReqConv
Libs
  preamble

(* HttpKvSpec, over the version-1 server worlds connecting at most M
   clients (endpointV1Kv's kv_spec_of_endpoint_disc concludes this) *)
Definition kv_spec_le_def:
  kv_spec_le lfd prog ⇔
    ∀sk M. server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
           ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
                kv_safe io ∧ kv_live sk io
End

(* ------------------------------------------------------------------------
   Safety, with the order renamed
   ------------------------------------------------------------------------ *)

Theorem LPREFIX_prefix[local]:
  LPREFIX (fromList evs) io ∧ evs1 ≼ evs ⇒ LPREFIX (fromList evs1) io
Proof
  strip_tac >> irule LPREFIX_TRANS >> first_assum (irule_at Any) >>
  simp[LPREFIX_fromList, from_toList]
QED

(* MAIN: kv_safe of a disciplined run carries over to its renamed trace *)
Theorem kv_sym_safe:
  v1_tr lfd ll0 s1 s2 prog io ∧ kv_safe io ⇒ sym_safe kv_safe io
Proof
  rw[sym_safe_def, always_def] >> REWRITE_TAC[kv_safe_def] >> rpt strip_tac >>
  rename1 ‘LPREFIX (fromList evs') (fromList (ren_evs 0 [] evs))’ >>
  rename1 ‘bytes_read_from _ evs' = brequests (rss' _) ++ rests' _’ >>
  ‘evs' ≼ ren_evs 0 [] evs’ by fs[LPREFIX_fromList, from_toList] >>
  drule ren_evs_prefix_inv >> strip_tac >> gvs[] >>
  rename1 ‘E ≼ evs’ >>
  ‘LPREFIX (fromList E) io’ by metis_tac[LPREFIX_prefix] >>
  ‘EVERY v1_event E ∧
   (∀pre ev post c. E = pre ++ ev :: post ∧ (event_written c ev ≠ [] ∨ event_read c ev ≠ []) ⇒
                    MEM c (opened_fds pre)) ∧
   ALL_DISTINCT (opened_fds E) ∧ LENGTH (opened_fds E) ≤ dimword (:64)’
    by (fs[v1_tr_def] >> drule_all v1_trace >> strip_tac >>
        gvs[ALL_DISTINCT_TAKE, LENGTH_TAKE]) >>
  qabbrev_tac ‘os = opened_fds E’ >>
  (* the fds of the run and of the renamed trace *)
  qabbrev_tac ‘h = λc:word64. (n2w (findi c os) : word64)’ >>
  ‘∀c. MEM c os ⇒ findi c os < LENGTH os ∧ EL (findi c os) os = c ∧
                  w2n (h c) = findi c os’
    by (rpt gen_tac >> strip_tac >> simp[Abbr ‘h’, MEM_findi, EL_findi] >>
        ‘findi c os < LENGTH os’ by simp[MEM_findi] >> fs[] >> decide_tac) >>
  ‘∀c c'. MEM c os ∧ MEM c' os ⇒ (h c = h c' ⇔ c = c')’
    by (rpt strip_tac >> eq_tac >> rw[] >> metis_tac[]) >>
  ‘∀c. MEM c os ⇒
       bytes_written_to (h c) (ren_evs 0 [] E) = bytes_written_to c E ∧
       bytes_read_from (h c) (ren_evs 0 [] E) = bytes_read_from c E’
    by (rpt gen_tac >> strip_tac >>
        ‘h c = n2w (findi c os)’ by simp[Abbr ‘h’] >> pop_assum SUBST1_TAC >>
        ‘EL (findi c os) os = c ∧ findi c os < LENGTH os’ by metis_tac[] >>
        mp_tac (Q.INST [‘j’ |-> ‘findi (c:word64) (os:word64 list)’, ‘evs’ |-> ‘E:io_event list’,
                        ‘evs1’ |-> ‘E:io_event list’] kv_bytes_prefix) >>
        impl_tac >- fs[Abbr ‘os’] >>
        qpat_x_assum ‘Abbrev (os = _)’
          (fn th => REWRITE_TAC[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
        metis_tac[]) >>
  ‘∀d. LENGTH os ≤ w2n d ⇒
       bytes_written_to d (ren_evs 0 [] E) = [] ∧ bytes_read_from d (ren_evs 0 [] E) = []’
    by (rpt gen_tac >> strip_tac >> irule kv_ren_none >> simp[] >> metis_tac[]) >>
  ‘∀c. ¬MEM c os ⇒ bytes_written_to c E = [] ∧ bytes_read_from c E = []’
    by (rpt gen_tac >> strip_tac >> simp[bytes_written_to_def, bytes_read_from_def] >>
        conj_tac >> irule proj_unopened >> simp[] >> metis_tac[]) >>
  (* the run's requests *)
  qabbrev_tac ‘rss = λc. if MEM c os then rss' (h c) else []’ >>
  qabbrev_tac ‘rests = λc. if MEM c os then rests' (h c) else []’ >>
  qpat_x_assum ‘HttpKvSpec$kv_safe io’ (mp_tac o REWRITE_RULE[kv_safe_def]) >>
  disch_then (qspecl_then [‘E’, ‘rss’, ‘rests’] mp_tac) >>
  impl_tac
  >- (simp[] >> gen_tac >> Cases_on ‘MEM c os’ >> simp[Abbr ‘rss’, Abbr ‘rests’]
      >- metis_tac[] >>
      simp[no_full_brequest_nil, brequests_def, HttpSpecTheory.bytes_def]) >>
  strip_tac >>
  ‘∀x. MEM x order ⇒ MEM (FST x) os’
    by (rpt strip_tac >> Cases_on ‘x’ >> drule_all is_order_MEM >>
        rw[Abbr ‘rss’] >> CCONTR_TAC >> fs[]) >>
  ‘∀x. MEM x order ⇒ rss' (h (FST x)) = rss (FST x)’ by rw[Abbr ‘rss’] >>
  qexists_tac ‘MAP (λ(c, i). (h c, i)) order’ >>
  ‘∀c. MEM c os ⇒ replies rss' (MAP (λ(c, i). (h c, i)) order) (h c) = replies rss order c’
    by (rpt strip_tac >> irule replies_rename >> metis_tac[]) >>
  (* the renamed trace's fds are the run's, renamed *)
  ‘∀d. w2n d < LENGTH os ⇒ MEM (EL (w2n d) os) os ∧ h (EL (w2n d) os) = d’
    by (rpt gen_tac >> strip_tac >> simp[EL_MEM] >>
        ‘ALL_DISTINCT os’ by simp[Abbr ‘os’] >>
        simp[Abbr ‘h’, findi_EL]) >>
  rpt conj_tac
  >- ((* an order of rss' *)
      rw[is_order_def] >> rename1 ‘FST _ = d’ >>
      reverse (Cases_on ‘w2n d < LENGTH os’)
      >- (‘rss' d = []’
            by (‘bytes_read_from d (ren_evs 0 [] E) = []’ by fs[NOT_LESS] >>
                qpat_x_assum ‘∀c. EVERY valid_brequest (rss' c) ∧ _’
                  (qspec_then ‘d’ strip_assume_tac) >>
                rfs[brequests_nil]) >>
          simp[COUNT_LIST_def, FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
          rpt strip_tac >> rename1 ‘MEM (cc, ii) order’ >>
          ‘MEM cc os’ by metis_tac[FST] >>
          ‘w2n d = findi cc os ∧ findi cc os < LENGTH os’ by metis_tac[] >>
          fs[]) >>
      ‘MEM (EL (w2n d) os) os ∧ h (EL (w2n d) os) = d’ by metis_tac[] >>
      qabbrev_tac ‘c = EL (w2n d) os’ >>
      ‘rss' d = rss c’ by rw[Abbr ‘rss’] >>
      qpat_x_assum ‘is_order rss order’ (mp_tac o Q.SPEC ‘c’ o REWRITE_RULE[is_order_def]) >>
      simp[] >> disch_then (SUBST1_TAC o SYM) >>
      simp[FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      ‘(λ(p1:word64, p2:num). p2) = SND’ by simp[FUN_EQ_THM, FORALL_PROD] >>
      pop_assum SUBST1_TAC >>
      AP_TERM_TAC >> simp[FILTER_EQ, FORALL_PROD] >> rpt strip_tac >>
      ‘MEM p_1 os’ by metis_tac[FST] >>
      metis_tac[])
  >- ((* real time *)
      simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
      rename1 ‘precedes _ _ _ (h ca, ia) (h cb, ib)’ >>
      ‘MEM ca os ∧ MEM cb os’ by metis_tac[FST] >>
      ‘ca ≠ cb’ by (strip_tac >> fs[]) >>
      ‘earlier order (ca, ia) (cb, ib)’ suffices_by
        (strip_tac >>
         qpat_x_assum ‘earlier order _ _’ (strip_assume_tac o REWRITE_RULE[earlier_def]) >>
         simp[earlier_def] >>
         qexistsl_tac [‘MAP (λ(c,i). (h c,i)) l1’, ‘MAP (λ(c,i). (h c,i)) l2’,
                       ‘MAP (λ(c,i). (h c,i)) l3’] >> simp[]) >>
      qpat_x_assum ‘∀x y. MEM x order ∧ _ ⇒ earlier _ _ _’ irule >> simp[] >>
      fs[precedes_def] >>
      drule ren_evs_prefix_inv >> strip_tac >> gvs[] >>
      rename1 ‘E3 ≼ E’ >> qexists_tac ‘E3’ >> simp[] >>
      ‘∀c. MEM c os ⇒
           bytes_written_to (h c) (ren_evs 0 [] E3) = bytes_written_to c E3 ∧
           bytes_read_from (h c) (ren_evs 0 [] E3) = bytes_read_from c E3’
        by (rpt gen_tac >> strip_tac >>
            ‘h c = n2w (findi c os)’ by simp[Abbr ‘h’] >> pop_assum SUBST1_TAC >>
            ‘EL (findi c os) os = c ∧ findi c os < LENGTH os’ by metis_tac[] >>
            mp_tac (Q.INST [‘j’ |-> ‘findi (c:word64) (os:word64 list)’,
                            ‘evs’ |-> ‘E:io_event list’, ‘evs1’ |-> ‘E3:io_event list’]
                      kv_bytes_prefix) >>
            impl_tac >- fs[Abbr ‘os’] >>
            qpat_x_assum ‘Abbrev (os = _)’
              (fn th => REWRITE_TAC[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
            metis_tac[]) >>
      ‘rss' (h cb) = rss cb’ by rw[Abbr ‘rss’] >>
      metis_tac[]) >>
  (* what is written *)
  gen_tac >> rename1 ‘bytes_written_to d _’ >>
  reverse (Cases_on ‘w2n d < LENGTH os’) >- (‘LENGTH os ≤ w2n d’ by decide_tac >> simp[]) >>
  ‘MEM (EL (w2n d) os) os ∧ h (EL (w2n d) os) = d’ by metis_tac[] >>
  qabbrev_tac ‘c = EL (w2n d) os’ >>
  qpat_x_assum ‘h c = d’ (SUBST1_TAC o SYM) >> simp[]
QED

(* ------------------------------------------------------------------------
   The converse
   ------------------------------------------------------------------------ *)

Theorem reply_bytes_TAKE[local]:
  reply_bytes (TAKE k ans) ≼ reply_bytes ans
Proof
  ‘ans = TAKE k ans ++ DROP k ans’ by simp[] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[reply_bytes_APPEND]
QED

(* MAIN: for an fd-disciplined program, HttpKvSpec over the version-1
   server worlds connecting at most M clients implies the endpoint
   key-value spec with version 1's calls, in every world leaving room for
   one more client *)
Theorem endpoint_of_kv_spec_le:
  v1_disciplined lfd prog ∧ kv_spec_le lfd prog ⇒
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
               nonsat1 lfd a w)
    ep_kv_guar prog
Proof
  rw[rg_spec_def] >>
  ‘∀sk N. server_world2 lfd sk ∧ (∀n. nconn sk n ≤ N) ∧
          LENGTH sk.reserved + N + 3 < dimword (:64) ⇒
          ∃io. semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog
                 (Diverge io) ∧ kv_safe io ∧
               acc_live (λx y. ∀rs. EVERY valid_brequest rs ∧ brequests rs ≼ x ⇒
                                    ∃ans. LENGTH ans = LENGTH rs ∧ reply_bytes ans ≼ y) sk io’
    by (mp_tac (Q.INST [‘Rel’ |-> ‘λrs y. ∃ans. LENGTH ans = LENGTH rs ∧ reply_bytes ans ≼ y’,
                        ‘Sf’ |-> ‘kv_safe’,
                        ‘r0’ |-> ‘Req "GET" "/" "1.1" [] ""’] req_acc_live) >>
        simp[] >>
        impl_tac
        >- (rpt conj_tac >>
            TRY (EVAL_TAC >> NO_TAC) >>
            TRY (rpt strip_tac >> qexists_tac ‘TAKE (LENGTH rs') ans’ >>
                 imp_res_tac IS_PREFIX_LENGTH >> simp[] >>
                 irule IS_PREFIX_TRANS >> qexists_tac ‘reply_bytes ans’ >>
                 simp[reply_bytes_TAKE] >> NO_TAC) >>
            TRY (rpt strip_tac >> qexists_tac ‘ans’ >> simp[] >>
                 irule IS_PREFIX_TRANS >> metis_tac[] >> NO_TAC) >>
            TRY (rpt strip_tac >> Cases_on ‘ans’ >> fs[] >>
                 fs[reply_bytes_def, HttpSpecTheory.bytes_def, print_response_nonempty] >>
                 NO_TAC) >>
            rpt strip_tac >>
            ‘LENGTH sk.reserved + N + 3 < dimword (:64)’ by fs[] >>
            drule_all v1of2_props >> strip_tac >>
            qpat_x_assum ‘kv_spec_le _ _’ (mp_tac o REWRITE_RULE [kv_spec_le_def]) >>
            disch_then (qspecl_then [‘v1of2 lfd sk’, ‘N’] mp_tac) >>
            impl_tac >- (fs[sched_connects_le_conns] >> decide_tac) >> strip_tac >>
            qexists_tac ‘io’ >> fs[kv_live_def] >> metis_tac[]) >>
        simp[]) >>
  drule_at (Pos (el 2)) endpoint_of_v1_live >> simp[] >>
  disch_then drule_all >> strip_tac >> qexists_tac ‘io’ >>
  simp[ep_kv_guar_def] >>
  irule kv_sym_safe >> simp[v1_tr_def] >> metis_tac[]
QED

(* MAIN: the disciplined kv_sym_equiv *)
Theorem kv_sym_equiv_disc_thm:
  ∀lfd a prog.
    v1_disciplined lfd prog ⇒
    (rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
       ep_kv_guar prog ⇒ kv_spec_le lfd prog) ∧
    (kv_spec_le lfd prog ⇒
     rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
                  nonsat1 lfd a w)
       ep_kv_guar prog)
Proof
  rpt strip_tac
  >- (REWRITE_TAC[kv_spec_le_def] >> rpt strip_tac >>
      drule_all kv_spec_of_endpoint_disc >> simp[])
  >> metis_tac[endpoint_of_kv_spec_le]
QED
