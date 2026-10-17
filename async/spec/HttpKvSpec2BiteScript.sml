(*
  HttpKvSpec2 bites: the statement rules out plausible bugs, and its
  assumptions are satisfiable with fds actually reused.  Everything here
  is proved.

  - NEW, fd reuse: a server that answers a previous connection's request
    on the new connection that reuses its fd violates kv_safe2
    (broken_kv_answers_across_reuse).  HttpKvSpec's per-fd kv_safe does
    NOT catch this bug (v1_kv_misses_leak).
  - NEW, closing: a server that answers, reads the client's EOF and never
    closes is linearizable and live, but violates echo_closes2
    (broken_kv_never_closes).
  - Non-vacuity: a fair version-2 world in which two clients each send
    GET /x and close (two_gets_world2), and an ideal trace for it, with
    two episodes on the same fd, that is linearizable, live and closes
    (ideal_kv2_trace_spec).
  HttpKvSpec's own bites (lost writes, a store per connection, stale
  reads, never answering) carry over per episode.
*)
Theory HttpKvSpec2Bite
Ancestors
  HttpKvSpec2 HttpKvSpec HttpKvSpecBite HttpSpecBodiesBite HttpSpecBodies HttpSpec EchoSpec2Bite
  EchoSpec2 EchoSpecBite EchoSpec ffiSpikeSocketFFI socketV2FFI socketV2Fair
  llist rich_list Marshalling
Libs
  preamble

Overload gR = “brequests [gx]”

(* ------------------------------------------------------------------------
   Helpers
   ------------------------------------------------------------------------ *)

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

Theorem prefix_take[local]:
  evs ≼ l ⇔ ∃n. n ≤ LENGTH l ∧ evs = TAKE n l
Proof
  eq_tac >> rw[]
  >- (qexists_tac ‘LENGTH evs’ >> gvs[IS_PREFIX_APPEND] >> simp[TAKE_APPEND1])
  >> simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP n l’ >> simp[]
QED

Theorem valid_gx[local]:
  valid_brequest gx
Proof
  EVAL_TAC
QED

Theorem no_full_nil[local]:
  no_full_brequest []
Proof
  rw[no_full_brequest_def, IS_PREFIX_NIL] >> Cases_on ‘r’ >>
  simp[brequests_def, print_brequest_def, bytes_def]
QED

Theorem brequests_nil[local]:
  brequests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[brequests_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_brequest_def]
QED

Theorem bytes_split[local]:
  ∀s p rest. bytes p ++ rest = bytes s ⇒ ∃s'. s = p ++ s' ∧ rest = bytes s'
Proof
  simp[bytes_def] >> Induct_on ‘p’ >> rw[] >>
  Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem brequests_CONS[local]:
  brequests [] = [] ∧
  brequests (r :: rs) = bytes (print_brequest r) ++ brequests rs
Proof
  simp[brequests_def, bytes_def]
QED

(* The only valid requests whose bytes, followed by a rest, are the bytes
   of r are none, or r itself with nothing after *)
Theorem brequests_of_one[local]:
  valid_brequest r ∧ EVERY valid_brequest rs ∧
  brequests rs ++ rest = brequests [r] ⇒
  rs = [] ∨ (rs = [r] ∧ rest = [])
Proof
  Cases_on ‘rs’ >> rw[] >> fs[brequests_CONS] >>
  ‘bytes (print_brequest h) ++ (brequests t ++ rest) = bytes (print_brequest r)’
    by fs[] >>
  drule bytes_split >> strip_tac >>
  ‘h = r ∧ s' = []’
    by (irule print_brequest_unique >> fs[]) >>
  qpat_x_assum ‘print_brequest r = _’ kall_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[bytes_def, APPEND_eq_NIL, brequests_nil]
QED

(* What was read is nothing or one GET /x: the requests are known *)
Theorem read_gets[local]:
  EVERY valid_brequest rs ∧ no_full_brequest rest ∧ brequests rs ++ rest = x ∧
  (x = [] ∨ x = gR) ⇒
  (x = [] ⇒ rs = []) ∧ (x = gR ⇒ rs = [gx])
Proof
  rw[] >> gvs[APPEND_eq_NIL, brequests_nil] >>
  qspecl_then [‘rs’, ‘[gx]’, ‘rest’, ‘[]’] mp_tac parse_unique >>
  simp[valid_gx, no_full_nil]
QED


(* ------------------------------------------------------------------------
   Linearizability of traces whose episodes each send one GET /x
   ------------------------------------------------------------------------ *)

(* In every prefix, each episode has read nothing and written nothing, or
   (for the first two) read GET /x and written nothing or its 404; and
   episode 1 is written to only after episode 0's request was read *)
Definition gets_trace_def:
  gets_trace tr ⇔
    (∀evs j. evs ≼ tr ⇒
       ep_read j evs = [] ∧ ep_written j evs = [] ∨
       j < 2 ∧ ep_read j evs = gR ∧
       (ep_written j evs = [] ∨ ep_written j evs = reply_bytes [NotFound])) ∧
    (∀evs. evs ≼ tr ∧ ep_written 1 evs ≠ [] ⇒ ep_read 0 evs ≠ [])
End

Theorem gets_kv_safe2:
  gets_trace tr ⇒ kv_safe2 (fromList tr)
Proof
  rw[gets_trace_def, kv_safe2_def, LPREFIX_fromList_fromList] >>
  ‘∀j. (ep_read j evs = [] ⇒ rss j = []) ∧ (ep_read j evs = gR ⇒ rss j = [gx]) ∧
       (ep_read j evs = [] ∨ ep_read j evs = gR) ∧ (2 ≤ j ⇒ rss j = [])’
    by (gen_tac >> first_x_assum (qspec_then ‘j’ strip_assume_tac) >>
        first_x_assum (qspecl_then [‘evs’, ‘j’] mp_tac) >> simp[] >> strip_tac >>
        rpt conj_tac >> rpt strip_tac >> fs[brequests_nil] >>
        qspecl_then [‘rss j’, ‘rests j’, ‘gR’] mp_tac
          (Q.GENL [‘rs’, ‘rest’, ‘x’] read_gets) >> simp[]) >>
  qexists_tac ‘FILTER (λx. rss (FST x) ≠ []) [(0,0); (1,0)]’ >>
  ‘∀j. rss j = [] ∨ rss j = [gx]’ by metis_tac[NOT_LESS] >>
  ‘∀rss' : num -> brequest list. (∀j. rss' j = [] ∨ rss' j = [gx]) ⇒
     ∀j. replies rss' (FILTER (λx. rss' (FST x) ≠ []) [(0,0); (1,0)]) j =
         if j < 2 ∧ rss' j ≠ [] then [NotFound] else []’
    by (rpt strip_tac >>
        first_assum (qspec_then ‘0’ strip_assume_tac) >>
        first_assum (qspec_then ‘1’ strip_assume_tac) >>
        simp[replies_def] >> rw[] >> gvs[] >>
        simp[kv_run_def, kv_step_def, kget_def] >>
        Cases_on ‘j = 0’ >> Cases_on ‘j = 1’ >> gvs[] >> rw[] >> fs[]) >>
  rpt conj_tac
  >- (rw[is_order2_def] >>
      qpat_assum ‘∀j. rss j = [] ∨ _’ (qspec_then ‘0’ strip_assume_tac) >>
      qpat_assum ‘∀j. rss j = [] ∨ _’ (qspec_then ‘1’ strip_assume_tac) >>
      (Cases_on ‘j < 2’
       >- (‘j = 0 ∨ j = 1’ by fs[] >> fs[] >> EVAL_TAC) >>
       ‘rss j = []’ by metis_tac[NOT_LESS] >>
       fs[COUNT_LIST_def] >> rw[] >> fs[]))
  >- (rpt gen_tac >> strip_tac >>
      ‘MEM x [(0,0); (1,0)] ∧ MEM y [(0,0); (1,0)]’ by gvs[MEM_FILTER] >>
      gvs[] >> gvs[MEM_FILTER]
      >- (‘rss 0 ≠ [] ∧ rss 1 ≠ []’
            by (rpt (qpat_x_assum ‘MEM _ _’ mp_tac) >> rpt (IF_CASES_TAC >> simp[])) >>
          simp[earlier_def] >> qexistsl [‘[]’, ‘[]’, ‘[]’] >> simp[])
      >- (qpat_x_assum ‘precedes2 _ _ _ _ _’ mp_tac >> simp[precedes2_def] >>
          rpt strip_tac >>
          ‘evs1 ≼ tr’ by metis_tac[IS_PREFIX_TRANS] >>
          ‘ep_written 1 evs1 ≠ []’
            by (‘rss 1 ≠ []’ by (qpat_x_assum ‘MEM (1,0) _’ mp_tac >> rpt (IF_CASES_TAC >> simp[])) >>
                strip_tac >> fs[reply_bytes_def, bytes_def, print_response_def]) >>
          ‘ep_read 0 evs1 = []’ by fs[brequests_def, bytes_def] >> metis_tac[]))
  >> gen_tac >> first_x_assum (qspec_then ‘rss’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘j’ SUBST1_TAC) >>
  first_x_assum (qspecl_then [‘evs’, ‘j’] mp_tac) >> simp[] >> rw[] >> gvs[] >>
  first_x_assum (qspec_then ‘j’ strip_assume_tac) >> gvs[]
QED

(* ------------------------------------------------------------------------
   fd reuse: a new connection never receives the previous one's answer
   ------------------------------------------------------------------------ *)

Theorem LENGTH_kv_run[local]:
  ∀l st. LENGTH (kv_run st l) = LENGTH l
Proof
  Induct >> simp[kv_run_def] >> rpt gen_tac >> Cases_on ‘kv_step st h’ >> simp[]
QED

Theorem FILTER_ZIP_nil[local]:
  ∀order (l : response list).
    LENGTH order = LENGTH l ∧ FILTER (λx. FST x = j) order = [] ⇒
    FILTER (λ((d, i:num), a). d = j) (ZIP (order, l)) = []
Proof
  Induct >> simp[] >> gen_tac >> Cases >> simp[] >> PairCases_on ‘h’ >>
  rw[] >> fs[]
QED

Overload kv_leak = “[acc L c1; rd c1 gR 100; cls c1; acc L c1; wr c1 (reply_bytes [NotFound])]”

(* NEW: such a server violates kv_safe2 *)
Theorem broken_kv_answers_across_reuse:
  starts_with kv_leak io ⇒ ¬kv_safe2 io
Proof
  rw[kv_safe2_def] >>
  qexistsl [‘kv_leak’, ‘λj. if j = 0 then [gx] else []’, ‘K []’] >>
  simp[no_full_nil, valid_gx] >> conj_tac
  >- (gen_tac >> Cases_on ‘j = 0’ >> simp[valid_gx]
      >- EVAL_TAC >> simp[brequests_def, bytes_def] >>
      Cases_on ‘j = 1’ >> simp[] >> EVAL_TAC >> rw[] >> fs[]) >>
  gen_tac >> CCONTR_TAC >> fs[is_order2_def] >>
  qpat_x_assum ‘∀j. ep_written _ _ ≼ _’ (qspec_then ‘1’ mp_tac) >>
  qpat_x_assum ‘∀j. MAP SND _ = _’ (qspec_then ‘1’ mp_tac) >> simp[] >> strip_tac >>
  ‘replies (λj. if j = 0 then [gx] else []) order 1 = []’
    by (simp[replies_def] >> irule FILTER_ZIP_nil >>
        fs[COUNT_LIST_def, LENGTH_kv_run]) >>
  simp[] >> EVAL_TAC
QED

Theorem gR_nonempty[local]:
  gR ≠ []
Proof
  EVAL_TAC
QED

(* ... but HttpKvSpec's per-fd kv_safe does not catch it: on fd c1, GET /x
   was read and its 404 written *)
Theorem v1_kv_misses_leak:
  kv_safe (fromList kv_leak) ∧ ¬kv_safe2 (fromList kv_leak)
Proof
  reverse conj_tac >- (irule broken_kv_answers_across_reuse >> simp[]) >>
  rw[kv_safe_def, LPREFIX_fromList_fromList] >>
  ‘∀c. bytes_read_from c evs = [] ∧ bytes_written_to c evs = [] ∨
       c = c1 ∧ bytes_read_from c evs = gR ∧
       (bytes_written_to c evs = [] ∨ bytes_written_to c evs = reply_bytes [NotFound])’
    by (gen_tac >> qpat_x_assum ‘∀c. EVERY _ _ ∧ _’ kall_tac >>
        qpat_x_assum ‘_ ≼ _’ (strip_assume_tac o REWRITE_RULE [prefix_take]) >>
        ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5’ by fs[] >> gvs[] >>
        EVAL_TAC >> rw[] >> EVAL_TAC) >>
  ‘∀c. rss c = if c = c1 ∧ bytes_read_from c evs ≠ [] then [gx] else []’
    by (gen_tac >> first_x_assum (qspec_then ‘c’ strip_assume_tac) >>
        first_x_assum (qspec_then ‘c’ strip_assume_tac) >> gvs[] >>
        TRY (gvs[APPEND_eq_NIL, brequests_nil] >> NO_TAC) >>
        qspecl_then [‘rss c1’, ‘rests c1’, ‘gR’] mp_tac
          (Q.GENL [‘rs’, ‘rest’, ‘x’] read_gets) >> simp[] >> EVAL_TAC) >>
  qpat_x_assum ‘∀c. EVERY _ _ ∧ _’ kall_tac >>
  qexists_tac ‘if rss c1 = [] then [] else [(c1, 0)]’ >> rpt conj_tac
  >- (rw[is_order_def] >> rw[] >> gvs[] >> EVAL_TAC)
  >- (rw[] >> fs[])
  >> gen_tac >>
  qpat_x_assum ‘∀c. bytes_read_from _ _ = [] ∧ _ ∨ _’ (qspec_then ‘c’ strip_assume_tac) >>
  qpat_assum ‘∀c. rss c = _’ (qspec_then ‘4w’ assume_tac) >>
  qpat_x_assum ‘∀c. rss c = _’ (qspec_then ‘c’ assume_tac) >>
  rfs[gR_nonempty] >> rw[replies_def] >> rfs[gR_nonempty] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   A fair world with reuse: two clients, each sends GET /x and closes
   ------------------------------------------------------------------------ *)

Definition two_gets_world2_def:
  two_gets_world2 =
    <| listening := [(3w, [])]; clients := []; open_fds := [];
       reserved := [0w; 1w; 2w]; alloc := (λj. lowest_free);
       future := [| [Connect2 3w; Data2 0 gR; Eof2 0];
                    [Connect2 3w; Data2 1 gR; Eof2 1] |] |>
End

Theorem ticks2_quiet[local]:
  ∀n s. s.future = [||] ⇒ ticks2 n s = s
Proof
  Induct >> rw[ticks2_def, tick2_def]
QED

Theorem two_gets_world2_sched_wf[local]:
  sched_wf2 two_gets_world2
Proof
  rw[sched_wf2_def] >> Cases_on ‘n’ >- EVAL_TAC
  >> Cases_on ‘n'’ >- EVAL_TAC
  >> simp[ticks2_def]
  >> ‘(tick2 (tick2 two_gets_world2)).future = [||]’ by EVAL_TAC
  >> simp[ticks2_quiet, next_step2_def, step_ok2_def]
QED

(* NON-VACUITY: the assumption holds *)
Theorem server_world2_two_gets:
  server_world2 3w two_gets_world2
Proof
  simp[server_world2_def, two_gets_world2_sched_wf] >> conj_tac >- EVAL_TAC >>
  simp[two_gets_world2_def, lowest_free_alloc_ok]
QED

Theorem arrivals2_upto_nil[local]:
  arrivals2_upto n [||] = []
Proof
  Cases_on ‘n’ >> simp[arrivals2_upto_def]
QED

Theorem sent2_upto_two_gets[local]:
  sent2_upto j n two_gets_world2 =
    if j = 0 ∧ 1 ≤ n then gR else if j = 1 ∧ 2 ≤ n then gR else []
Proof
  Cases_on ‘n’ >> simp[sent2_upto_def, arrivals2_upto_def, two_gets_world2_def]
  >> Cases_on ‘n'’ >> simp[arrivals2_upto_def, arrivals2_upto_nil] >>
  Cases_on ‘j = 0’ >> Cases_on ‘j = 1’ >> fs[]
QED

(* What a client of this world has sent is no request, or GET /x *)
Theorem sent_gx[local]:
  EVERY valid_brequest rs ∧ brequests rs ≼ sent2_upto j n two_gets_world2 ⇒
  rs = [] ∨ (rs = [gx] ∧ (j = 0 ∧ 1 ≤ n ∨ j = 1 ∧ 2 ≤ n))
Proof
  strip_tac >> fs[sent2_upto_two_gets] >>
  ‘brequests rs ≼ gR ⇒ rs = [] ∨ rs = [gx]’
    by (rw[IS_PREFIX_APPEND] >>
        ‘rs = [] ∨ (rs = [gx] ∧ l = [])’
          by (irule brequests_of_one >> simp[valid_gx]) >> fs[]) >>
  Cases_on ‘j = 0 ∧ 1 ≤ n’ >> fs[] >>
  Cases_on ‘j = 1 ∧ 2 ≤ n’ >> fs[brequests_nil]
QED

(* ------------------------------------------------------------------------
   An ideal trace, with two episodes on the same fd
   ------------------------------------------------------------------------ *)

Overload ideal_kv2 =
  “[acc L 4w; rd 4w gR 100; wr 4w (reply_bytes [NotFound]); rdeof 4w 100; cls 4w;
    acc L 4w; rd 4w gR 100; wr 4w (reply_bytes [NotFound]); rdeof 4w 100; cls 4w]”

Theorem ideal_kv2_gets[local]:
  gets_trace ideal_kv2
Proof
  rw[gets_trace_def, prefix_take] >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
   n = 8 ∨ n = 9 ∨ n = 10’ by fs[] >>
  TRY (‘j = 0 ∨ j = 1 ∨ 2 ≤ j’ by fs[]) >> gvs[] >>
  rpt (pop_assum mp_tac) >> EVAL_TAC >> rw[] >> fs[]
QED

Theorem ideal_kv2_live[local]:
  kv_live2 two_gets_world2 (fromList ideal_kv2)
Proof
  rw[kv_live2_def] >> drule_all sent_gx >> rw[]
  >- (qexistsl [‘[]’, ‘[]’] >> simp[] >> EVAL_TAC)
  >> qexistsl [‘ideal_kv2’, ‘[NotFound]’] >> simp[LPREFIX_fromList_fromList] >>
  EVAL_TAC
QED

Theorem ideal_kv2_closes[local]:
  echo_closes2 (fromList ideal_kv2)
Proof
  rw[echo_closes2_def, LPREFIX_fromList_fromList] >>
  qexists_tac ‘ideal_kv2’ >> simp[] >>
  ‘j < LENGTH (accepted_fds evs)’ by gvs[ep_eof_read_def] >>
  ‘accepted_fds evs ≼ accepted_fds ideal_kv2’
    by (qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
        ASM_REWRITE_TAC [accepted_fds_def, MAP_APPEND, FLAT_APPEND] >>
        REWRITE_TAC [IS_PREFIX_APPEND] >> metis_tac[]) >>
  ‘LENGTH (accepted_fds ideal_kv2) = 2’ by EVAL_TAC >>
  imp_res_tac IS_PREFIX_LENGTH >>
  ‘j = 0 ∨ j = 1’ by simp[] >> gvs[] >> EVAL_TAC
QED

(* NON-VACUITY: in a fair world with reuse, the three clauses are jointly
   satisfiable *)
Theorem ideal_kv2_trace_spec:
  server_world2 3w two_gets_world2 ∧
  kv_safe2 (fromList ideal_kv2) ∧ kv_live2 two_gets_world2 (fromList ideal_kv2) ∧
  echo_closes2 (fromList ideal_kv2)
Proof
  simp[server_world2_two_gets, gets_kv_safe2, ideal_kv2_gets, ideal_kv2_live,
       ideal_kv2_closes]
QED

(* ------------------------------------------------------------------------
   A server that never closes
   ------------------------------------------------------------------------ *)

Overload noclose_kv2 =
  “[acc L 4w; rd 4w gR 100; wr 4w (reply_bytes [NotFound]); rdeof 4w 100;
    acc L 5w; rd 5w gR 100; wr 5w (reply_bytes [NotFound]); rdeof 5w 100]”

Theorem noclose_kv2_gets[local]:
  gets_trace noclose_kv2
Proof
  rw[gets_trace_def, prefix_take] >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
   n = 8’ by fs[] >>
  TRY (‘j = 0 ∨ j = 1 ∨ 2 ≤ j’ by fs[]) >> gvs[] >>
  rpt (pop_assum mp_tac) >> EVAL_TAC >> rw[] >> fs[]
QED

(* NEW: it is linearizable and live, but violates echo_closes2 *)
Theorem broken_kv_never_closes:
  kv_safe2 (fromList noclose_kv2) ∧
  kv_live2 two_gets_world2 (fromList noclose_kv2) ∧
  ¬echo_closes2 (fromList noclose_kv2)
Proof
  rpt conj_tac
  >- simp[gets_kv_safe2, noclose_kv2_gets]
  >- (rw[kv_live2_def] >> drule_all sent_gx >> rw[]
      >- (qexistsl [‘[]’, ‘[]’] >> simp[] >> EVAL_TAC)
      >> qexistsl [‘noclose_kv2’, ‘[NotFound]’] >> simp[LPREFIX_fromList_fromList] >>
      EVAL_TAC)
  >> rw[echo_closes2_def, LPREFIX_fromList_fromList] >>
  qexistsl [‘noclose_kv2’, ‘0’] >> simp[] >> conj_tac >- EVAL_TAC >>
  rw[] >> Cases_on ‘evs' ≼ noclose_kv2’ >> simp[] >> gvs[prefix_take] >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
   n = 8’ by simp[] >> gvs[] >> EVAL_TAC
QED
