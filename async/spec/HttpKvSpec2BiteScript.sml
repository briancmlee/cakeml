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
  - From the spec review (kv2): non-vacuity on a trace the FFI really
    produces, with real polls and the second accept reusing fd 4, idling
    forever (real_trace_spec); real time across two episodes on the same
    reused fd (broken_stale_across_reuse).
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

(* ========================================================================
   From the spec review of HttpKvSpec2 (checks R1 and R2):

   R1  Non-vacuity with REAL polls: the trace is the one CakeML's call_FFI
       produces when a program makes these FFI calls in two_gets_world2
       (polls included; the second accept really reuses fd 4), and the
       infinite trace that then polls forever ("stutters") is
       linearizable, live and closes.
   R2  Real time across two episodes on the SAME reused fd: episode 0
       POSTs x and is answered and closed; episode 1, on fd 4 again,
       GETs x and is answered 404 (a stale read): rejected.
   ======================================================================== *)

(* ------------------------------------------------------------------------
   R1: running FFI calls exactly as CakeML's semantics does
   ------------------------------------------------------------------------ *)

Definition run2_def:
  run2 st [] = SOME st ∧
  run2 st ((n, conf, bytes) :: cs) =
    case call_FFI st (ExtCall n) conf bytes of
    | FFI_return st' _ => run2 st' cs
    | FFI_final _ => NONE
End

Theorem run2_append:
  ∀xs st. run2 st (xs ++ ys) =
          case run2 st xs of NONE => NONE | SOME st' => run2 st' ys
Proof
  Induct >> simp[run2_def, FORALL_PROD] >> rw[] >> CASE_TAC >> simp[]
QED

(* The calls of a simple server: poll the listener; accept; read the
   request; write the 404; read the EOF; close.  Twice. *)
Overload pollc = “(«sock_poll», fd_bytes 3w, [0w : word8])”
Overload epc =
  “[(«sock_accept», fd_bytes 3w, REPLICATE 9 (0w : word8));
    («sock_read», fd_bytes 4w, REPLICATE 109 (0w : word8));
    («sock_write», fd_bytes 4w ++ reply_bytes [NotFound], [] : word8 list);
    («sock_read», fd_bytes 4w, REPLICATE 109 (0w : word8));
    («sock_close», fd_bytes 4w, [] : word8 list)]”
Overload real_calls = “pollc :: epc ++ pollc :: epc”

(* A poll of the listener that reported b *)
Definition poll_ev_def:
  poll_ev (b : word8) = IO_event (ExtCall «sock_poll») (fd_bytes 3w) (ZIP ([0w], [b]))
End

Overload ep_evs =
  “[acc L 4w; rd 4w gR 100; wr 4w (reply_bytes [NotFound]); rdeof 4w 100; cls 4w]”
Overload real_tr = “poll_ev 1w :: ep_evs ++ poll_ev 1w :: ep_evs”

Theorem lowest_free_0123[local]:
  lowest_free [0w; 1w; 2w; 3w] = 4w
Proof
  REWRITE_TAC[lowest_free_def] >>
  ‘(LEAST n. ¬MEM (n2w n : word64) [0w; 1w; 2w; 3w]) = 4’
    suffices_by simp[] >>
  numLib.LEAST_ELIM_TAC >> rw[]
  >- (qexists_tac ‘4’ >> EVAL_TAC) >>
  CCONTR_TAC >> ‘n < 4 ∨ 4 < n’ by simp[]
  >- (‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3’ by simp[] >> gvs[]) >>
  first_x_assum (qspec_then ‘4’ mp_tac) >> simp[] >> EVAL_TAC
QED

(* Evaluate the run, keeping lowest_free folded until it is rewritten *)
val real_run_eval =
  (computeLib.RESTR_EVAL_CONV [“lowest_free”] THENC REWRITE_CONV [lowest_free_0123] THENC
   computeLib.RESTR_EVAL_CONV [“lowest_free”] THENC REWRITE_CONV [lowest_free_0123] THENC
   EVAL) “run2 (socket2_ffi two_gets_world2) real_calls”;

(* MAIN (R1): the FFI really produces real_tr, and leaves a world in which
   nothing more arrives and the listener has nothing pending *)
Theorem real_run:
  ∃st. run2 (socket2_ffi two_gets_world2) real_calls = SOME st ∧
       st.io_events = real_tr ∧ st.oracle = socket2_oracle ∧
       st.ffi_state.future = [||] ∧ st.ffi_state.listening = [(3w, [])] ∧
       st.ffi_state.open_fds = []
Proof
  REWRITE_TAC [real_run_eval, optionTheory.SOME_11] >>
  CONV_TAC (QUANT_CONV (LAND_CONV SYM_CONV)) >>
  CONV_TAC Unwind.UNWIND_EXISTS_CONV >> EVAL_TAC
QED

Theorem run2_polls:
  ∀m st. st.oracle = socket2_oracle ∧ st.ffi_state.future = [||] ∧
         st.ffi_state.listening = [(3w, [])] ∧ st.ffi_state.open_fds = [] ⇒
         ∃st'. run2 st (REPLICATE m pollc) = SOME st' ∧
               st'.io_events = st.io_events ++ REPLICATE m (poll_ev 0w) ∧
               st'.oracle = socket2_oracle ∧ st'.ffi_state = st.ffi_state
Proof
  Induct >> simp[run2_def] >> rpt strip_tac >>
  ‘call_FFI st (ExtCall «sock_poll») (fd_bytes 3w) [0w] =
   FFI_return (st with io_events := st.io_events ++ [poll_ev 0w]) [0w]’
    by (simp[ffiTheory.call_FFI_def, socket2_oracle_def, socket2_fn_def,
             ffi_sock_poll2_def, tick2_def, is_ready2_def, client_of_def,
             poll_ev_def] >>
        EVAL_TAC >> simp[ffiTheory.ffi_state_component_equality]) >>
  simp[] >>
  first_x_assum (qspec_then ‘st with io_events := st.io_events ++ [poll_ev 0w]’ mp_tac) >>
  simp[] >> strip_tac >> simp[]
QED

(* MAIN (R1): every finite stretch of "real_tr, then m idle polls" is what
   the FFI produces *)
Theorem real_run_polls:
  ∀m. ∃st. run2 (socket2_ffi two_gets_world2) (real_calls ++ REPLICATE m pollc) = SOME st ∧
           st.io_events = real_tr ++ REPLICATE m (poll_ev 0w)
Proof
  gen_tac >> strip_assume_tac real_run >>
  drule_all run2_polls >> disch_then (qspec_then ‘m’ strip_assume_tac) >>
  ONCE_REWRITE_TAC [run2_append] >> ASM_REWRITE_TAC [] >> simp[]
QED

(* ------------------------------------------------------------------------
   R1: stutter lemmas: idle polls change no projection
   ------------------------------------------------------------------------ *)

Theorem ep_events_append:
  ∀xs k opn. ∃k' opn'.
    ep_events j k opn (xs ++ ys) = ep_events j k opn xs ++ ep_events j k' opn' ys
Proof
  Induct >> simp[ep_events_def] >- metis_tac[] >>
  rpt gen_tac >> rpt (CASE_TAC >> simp[]) >> metis_tac[APPEND_ASSOC]
QED

Theorem poll_ev_inert:
  event_accepted (poll_ev b) = NONE ∧ event_closed (poll_ev b) = NONE ∧
  event_eof (poll_ev b) = NONE ∧ event_read c (poll_ev b) = [] ∧
  event_written c (poll_ev b) = []
Proof
  simp[poll_ev_def] >> EVAL_TAC
QED

Theorem ep_events_polls:
  ∀m k opn. EVERY (λe. e = poll_ev 0w) (ep_events j k opn (REPLICATE m (poll_ev 0w)))
Proof
  Induct >> simp[ep_events_def, poll_ev_inert] >> rw[]
QED

Theorem every_poll_proj[local]:
  EVERY (λe. e = poll_ev 0w) l ⇒
  bytes_read_from c l = [] ∧ bytes_written_to c l = [] ∧
  ¬EXISTS (λev. event_eof ev = SOME f) l ∧ ¬EXISTS (λev. event_closed ev = SOME f) l
Proof
  Induct_on ‘l’ >> simp[bytes_read_from_def, bytes_written_to_def] >>
  rw[] >> fs[poll_ev_inert, bytes_read_from_def, bytes_written_to_def]
QED

(* MAIN (stutter): idle polls after a trace change none of the per-episode
   projections the spec uses *)
Theorem stutter:
  accepted_fds (tr ++ REPLICATE m (poll_ev 0w)) = accepted_fds tr ∧
  ep_read j (tr ++ REPLICATE m (poll_ev 0w)) = ep_read j tr ∧
  ep_written j (tr ++ REPLICATE m (poll_ev 0w)) = ep_written j tr ∧
  (ep_eof_read j (tr ++ REPLICATE m (poll_ev 0w)) ⇔ ep_eof_read j tr) ∧
  (ep_closed j (tr ++ REPLICATE m (poll_ev 0w)) ⇔ ep_closed j tr)
Proof
  ‘∀m. accepted_fds (REPLICATE m (poll_ev 0w)) = []’
    by (Induct >> fs[accepted_fds_def, poll_ev_inert]) >>
  ‘accepted_fds (tr ++ REPLICATE m (poll_ev 0w)) = accepted_fds tr’
    by (pop_assum (qspec_then ‘m’ mp_tac) >> simp[accepted_fds_def]) >>
  qspecl_then [‘tr’, ‘0’, ‘[]’] strip_assume_tac
    (Q.GEN ‘ys’ ep_events_append |> Q.SPEC ‘REPLICATE m (poll_ev 0w)’) >>
  qspecl_then [‘m’, ‘k'’, ‘opn'’] assume_tac ep_events_polls >>
  drule every_poll_proj >> strip_tac >>
  simp[ep_read_def, ep_written_def, ep_eof_read_def, ep_closed_def,
       bytes_read_from_def, bytes_written_to_def] >>
  fs[bytes_read_from_def, bytes_written_to_def]
QED

(* ------------------------------------------------------------------------
   R1: the infinite trace: real_tr, then idle polls forever
   ------------------------------------------------------------------------ *)

Definition io_real_def:
  io_real = LGENLIST (λn. if n < LENGTH real_tr then EL n real_tr else poll_ev 0w) NONE
End

Theorem LGENLIST_NONE_CONS[local]:
  LGENLIST f NONE = f 0 ::: LGENLIST (f o SUC) NONE
Proof
  simp[LNTH_EQ] >> Cases >> simp[LNTH_LGENLIST]
QED

Theorem LTAKE_LGENLIST_NONE[local]:
  ∀n f. LTAKE n (LGENLIST f NONE) = SOME (GENLIST f n)
Proof
  Induct >> simp[] >> rpt gen_tac >> ONCE_REWRITE_TAC[LGENLIST_NONE_CONS] >>
  simp[GENLIST_CONS]
QED

Theorem LPREFIX_LGENLIST_NONE[local]:
  LPREFIX (fromList evs) (LGENLIST f NONE) ⇔ evs = GENLIST f (LENGTH evs)
Proof
  simp[LPREFIX_fromList] >>
  ‘toList (LGENLIST f NONE) = NONE’
    by simp[toList] >>
  simp[LTAKE_LGENLIST_NONE] >> metis_tac[]
QED

Theorem genlist_real[local]:
  GENLIST (λn. if n < LENGTH tr then EL n tr else p) k =
  if k ≤ LENGTH tr then TAKE k tr else tr ++ REPLICATE (k - LENGTH tr) p
Proof
  rw[LIST_EQ_REWRITE, EL_GENLIST, EL_TAKE] >>
  rw[EL_APPEND1, EL_APPEND2, EL_REPLICATE]
QED

(* Every finite prefix of io_real is a prefix of real_tr, or real_tr
   followed by idle polls *)
Theorem take_prefix[local]:
  TAKE n l ≼ l
Proof
  simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP n l’ >> simp[TAKE_DROP]
QED

Theorem LENGTH_real_tr[local]:
  LENGTH real_tr = 12
Proof
  EVAL_TAC
QED

(* Every finite prefix of io_real is a prefix of real_tr, or real_tr
   followed by idle polls *)
Theorem io_real_prefixes:
  LPREFIX (fromList evs) io_real ⇔
  (LENGTH evs ≤ 12 ∧ evs = TAKE (LENGTH evs) real_tr) ∨
  ∃m. evs = real_tr ++ REPLICATE m (poll_ev 0w)
Proof
  REWRITE_TAC[io_real_def, LPREFIX_LGENLIST_NONE] >> REWRITE_TAC[genlist_real] >>
  REWRITE_TAC[LENGTH_real_tr] >> eq_tac >> strip_tac
  >- (Cases_on ‘LENGTH evs ≤ 12’ >> fs[] >> metis_tac[])
  >- (IF_CASES_TAC >- first_assum ACCEPT_TAC >> fs[])
  >> qpat_x_assum ‘evs = _’ SUBST1_TAC >>
  REWRITE_TAC[LENGTH_APPEND, LENGTH_real_tr, LENGTH_REPLICATE] >>
  Cases_on ‘m’ >> simp[]
QED

Theorem real_tr_lprefix[local]:
  LPREFIX (fromList real_tr) io_real
Proof
  REWRITE_TAC[io_real_prefixes] >> disj2_tac >> qexists_tac ‘0’ >>
  REWRITE_TAC[REPLICATE, APPEND_NIL]
QED

Theorem real_tr_gets[local]:
  gets_trace real_tr
Proof
  rw[gets_trace_def, prefix_take] >>
  ‘n ≤ 12’ by (pop_assum mp_tac >> EVAL_TAC >> simp[]) >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
   n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12’ by fs[] >>
  TRY (‘j = 0 ∨ j = 1 ∨ 2 ≤ j’ by fs[]) >> gvs[] >>
  rpt (pop_assum mp_tac) >> EVAL_TAC >> rw[] >> fs[]
QED

Theorem TAKE_REPLICATE[local]:
  ∀m k. TAKE k (REPLICATE m x) = REPLICATE (MIN k m) x
Proof
  Induct >> Cases >> simp[MIN_DEF] >> rw[] >> fs[MIN_DEF]
QED

(* gets_trace survives idle polls *)
Theorem gets_trace_polls[local]:
  gets_trace tr ⇒ gets_trace (tr ++ REPLICATE m (poll_ev 0w))
Proof
  rw[gets_trace_def] >>
  ‘evs ≼ tr ∨ ∃m'. evs = tr ++ REPLICATE m' (poll_ev 0w)’
    by (qpat_x_assum ‘evs ≼ _’ mp_tac >> simp[prefix_take] >> rw[] >>
        Cases_on ‘n ≤ LENGTH tr’
        >- (disj1_tac >> simp[TAKE_APPEND1, IS_PREFIX_APPEND] >>
            metis_tac[TAKE_DROP]) >>
        disj2_tac >> simp[TAKE_APPEND2, TAKE_REPLICATE] >> metis_tac[]) >>
  gvs[stutter] >> metis_tac[IS_PREFIX_REFL]
QED

Theorem kv_safe2_from_finite[local]:
  (∀evs. LPREFIX (fromList evs) io ⇒ ∃l. evs ≼ l ∧ kv_safe2 (fromList l)) ⇒
  kv_safe2 io
Proof
  rw[kv_safe2_def] >> first_x_assum drule >> strip_tac >>
  first_x_assum irule >> simp[LPREFIX_fromList_fromList] >> metis_tac[]
QED

Theorem real_live[local]:
  kv_live2 two_gets_world2 io_real
Proof
  rw[kv_live2_def] >> drule_all sent_gx >> rw[]
  >- (qexistsl [‘[]’, ‘[]’] >> simp[io_real_prefixes] >> EVAL_TAC) >>
  qexistsl [‘real_tr’, ‘[NotFound]’] >> simp[real_tr_lprefix] >> EVAL_TAC
QED

Theorem accepted_fds_prefix[local]:
  evs ≼ l ⇒ accepted_fds evs ≼ accepted_fds l
Proof
  rw[IS_PREFIX_APPEND] >>
  REWRITE_TAC [accepted_fds_def, MAP_APPEND, FLAT_APPEND] >> metis_tac[]
QED

Theorem real_closes[local]:
  echo_closes2 io_real
Proof
  rw[echo_closes2_def] >> qexists_tac ‘real_tr’ >>
  conj_tac >- simp[real_tr_lprefix] >>
  ‘j < LENGTH (accepted_fds evs)’ by gvs[ep_eof_read_def] >>
  ‘LENGTH (accepted_fds real_tr) = 2’ by EVAL_TAC >>
  ‘LENGTH (accepted_fds evs) ≤ 2’
    by (qpat_x_assum ‘LPREFIX _ _’ (strip_assume_tac o REWRITE_RULE [io_real_prefixes])
        >- (‘evs ≼ real_tr’ by metis_tac[take_prefix] >>
            drule accepted_fds_prefix >> strip_tac >>
            imp_res_tac IS_PREFIX_LENGTH >> fs[]) >>
        qpat_x_assum ‘evs = _’ SUBST1_TAC >> REWRITE_TAC[stutter] >> fs[]) >>
  ‘j = 0 ∨ j = 1’ by simp[] >> pop_assum strip_assume_tac >>
  pop_assum SUBST1_TAC >> EVAL_TAC
QED

(* MAIN (R1, non-vacuity with real polls): the world is fair; every finite
   stretch of the trace is what the FFI produces; and the infinite trace
   (real_tr, then idle polls forever) is linearizable, live and closes *)
Theorem real_trace_spec:
  server_world2 3w two_gets_world2 ∧
  (∀m. ∃st. run2 (socket2_ffi two_gets_world2) (real_calls ++ REPLICATE m pollc) = SOME st ∧
            st.io_events = real_tr ++ REPLICATE m (poll_ev 0w)) ∧
  (∀evs. LPREFIX (fromList evs) io_real ⇒
         ∃m. evs ≼ real_tr ++ REPLICATE m (poll_ev 0w)) ∧
  kv_safe2 io_real ∧ kv_live2 two_gets_world2 io_real ∧ echo_closes2 io_real
Proof
  rpt conj_tac
  >- simp[server_world2_two_gets]
  >- simp[real_run_polls]
  >- (rw[io_real_prefixes]
      >- (qexists_tac ‘0’ >> simp[] >> metis_tac[take_prefix]) >>
      qexists_tac ‘m’ >> simp[])
  >- (irule kv_safe2_from_finite >> rw[io_real_prefixes]
      >- (qexists_tac ‘real_tr’ >> simp[gets_kv_safe2, real_tr_gets] >>
          metis_tac[take_prefix])
      >> qexists_tac ‘real_tr ++ REPLICATE m (poll_ev 0w)’ >>
      simp[gets_kv_safe2, gets_trace_polls, real_tr_gets])
  >- simp[real_live]
  >> simp[real_closes]
QED

(* ------------------------------------------------------------------------
   R2: real time across two episodes on the same reused fd
   ------------------------------------------------------------------------ *)

Overload stale2 =
  “[acc L 4w; rd 4w (brequests [x1]) 100; wr 4w (reply_bytes [Ok ""]);
    rdeof 4w 100; cls 4w;
    acc L 4w; rd 4w gR 100; wr 4w (reply_bytes [NotFound])]”

Overload rss2 = “λj:num. if j = 0 then [x1] else if j = 1 then [gx] else []”

Theorem order2_mem[local]:
  (∀j. MAP SND (FILTER (λx. FST x = j) (order : (num # num) list)) =
       if j < 2 then [0] else []) ⇒
  ∀p q. MEM (p,q) order ⇒ (p,q) = (0,0) ∨ (p,q) = (1,0)
Proof
  rpt strip_tac >> first_x_assum (qspec_then ‘p’ mp_tac) >> rw[]
  >- (‘MEM (p,q) (FILTER (λx. FST x = p) order)’ by simp[MEM_FILTER] >> gvs[] >>
      ‘p = 0 ∨ p = 1’ by simp[] >> gvs[])
  >> simp[FILTER_NEQ_NIL] >> qexists_tac ‘(p,q)’ >> simp[]
QED

Theorem split01[local]:
  ∀l : (num # num) list. (∀x. MEM x l ⇒ x = (0,0) ∨ x = (1,0)) ⇒
    LENGTH l = LENGTH (FILTER (λx. FST x = 0) l) + LENGTH (FILTER (λx. FST x = 1) l)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  ‘h = (0,0) ∨ h = (1,0)’ by metis_tac[] >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem order_two_core[local]:
  (∀j. MAP SND (FILTER (λx. FST x = j) (order : (num # num) list)) =
       if j < 2 then [0] else []) ⇒
  order = [(0,0); (1,0)] ∨ order = [(1,0); (0,0)]
Proof
  strip_tac >>
  ‘∀x. MEM x order ⇒ x = (0,0) ∨ x = (1,0)’ by (Cases >> metis_tac[order2_mem]) >>
  qpat_x_assum ‘∀j. _’ (fn th => assume_tac (SIMP_RULE arith_ss [] (Q.SPEC ‘0’ th)) >>
                                  assume_tac (SIMP_RULE arith_ss [] (Q.SPEC ‘1’ th))) >>
  ‘LENGTH order = 2’
    by (drule split01 >> disch_then SUBST1_TAC >>
        rpt (qpat_x_assum ‘MAP SND _ = _’ (mp_tac o Q.AP_TERM ‘LENGTH’)) >> simp[]) >>
  Cases_on ‘order’ >> fs[] >> Cases_on ‘t’ >> fs[] >> Cases_on ‘t'’ >> fs[] >>
  ‘h = (0,0) ∨ h = (1,0)’ by metis_tac[] >> ‘h' = (0,0) ∨ h' = (1,0)’ by metis_tac[] >>
  gvs[]
QED

(* With requests in episodes 0 and 1 only, one each, an order is one of
   the two interleavings *)
Theorem order_two2[local]:
  is_order2 rss order ∧ (∀j. LENGTH (rss j) = if j < 2 then 1 else 0) ⇒
  order = [(0,0); (1,0)] ∨ order = [(1,0); (0,0)]
Proof
  rw[is_order2_def] >> irule order_two_core >>
  gen_tac >> qpat_assum ‘∀j. MAP SND _ = _’ (qspec_then ‘j’ SUBST1_TAC) >>
  qpat_assum ‘∀j. LENGTH _ = _’ (qspec_then ‘j’ SUBST1_TAC) >>
  rw[] >> EVAL_TAC
QED

Theorem earlier_two[local]:
  ¬earlier [(1n,0n); (0n,0n)] (0n,0n) (1n,0n)
Proof
  simp[earlier_def] >> rpt strip_tac >>
  Cases_on ‘l1’ >> gvs[] >> Cases_on ‘t’ >> gvs[] >>
  Cases_on ‘l2’ >> gvs[]
QED

(* MAIN (R2): episode 0 POSTs x=1, is answered and closed; episode 1 is
   accepted on the SAME fd 4, GETs x and is answered 404.  The POST's
   response was written before episode 1 read anything, so real time puts
   it first: kv_safe2 rejects the stale read *)
Theorem broken_stale_across_reuse:
  starts_with stale2 io ⇒ ¬kv_safe2 io
Proof
  rw[kv_safe2_def] >>
  qexistsl [‘stale2’, ‘rss2’, ‘λj. []’] >> simp[no_full_nil] >>
  conj_tac
  >- (gen_tac >> Cases_on ‘j = 0’ >- (simp[] >> EVAL_TAC) >>
      Cases_on ‘j = 1’ >- (simp[] >> EVAL_TAC) >>
      simp[brequests_nil] >> simp[ep_read_def] >> rw[] >>
      pop_assum mp_tac >> EVAL_TAC >> simp[]) >>
  gen_tac >> CCONTR_TAC >> fs[] >>
  ‘order = [(0,0); (1,0)] ∨ order = [(1,0); (0,0)]’
    by (irule order_two2 >> qexists_tac ‘rss2’ >> rw[])
  >- (qpat_x_assum ‘order = _’ SUBST_ALL_TAC >>
      qpat_x_assum ‘∀j. ep_written _ _ ≼ _’ (qspec_then ‘1’ mp_tac) >> EVAL_TAC) >>
  qpat_x_assum ‘order = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘∀x y. _’ (qspecl_then [‘(0,0)’, ‘(1,0)’] mp_tac) >>
  simp[earlier_two] >>
  simp[precedes2_def] >> qexists_tac ‘TAKE 5 stale2’ >> EVAL_TAC
QED
