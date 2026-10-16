(*
  KvSpec bites: the key-value statement rules out plausible bugs, and
  its assumptions are satisfiable.  Everything here is proved.  DRAFT, for
  the user's decision.

  - A server that loses a write (a connection does not see its own POST)
    violates safety.
  - A server with a store per connection violates safety, in every order:
    two clients each POST one key and then GET the other's, and both get
    404 (the "store buffer" pattern).  Not even sequentially consistent.
  - A server that serves a stale read violates safety: A's POST is
    answered, then B connects and its GET gets 404.  This trace IS
    sequentially consistent (stale_read_sc, for sequential consistency
    as kv_safe_sc below); only real time rules it out.
  - A server that never answers violates liveness.
  - Non-vacuity: in a fair world where two clients send a POST and a GET
    of the same key, an interleaved trace (read both, answer both, the
    GET seeing the POST) is safe and live.
*)
Theory KvSpecBite
Ancestors
  KvSpec HttpSpec HttpSpecBite HttpGetSpec HttpGetSpecBite
  EchoSpec EchoSpecBite socketWorld socketFair llist
  rich_list Marshalling ASCIInumbers
Libs
  preamble

Definition kpost_def:
  kpost k v = Req "POST" k "1.0" [("Content-Length", toString (LENGTH v))] v
End

Definition kget_def:
  kget k = Req "GET" k "1.0" [] ""
End

(* Sequential consistency: kv_safe without real time *)
Definition kv_safe_sc_def:
  kv_safe_sc io ⇔
    ∀evs rss rests.
      LPREFIX (fromList evs) io ∧
      (∀c. EVERY valid_brequest (rss c) ∧ no_full_brequest (rests c) ∧
           bytes_read_from c evs = brequests (rss c) ++ rests c) ⇒
      ∃order. is_order rss order ∧
              ∀c. bytes_written_to c evs ≼ reply_bytes (replies rss order c)
End

(* ------------------------------------------------------------------------
   Reading requests back is unique
   ------------------------------------------------------------------------ *)

Theorem bytes_prefix[local]:
  ∀p q x y. bytes p ++ x = bytes q ++ y ⇒ (∃z. q = p ++ z) ∨ (∃z. p = q ++ z)
Proof
  Induct >> simp[bytes_def] >> Cases_on ‘q’ >> simp[] >> rpt gen_tac >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >>
  simp[ORD_11] >> strip_tac >> gvs[] >>
  fs[bytes_def] >> metis_tac[]
QED

Theorem brequests_CONS[local]:
  brequests [] = [] ∧
  brequests (r :: rs) = bytes (print_brequest r) ++ brequests rs
Proof
  simp[brequests_def, bytes_def]
QED

Theorem print_brequest_NIL[local]:
  print_brequest r ≠ []
Proof
  Cases_on ‘r’ >> simp[print_brequest_def]
QED

Theorem brequests_NIL[local]:
  brequests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[brequests_CONS, bytes_def, print_brequest_NIL]
QED

Theorem bytes_APPEND[local]:
  bytes (a ++ b) = bytes a ++ bytes b
Proof
  simp[bytes_def]
QED

Theorem no_full_brequest_CONS[local]:
  valid_brequest r ⇒ ¬no_full_brequest (brequests (r :: rs) ++ x)
Proof
  rw[no_full_brequest_def] >> qexists_tac ‘r’ >>
  simp[brequests_CONS, IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC, APPEND_NIL]
QED

(* MAIN (framing): what the server has read from a connection splits in
   only one way into complete requests and a partial one *)
Theorem parse_unique:
  ∀rs1 rs2 x1 x2.
    EVERY valid_brequest rs1 ∧ EVERY valid_brequest rs2 ∧
    no_full_brequest x1 ∧ no_full_brequest x2 ∧
    brequests rs1 ++ x1 = brequests rs2 ++ x2 ⇒ rs1 = rs2 ∧ x1 = x2
Proof
  Induct >> rpt gen_tac >> Cases_on ‘rs2’ >> strip_tac
  >- fs[brequests_CONS]
  >- (qpat_x_assum ‘_ = _’
        (assume_tac o REWRITE_RULE [cj 1 brequests_CONS, APPEND]) >>
      metis_tac[no_full_brequest_CONS, EVERY_DEF])
  >- (qpat_x_assum ‘_ = _’
        (assume_tac o REWRITE_RULE [cj 1 brequests_CONS, APPEND_NIL, APPEND]) >>
      metis_tac[no_full_brequest_CONS, EVERY_DEF]) >>
  fs[brequests_CONS] >>
  ‘h = h'’
    by (qpat_x_assum ‘_ ++ _ = _ ++ _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        disch_then (strip_assume_tac o MATCH_MP bytes_prefix) >>
        gvs[bytes_APPEND] >> metis_tac[print_brequest_unique, APPEND_NIL]) >>
  gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem no_full_brequest_NIL[local]:
  no_full_brequest []
Proof
  rw[no_full_brequest_def, IS_PREFIX_NIL] >> Cases_on ‘r’ >>
  simp[brequests_def, print_brequest_def, bytes_def]
QED

(* To know rss at a point of a trace, it suffices to read the trace *)
Theorem parse_known[local]:
  (∀c. EVERY valid_brequest (rss c) ∧ no_full_brequest (rests c) ∧
       bytes_read_from c evs = brequests (rss c) ++ rests c) ∧
  (∀c. EVERY valid_brequest (R c) ∧ bytes_read_from c evs = brequests (R c)) ⇒
  rss = R
Proof
  rw[FUN_EQ_THM] >>
  metis_tac[parse_unique, no_full_brequest_NIL, APPEND_NIL]
QED

(* ------------------------------------------------------------------------
   Orders of two connections' requests are their shuffles
   ------------------------------------------------------------------------ *)

Definition shuffles_def:
  shuffles [] ys = [ys] ∧
  shuffles (x::xs) [] = [x::xs] ∧
  shuffles (x::xs) (y::ys) =
    MAP (CONS x) (shuffles xs (y::ys)) ++ MAP (CONS y) (shuffles (x::xs) ys)
End

Theorem shuffles_NIL[local]:
  shuffles xs [] = [xs]
Proof
  Cases_on ‘xs’ >> simp[shuffles_def]
QED

Theorem MEM_shuffles[local]:
  ∀l. (∀x. MEM x l ⇒ P x ∨ Q x) ∧ (∀x. ¬(P x ∧ Q x)) ⇒
      MEM l (shuffles (FILTER P l) (FILTER Q l))
Proof
  Induct >> simp[shuffles_def] >> rpt strip_tac >>
  ‘MEM l (shuffles (FILTER P l) (FILTER Q l))’ by metis_tac[] >>
  Cases_on ‘P h’
  >- (‘¬Q h’ by metis_tac[] >> simp[] >>
      Cases_on ‘FILTER Q l’ >> gvs[shuffles_NIL, shuffles_def, MEM_MAP]) >>
  ‘Q h’ by metis_tac[] >> simp[] >>
  Cases_on ‘FILTER P l’ >> gvs[shuffles_def, MEM_MAP]
QED

Theorem FILTER_conn[local]:
  ∀l ns. MAP SND (FILTER (λx. FST x = c) l) = ns ⇒
         FILTER (λx. FST x = c) l = MAP (λi. (c, i)) ns
Proof
  Induct >> simp[] >> Cases >> rw[] >> simp[]
QED

(* MAIN: with requests on two connections only, an order is a shuffle of
   the two connections' requests *)
Theorem orders_two:
  is_order rss order ∧ ca ≠ cb ∧ (∀c. c ≠ ca ∧ c ≠ cb ⇒ rss c = []) ⇒
  MEM order (shuffles (MAP (λi. (ca, i)) (COUNT_LIST (LENGTH (rss ca))))
                      (MAP (λi. (cb, i)) (COUNT_LIST (LENGTH (rss cb)))))
Proof
  rw[is_order_def] >>
  ‘∀c. FILTER (λx. FST x = c) order =
       MAP (λi. (c, i)) (COUNT_LIST (LENGTH (rss c)))’ by metis_tac[FILTER_conn] >>
  ‘∀x. MEM x order ⇒ FST x = ca ∨ FST x = cb’
    by (rpt strip_tac >> CCONTR_TAC >>
        ‘rss (FST x) = []’ by metis_tac[] >>
        qpat_x_assum ‘∀c. FILTER _ _ = _’ (qspec_then ‘FST x’ mp_tac) >>
        simp[COUNT_LIST_def, FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  qspecl_then [‘λx. FST x = cb’, ‘λx. FST x = ca’, ‘order’] mp_tac
    (GEN_ALL MEM_shuffles) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  qpat_x_assum ‘∀c. FILTER _ _ = _’ (fn th => simp[th])
QED

Theorem earlier_CONS[local]:
  (earlier [] x y ⇔ F) ∧
  (earlier (h :: t) x y ⇔ (h = x ∧ MEM y t) ∨ earlier t x y)
Proof
  rw[earlier_def] >> eq_tac >> rw[]
  >- (Cases_on ‘l1’ >> gvs[] >> metis_tac[MEM_APPEND, MEM])
  >- (gvs[MEM_SPLIT] >> qexistsl [‘[]’, ‘l1’, ‘l2’] >> simp[])
  >- (qexistsl [‘h :: l1’, ‘l2’, ‘l3’] >> simp[])
QED

Theorem prefix_CONS[local]:
  evs ≼ h :: t ⇔ evs = [] ∨ ∃r. evs = h :: r ∧ r ≼ t
Proof
  Cases_on ‘evs’ >> simp[]
QED

Theorem prefix_NIL[local]:
  evs ≼ [] ⇔ evs = []
Proof
  Cases_on ‘evs’ >> simp[]
QED

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

(* ------------------------------------------------------------------------
   Broken servers violate safety
   ------------------------------------------------------------------------ *)

Overload x1 = “kpost "/x" "1"”
Overload y1 = “kpost "/y" "1"”
Overload gx = “kget "/x"”
Overload gy = “kget "/y"”
Overload done = “reply_bytes [Ok ""]”
Overload missing = “reply_bytes [NotFound]”

(* MAIN (bite): losing a write.  c1 POSTs x, then GETs x, and gets 404. *)
Theorem broken_loses_write:
  starts_with [rd c1 (brequests [x1; gx]) 100;
               wr c1 (reply_bytes [Ok ""; NotFound])] io ⇒
  ¬kv_safe io
Proof
  rw[kv_safe_def] >>
  qexistsl [‘[rd c1 (brequests [x1; gx]) 100;
              wr c1 (reply_bytes [Ok ""; NotFound])]’,
            ‘λc. if c = c1 then [x1; gx] else []’, ‘K []’] >>
  simp[no_full_brequest_NIL] >> conj_tac
  >- (rw[] >> EVAL_TAC >> rw[] >> fs[]) >>
  gen_tac >> CCONTR_TAC >> fs[] >>
  drule orders_two >> disch_then (qspecl_then [‘c1’, ‘c2’] mp_tac) >>
  impl_tac >- rw[] >> CONV_TAC (LAND_CONV EVAL) >> strip_tac >> gvs[] >>
  qpat_x_assum ‘∀c. _’ (qspec_then ‘c1’ mp_tac) >> EVAL_TAC
QED

(* MAIN (bite): a store per connection.  c1 POSTs x and GETs y, c2 POSTs y
   and GETs x, and both GETs get 404.  No order explains this (whichever
   GET comes last sees both POSTs): not even sequentially consistent. *)
Overload dekker =
  “[rd c1 (brequests [x1; gy]) 100; rd c2 (brequests [y1; gx]) 100;
    wr c1 (reply_bytes [Ok ""; NotFound]); wr c2 (reply_bytes [Ok ""; NotFound])]”

Theorem broken_store_per_connection:
  starts_with dekker io ⇒ ¬kv_safe_sc io
Proof
  rw[kv_safe_sc_def] >>
  qexistsl [‘dekker’, ‘λc. if c = c1 then [x1; gy] else if c = c2 then [y1; gx] else []’,
            ‘K []’] >>
  simp[no_full_brequest_NIL] >> conj_tac
  >- (rw[] >> EVAL_TAC >> rw[] >> fs[]) >>
  gen_tac >> CCONTR_TAC >> fs[] >>
  drule orders_two >> disch_then (qspecl_then [‘c1’, ‘c2’] mp_tac) >>
  impl_tac >- rw[] >> CONV_TAC (LAND_CONV EVAL) >> strip_tac >> gvs[] >>
  first_assum (qspec_then ‘c1’ mp_tac) >>
  first_x_assum (qspec_then ‘c2’ mp_tac) >> EVAL_TAC
QED

(* Linearizability implies sequential consistency *)
Theorem kv_safe_sc:
  kv_safe io ⇒ kv_safe_sc io
Proof
  rw[kv_safe_def, kv_safe_sc_def] >> first_x_assum drule_all >> metis_tac[]
QED

(* MAIN (bite): a stale read.  c1's POST of x is answered; only then is
   c2's GET of x read, and it gets 404. *)
Overload stale =
  “[rd c1 (brequests [x1]) 100; wr c1 done;
    rd c2 (brequests [gx]) 100; wr c2 missing]”

Theorem broken_stale_read:
  starts_with stale io ⇒ ¬kv_safe io
Proof
  rw[kv_safe_def] >>
  qexistsl [‘stale’, ‘λc. if c = c1 then [x1] else if c = c2 then [gx] else []’,
            ‘K []’] >>
  simp[no_full_brequest_NIL] >> conj_tac
  >- (rw[] >> EVAL_TAC >> rw[] >> fs[]) >>
  gen_tac >> CCONTR_TAC >> fs[] >>
  drule orders_two >> disch_then (qspecl_then [‘c1’, ‘c2’] mp_tac) >>
  impl_tac >- rw[] >> CONV_TAC (LAND_CONV EVAL) >> strip_tac >> gvs[] >>
  TRY (qpat_x_assum ‘∀c. _’ (qspec_then ‘c2’ mp_tac) >> EVAL_TAC >> NO_TAC) >>
  qpat_x_assum ‘∀x y. _’ (qspecl_then [‘(c1, 0)’, ‘(c2, 0)’] mp_tac) >>
  simp[earlier_CONS, precedes_def] >>
  qexists_tac ‘[rd c1 (brequests [x1]) 100; wr c1 done]’ >> EVAL_TAC
QED

(* The stale read is sequentially consistent: c2's GET goes first *)
Theorem stale_read_sc:
  kv_safe_sc (fromList stale)
Proof
  rw[kv_safe_sc_def, LPREFIX_fromList_fromList] >>
  ‘rss = λc. if c = c1 ∧ bytes_read_from c1 evs ≠ [] then [x1] else
             if c = c2 ∧ bytes_read_from c2 evs ≠ [] then [gx] else []’
    by (irule parse_known >> qexistsl [‘evs’, ‘rests’] >>
        reverse conj_tac >- first_assum ACCEPT_TAC >>
        qpat_x_assum ‘∀c. _’ kall_tac >> gen_tac >>
        qpat_x_assum ‘evs ≼ _’ mp_tac >> simp[prefix_CONS] >> strip_tac >>
        gvs[] >> CONV_TAC EVAL >> rw[] >> gvs[] >> EVAL_TAC) >>
  qpat_x_assum ‘∀c. _’ kall_tac >>
  qexists_tac ‘(if bytes_read_from c2 evs ≠ [] then [(c2, 0)] else []) ++
               (if bytes_read_from c1 evs ≠ [] then [(c1, 0)] else [])’ >>
  qpat_x_assum ‘rss = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘evs ≼ _’
    (strip_assume_tac o SIMP_RULE pure_ss [prefix_CONS, prefix_NIL]) >>
  rpt BasicProvers.VAR_EQ_TAC >> CONV_TAC EVAL >> rw[] >> gvs[] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   A server that never answers violates liveness
   ------------------------------------------------------------------------ *)

Theorem sent_upto_one_client[local]:
  sent_upto c n (one_client bs) = if n = 0 ∨ c ≠ 4w then [] else bs
Proof
  Cases_on ‘n’ >> simp[sent_upto_def, arrivals_upto_def, one_client_def] >>
  Cases_on ‘n'’ >> simp[arrivals_upto_def] >> rw[]
QED

Theorem broken_never_answers_kv:
  (∀evs. starts_with evs io ⇒ bytes_written_to 4w evs = []) ⇒
  ¬kv_live (one_client (brequests [gx])) io
Proof
  rw[kv_live_def] >> qexistsl [‘4w’, ‘1’, ‘[gx]’] >>
  simp[sent_upto_one_client] >> conj_tac >- EVAL_TAC >>
  rw[] >> Cases_on ‘LPREFIX (fromList evs) io’ >> simp[] >> res_tac >>
  simp[] >> Cases_on ‘ans’ >> gvs[reply_bytes_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_response_def]
QED

(* ------------------------------------------------------------------------
   Non-vacuity: two clients, one POSTs x, the other GETs it
   ------------------------------------------------------------------------ *)

Definition two_clients_def:
  two_clients bs1 bs2 =
    <| listeners := [(3w, [])]; conns := [];
       sched := [|[Connect 3w 4w; Data 4w bs1; Connect 3w 5w; Data 5w bs2]|] |>
End

Theorem ticks_quiet[local]:
  s.sched = [||] ⇒ ticks n s = s
Proof
  qid_spec_tac ‘s’ >> Induct_on ‘n’ >> rw[ticks_def] >>
  ‘tick s = s’ by simp[tick_def] >> simp[]
QED

Theorem two_clients_sched_wf:
  sched_wf (two_clients bs1 bs2)
Proof
  rw [sched_wf_def] \\ Cases_on ‘n’
  >- simp [ticks_def, next_step_def, two_clients_def, step_ok_def,
           arrival_ok_def, deliver1_def, is_listener_def, is_conn_def,
           AFUPDKEY_def, empty_conn_def]
  \\ ‘(tick (two_clients bs1 bs2)).sched = [||]’
    by simp [tick_def, two_clients_def, deliver_sched]
  \\ simp [ticks_def, ticks_quiet, next_step_def, step_ok_def]
QED

Theorem sent_upto_two_clients[local]:
  sent_upto c n (two_clients bs1 bs2) =
    if n = 0 then [] else if c = 4w then bs1 else if c = 5w then bs2 else []
Proof
  Cases_on ‘n’ >> simp[sent_upto_def, arrivals_upto_def, two_clients_def] >>
  rename1 ‘arrivals_upto m’ >> Cases_on ‘m’ >> simp[arrivals_upto_def] >>
  rw[] >> gvs[]
QED

Theorem print_prefix_eq[local]:
  valid_brequest a ∧ valid_brequest b ∧ print_brequest a = print_brequest b ++ z ⇒
  a = b
Proof
  strip_tac >>
  mp_tac (Q.SPECL [‘b’, ‘a’, ‘z’, ‘[]’]
            (Q.GENL [‘q1’, ‘q2’, ‘x’, ‘y’] print_brequest_unique)) >>
  simp[]
QED

Theorem brequests_of_one[local]:
  valid_brequest r ∧ EVERY valid_brequest rs ∧ brequests rs ≼ brequests [r] ⇒
  rs = [] ∨ rs = [r]
Proof
  Cases_on ‘rs’ >> rw[IS_PREFIX_APPEND] >> fs[brequests_CONS] >>
  ‘h = r’
    by (‘bytes (print_brequest h) ++ (brequests t ++ l) =
         bytes (print_brequest r) ++ []’ by fs[] >>
        drule bytes_prefix >> strip_tac >>
        gvs[bytes_APPEND] >> metis_tac[print_prefix_eq]) >>
  gvs[] >> Cases_on ‘t’ >> fs[brequests_CONS] >>
  fs[bytes_def, print_brequest_NIL]
QED

(* Both requests are read, then both answered; the GET sees the POST *)
Overload both = “[rd c1 (brequests [x1]) 100; rd c2 (brequests [gx]) 100;
                  wr c1 done; wr c2 (reply_bytes [Ok "1"])]”

Overload world2 = “two_clients (brequests [x1]) (brequests [gx])”

Theorem both_safe:
  kv_safe (fromList both)
Proof
  rw[kv_safe_def, LPREFIX_fromList_fromList] >>
  ‘rss = λc. if c = c1 ∧ bytes_read_from c1 evs ≠ [] then [x1] else
             if c = c2 ∧ bytes_read_from c2 evs ≠ [] then [gx] else []’
    by (irule parse_known >> qexistsl [‘evs’, ‘rests’] >>
        reverse conj_tac >- first_assum ACCEPT_TAC >>
        qpat_x_assum ‘∀c. _’ kall_tac >> gen_tac >>
        qpat_x_assum ‘evs ≼ _’ mp_tac >> simp[prefix_CONS] >> strip_tac >>
        gvs[] >> CONV_TAC EVAL >> rw[] >> gvs[] >> EVAL_TAC) >>
  qpat_x_assum ‘∀c. _’ kall_tac >>
  qexists_tac ‘(if bytes_read_from c1 evs ≠ [] then [(c1, 0)] else []) ++
               (if bytes_read_from c2 evs ≠ [] then [(c2, 0)] else [])’ >>
  qpat_x_assum ‘rss = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘evs ≼ _’
    (strip_assume_tac o SIMP_RULE pure_ss [prefix_CONS, prefix_NIL]) >>
  rpt BasicProvers.VAR_EQ_TAC >> CONV_TAC EVAL >> rw[] >> gvs[] >> TRY EVAL_TAC >>
  (* real time: (c1, 0) is first; (c2, 0) never precedes it *)
  TRY (qexistsl [‘[]’, ‘[]’, ‘[]’] >> simp[] >> NO_TAC) >>
  qpat_x_assum ‘precedes _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE [precedes_def]) >>
  qpat_x_assum ‘_ ≼ IO_event _ _ _ :: _’
    (strip_assume_tac o SIMP_RULE pure_ss [prefix_CONS, prefix_NIL]) >>
  rpt BasicProvers.VAR_EQ_TAC >> rpt (pop_assum mp_tac) >> EVAL_TAC
QED

Theorem both_live:
  kv_live world2 (fromList both)
Proof
  rw[kv_live_def, sent_upto_two_clients] >>
  ‘valid_brequest x1 ∧ valid_brequest gx’ by EVAL_TAC >>
  ‘rs = [] ∨ (c = c1 ∧ rs = [x1]) ∨ (c = c2 ∧ rs = [gx])’
    by (Cases_on ‘n = 0’ >> Cases_on ‘c = c1’ >> Cases_on ‘c = c2’ >>
        gvs[brequests_NIL] >> metis_tac[brequests_of_one]) >>
  gvs[]
  >- (qexists_tac ‘[]’ >> simp[reply_bytes_def, bytes_def])
  >- (qexistsl [‘both’, ‘[Ok ""]’] >> simp[LPREFIX_fromList_fromList] >> EVAL_TAC)
  >- (qexistsl [‘both’, ‘[Ok "1"]’] >> simp[LPREFIX_fromList_fromList] >> EVAL_TAC)
QED

(* MAIN (non-vacuity): a fair world with two clients exists, and in it the
   interleaved trace (read c1's POST of x, read c2's GET of x, answer
   both, the GET seeing the POST) is safe and live *)
Theorem both_trace_safe_and_live:
  server_world 3w world2 ∧ kv_safe (fromList both) ∧ kv_live world2 (fromList both)
Proof
  simp[both_safe, both_live, server_world_def, two_clients_sched_wf] >>
  simp[two_clients_def]
QED
