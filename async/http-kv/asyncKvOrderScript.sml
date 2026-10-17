(*
  Linearization by commit points, at the level of the trace.

  kv_safe's real-time condition (HttpKvSpec) follows from COMMIT POINTS:
  if every request x in the order has a position p x in the trace such
  that
   - by then, the server has read some byte of x, and
   - by then, the server has not yet written all of x's response,
  and the order is sorted by p, then the order respects real time
  (asyncKvLabel's commits_at_real_time).  This file has the definitions
  and list lemmas it needs.
*)
Theory asyncKvOrder
Ancestors
  list rich_list EchoSpec HttpSpec HttpSpecBodies HttpKvSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   Orders
   ------------------------------------------------------------------------ *)

Theorem earlier_CONS:
  (earlier [] x y ⇔ F) ∧
  (earlier (h :: t) x y ⇔ (h = x ∧ MEM y t) ∨ earlier t x y)
Proof
  rw[earlier_def] >> eq_tac >> rw[]
  >- (Cases_on ‘l1’ >> gvs[] >> metis_tac[MEM_APPEND, MEM])
  >- (gvs[MEM_SPLIT] >> qexistsl [‘[]’, ‘l1’, ‘l2’] >> simp[])
  >- (qexistsl [‘h :: l1’, ‘l2’, ‘l3’] >> simp[])
QED

Theorem earlier_total:
  ∀l. ALL_DISTINCT l ∧ MEM x l ∧ MEM y l ∧ x ≠ y ⇒
      earlier l x y ∨ earlier l y x
Proof
  Induct >> simp[earlier_CONS] >> metis_tac[]
QED

Theorem ALL_DISTINCT_conns[local]:
  ∀l. (∀c. ALL_DISTINCT (MAP SND (FILTER (λx. FST x = c) l))) ⇒ ALL_DISTINCT l
Proof
  Induct >> simp[] >> PairCases >> rpt strip_tac
  >- (first_x_assum (qspec_then ‘h0’ mp_tac) >>
      simp[MEM_MAP, MEM_FILTER] >> metis_tac[FST, SND]) >>
  first_x_assum irule >> gen_tac >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> rw[]
QED

(* MAIN: an order lists each request once *)
Theorem is_order_ALL_DISTINCT:
  is_order rss order ⇒ ALL_DISTINCT order
Proof
  rw[is_order_def] >> irule ALL_DISTINCT_conns >>
  simp[all_distinct_count_list]
QED

(* ------------------------------------------------------------------------
   Prefixes of the trace
   ------------------------------------------------------------------------ *)

Theorem prefix_TAKE[local]:
  evs1 ≼ evs ⇒ evs1 = TAKE (LENGTH evs1) evs
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_LENGTH_APPEND]
QED

Theorem TAKE_prefix_mono[local]:
  a ≤ b ⇒ TAKE a l ≼ TAKE b l
Proof
  rw[IS_PREFIX_APPEND] >> qexists_tac ‘TAKE (b - a) (DROP a l)’ >>
  simp[GSYM TAKE_SUM, TAKE_TAKE_MIN, MIN_DEF]
QED

Theorem bytes_read_from_prefix:
  evs1 ≼ evs2 ⇒ bytes_read_from c evs1 ≼ bytes_read_from c evs2
Proof
  rw[IS_PREFIX_APPEND, bytes_read_from_def] >> simp[]
QED

Theorem bytes_written_to_prefix:
  evs1 ≼ evs2 ⇒ bytes_written_to c evs1 ≼ bytes_written_to c evs2
Proof
  rw[IS_PREFIX_APPEND, bytes_written_to_def] >> simp[]
QED

(* ------------------------------------------------------------------------
   Commit points give real time
   ------------------------------------------------------------------------ *)

(* x's response is fully written by the trace evs1 *)
Definition answered_def:
  answered rss order (c, i) evs1 ⇔
    reply_bytes (TAKE (SUC i) (replies rss order c)) ≼ bytes_written_to c evs1
End

(* some byte of (d, j) has been read in the trace evs1 *)
Definition started_def:
  started rss (d, j) evs1 ⇔
    ¬(bytes_read_from d evs1 ≼ brequests (TAKE j (rss d)))
End

Theorem precedes_answered_started:
  precedes rss order evs x y ⇔
    ∃evs1. evs1 ≼ evs ∧ answered rss order x evs1 ∧ ¬started rss y evs1
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >>
  simp[precedes_def, answered_def, started_def]
QED

