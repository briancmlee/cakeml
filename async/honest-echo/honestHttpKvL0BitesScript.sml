(*
  Bites for honestHttpKvL0Spec (before any proof, as for echo): the draft
  statements rule out plausible bugs on the raw L0 trace, and are not
  vacuous.  Everything here is proved.

  HTTP (http_safe_l0):
   - answering a previous connection's request on the connection that
     reuses its fd (http_bite_reuse_leak);
   - answering before the request has been read (http_bite_early);
   - non-vacuity: two clients on the same reused fd, each answered
     (http_ideal_safe).
  KV (kv_safe_l0):
   - answering a previous connection's request on the connection that
     reuses its fd (kv_bite_reuse_leak);
   - a stale read across connections: c1's POST of x is answered, only
     then is c2's GET of x read, and it gets 404 (kv_bite_stale);
   - non-vacuity: two GETs on the same reused fd, each answered 404
     (kv_ideal_safe).

  The local helpers marked COPY are verbatim copies of local lemmas of
  HttpSpecBodies2Bite / HttpKvSpecBite (recorded per the temporary-copy
  rule).
*)
Theory honestHttpKvL0Bites
Ancestors
  llist rich_list ffi honestL0 honestEchoL0Spec honestEchoL0Bites honestHttpKvL0Spec
  HttpSpecBodies HttpSpecBodiesBite HttpKvSpec HttpKvSpecBite HttpSpec Marshalling
Libs
  preamble

Overload R[local] = “brequests [rp]”
Overload P[local] = “bresponses site [rp]”

(* ------------------------------------------------------------------------
   Helpers (COPY)
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

Theorem no_full_brequest_NIL[local]:
  no_full_brequest []
Proof
  rw[no_full_brequest_def, IS_PREFIX_NIL] >> Cases_on ‘r’ >>
  simp[brequests_def, print_brequest_def, bytes_def]
QED

Theorem brequests_NIL[local]:
  brequests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[brequests_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_brequest_def]
QED

(* ------------------------------------------------------------------------
   HTTP
   ------------------------------------------------------------------------ *)

(* Read rp on fd 4, close fd 4 without answering, accept a new connection
   that reuses fd 4, and answer rp on it *)
Theorem http_bite_reuse_leak:
  LPREFIX (fromList [acc_ev 3w 4w; recv_ev 4w R; close_ev 4w; acc_ev 3w 4w;
                     send_ev 4w P (LENGTH P)]) io ⇒
  ¬http_safe_l0 site io
Proof
  rw[http_safe_l0_def] >>
  qexistsl [‘[acc_ev 3w 4w; recv_ev 4w R; close_ev 4w; acc_ev 3w 4w; send_ev 4w P (LENGTH P)]’,
            ‘1’, ‘[]’, ‘[]’] >> simp[no_full_brequest_NIL] >>
  simp[l0_sent_def, l0_read_def, l0_accepted_def, l0_ep_events_def,
       alistTheory.ADELKEY_def] >> EVAL_TAC
QED

(* Answer before the request has been read *)
Theorem http_bite_early:
  LPREFIX (fromList [acc_ev 3w 4w; send_ev 4w P (LENGTH P)]) io ⇒
  ¬http_safe_l0 site io
Proof
  rw[http_safe_l0_def] >>
  qexistsl [‘[acc_ev 3w 4w; send_ev 4w P (LENGTH P)]’, ‘0’, ‘[]’, ‘[]’] >> simp[no_full_brequest_NIL] >>
  simp[l0_sent_def, l0_read_def, l0_accepted_def, l0_ep_events_def,
       alistTheory.ADELKEY_def] >> EVAL_TAC
QED

(* Non-vacuity: two clients on the same reused fd, each sends rp and is
   answered, in full, by the kernel *)
Definition http_ideal_def:
  http_ideal =
    [acc_ev 3w 4w; recv_ev 4w R; send_ev 4w P (LENGTH P); close_ev 4w;
     acc_ev 3w 4w; recv_ev 4w R; send_ev 4w P (LENGTH P)]
End

Theorem bytes_split[local]: (* COPY *)
  ∀s p rest. bytes p ++ rest = bytes s ⇒ ∃s'. s = p ++ s' ∧ rest = bytes s'
Proof
  simp[bytes_def] >> Induct_on ‘p’ >> rw[] >>
  Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem brequests_CONS[local]: (* COPY *)
  brequests [] = [] ∧
  brequests (r :: rs) = bytes (print_brequest r) ++ brequests rs
Proof
  simp[brequests_def, bytes_def]
QED

Theorem brequests_of_one[local]: (* COPY *)
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
  fs[bytes_def, APPEND_eq_NIL, brequests_NIL]
QED

Theorem valid_rp[local]:
  valid_brequest rp
Proof
  EVAL_TAC
QED

Theorem safe_rp[local]: (* COPY *)
  EVERY valid_brequest rs ∧ xb = brequests rs ++ rest ∧ no_full_brequest rest ∧
  (xb = [] ∧ wb = [] ∨ xb = R ∧ (wb = [] ∨ wb = P)) ⇒
  wb ≼ bresponses site rs
Proof
  rw[] >> simp[] >>
  ‘rs = [] ∨ rs = [rp] ∧ rest = []’ by metis_tac[brequests_of_one, valid_rp] >>
  gvs[brequests_CONS] >>
  fs[no_full_brequest_def] >> metis_tac[valid_rp, IS_PREFIX_REFL, brequests_CONS,
                                        APPEND_NIL]
QED

(* Past the accepted episodes nothing is read or sent *)
Theorem l0_beyond[local]:
  LENGTH (l0_accepted evs) ≤ j ⇒ l0_read j evs = [] ∧ l0_sent j evs = []
Proof
  simp[l0_read_def, l0_sent_def]
QED

Theorem http_ideal_cases[local]:
  n ≤ 7 ⇒
  l0_read j (TAKE n http_ideal) = [] ∧ l0_sent j (TAKE n http_ideal) = [] ∨
  l0_read j (TAKE n http_ideal) = R ∧
  (l0_sent j (TAKE n http_ideal) = [] ∨ l0_sent j (TAKE n http_ideal) = P)
Proof
  strip_tac >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7’ by simp[] >>
  (Cases_on ‘j < 2’
   >- (‘j = 0 ∨ j = 1’ by simp[] >> gvs[http_ideal_def] >>
       simp[l0_sent_def, l0_read_def, l0_accepted_def, l0_ep_events_def,
            alistTheory.ADELKEY_def] >> EVAL_TAC) >>
   disj1_tac >>
   ‘LENGTH (l0_accepted (TAKE n http_ideal)) ≤ 2’
     by (gvs[http_ideal_def] >> simp[l0_accepted_def] >> EVAL_TAC) >>
   ‘LENGTH (l0_accepted (TAKE n http_ideal)) ≤ j’
     by (irule LESS_EQ_TRANS >> first_assum (irule_at Any) >> decide_tac) >>
   simp[l0_beyond])
QED

Theorem http_ideal_safe:
  http_safe_l0 site (fromList http_ideal)
Proof
  rw[http_safe_l0_def, LPREFIX_fromList_fromList] >>
  qpat_x_assum ‘_ ≼ http_ideal’ (strip_assume_tac o REWRITE_RULE [prefix_take]) >>
  ‘LENGTH http_ideal = 7’ by simp[http_ideal_def] >> gvs[] >>
  drule http_ideal_cases >> disch_then (qspec_then ‘j’ strip_assume_tac) >>
  irule safe_rp >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   KV
   ------------------------------------------------------------------------ *)

Theorem shuffles_NIL[local]: (* COPY *)
  shuffles xs [] = [xs]
Proof
  Cases_on ‘xs’ >> simp[shuffles_def]
QED

Theorem MEM_shuffles[local]: (* COPY *)
  ∀l. (∀x. MEM x l ⇒ p x ∨ q x) ∧ (∀x. ¬(p x ∧ q x)) ⇒
      MEM l (shuffles (FILTER p l) (FILTER q l))
Proof
  Induct >> simp[shuffles_def] >> rpt strip_tac >>
  ‘MEM l (shuffles (FILTER p l) (FILTER q l))’ by metis_tac[] >>
  Cases_on ‘p h’
  >- (‘¬q h’ by metis_tac[] >> simp[] >>
      Cases_on ‘FILTER q l’ >> gvs[shuffles_NIL, shuffles_def, MEM_MAP]) >>
  ‘q h’ by metis_tac[] >> simp[] >>
  Cases_on ‘FILTER p l’ >> gvs[shuffles_def, MEM_MAP]
QED

Theorem FILTER_conn[local]: (* COPY *)
  ∀l ns. MAP SND (FILTER (λx. FST x = c) l) = ns ⇒
         FILTER (λx. FST x = c) l = MAP (λi. (c, i)) ns
Proof
  Induct >> simp[] >> Cases >> rw[] >> simp[]
QED

(* COPY of HttpKvSpecBite's orders_two, for episodes (num) *)
Theorem orders_two_l0[local]:
  is_order_l0 rss order ∧ ca ≠ cb ∧ (∀c. c ≠ ca ∧ c ≠ cb ⇒ rss c = []) ⇒
  MEM order (shuffles (MAP (λi. (ca, i)) (COUNT_LIST (LENGTH (rss ca))))
                      (MAP (λi. (cb, i)) (COUNT_LIST (LENGTH (rss cb)))))
Proof
  rw[is_order_l0_def] >>
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

Theorem earlier_CONS[local]: (* COPY *)
  (earlier [] x y ⇔ F) ∧
  (earlier (h :: t) x y ⇔ (h = x ∧ MEM y t) ∨ earlier t x y)
Proof
  rw[earlier_def] >> eq_tac >> rw[]
  >- (Cases_on ‘l1’ >> gvs[] >> metis_tac[MEM_APPEND, MEM])
  >- (gvs[MEM_SPLIT] >> qexistsl [‘[]’, ‘l1’, ‘l2’] >> simp[])
  >- (qexistsl [‘h :: l1’, ‘l2’, ‘l3’] >> simp[])
QED

Overload G[local] = “brequests [gx]”
Overload X[local] = “brequests [x1]”

(* Read c1's POST of x on fd 4, close fd 4 without answering, accept c2 on
   fd 4, and answer the POST on it *)
Overload leak_l0 =
  “[acc_ev 3w 4w; recv_ev 4w X; close_ev 4w; acc_ev 3w 4w;
    send_ev 4w done (LENGTH done)]”

Theorem kv_bite_reuse_leak:
  LPREFIX (fromList leak_l0) io ⇒ ¬kv_safe_l0 io
Proof
  rw[kv_safe_l0_def] >>
  ‘LENGTH (l0_accepted leak_l0) = 2’ by (simp[l0_accepted_def] >> EVAL_TAC) >>
  qexistsl [‘leak_l0’, ‘λj. if j = 0 then [x1] else []’, ‘K []’] >>
  simp[no_full_brequest_NIL] >> conj_tac
  >- (gen_tac >> Cases_on ‘j < 2’
      >- (‘j = 0 ∨ j = 1’ by simp[] >> simp[] >> TRY (conj_tac >- EVAL_TAC) >>
          simp[l0_read_def, l0_accepted_def, l0_ep_events_def,
               alistTheory.ADELKEY_def] >> EVAL_TAC) >>
      simp[l0_beyond, brequests_CONS]) >>
  gen_tac >> CCONTR_TAC >> fs[] >>
  drule orders_two_l0 >> disch_then (qspecl_then [‘0’, ‘1’] mp_tac) >>
  impl_tac >- rw[] >> CONV_TAC (LAND_CONV EVAL) >> strip_tac >> gvs[] >>
  qpat_x_assum ‘∀j. _ ≼ _’ (qspec_then ‘1’ mp_tac) >>
  simp[l0_sent_def, l0_accepted_def, l0_ep_events_def,
       alistTheory.ADELKEY_def] >> EVAL_TAC
QED

(* A stale read across connections: c1's POST of x is answered, c1 is
   closed, c2 is accepted on the same fd, its GET of x is read and gets 404 *)
Overload stale_l0 =
  “[acc_ev 3w 4w; recv_ev 4w X; send_ev 4w done (LENGTH done); close_ev 4w;
    acc_ev 3w 4w; recv_ev 4w G; send_ev 4w missing (LENGTH missing)]”

Theorem kv_bite_stale:
  LPREFIX (fromList stale_l0) io ⇒ ¬kv_safe_l0 io
Proof
  rw[kv_safe_l0_def] >>
  ‘LENGTH (l0_accepted stale_l0) = 2’ by (simp[l0_accepted_def] >> EVAL_TAC) >>
  qexistsl [‘stale_l0’, ‘λj. if j = 0 then [x1] else if j = 1 then [gx] else []’,
            ‘K []’] >>
  simp[no_full_brequest_NIL] >> conj_tac
  >- (gen_tac >> Cases_on ‘j < 2’
      >- (‘j = 0 ∨ j = 1’ by simp[] >> simp[] >> conj_tac >- EVAL_TAC >>
          simp[l0_read_def, l0_accepted_def, l0_ep_events_def,
               alistTheory.ADELKEY_def] >> EVAL_TAC) >>
      simp[l0_beyond, brequests_CONS]) >>
  gen_tac >> CCONTR_TAC >> fs[] >>
  drule orders_two_l0 >> disch_then (qspecl_then [‘0’, ‘1’] mp_tac) >>
  impl_tac >- rw[] >> CONV_TAC (LAND_CONV EVAL) >> strip_tac >> gvs[] >>
  (* the order where the GET sees the POST: c2's reply is wrong *)
  TRY (qpat_x_assum ‘∀j. _ ≼ _’ (qspec_then ‘1’ mp_tac) >>
       simp[l0_sent_def, l0_accepted_def, l0_ep_events_def,
            alistTheory.ADELKEY_def] >> EVAL_TAC >> NO_TAC) >>
  (* the order where the GET goes first: it breaks real time *)
  qpat_x_assum ‘∀x y. _’ (qspecl_then [‘(0, 0)’, ‘(1, 0)’] mp_tac) >>
  simp[earlier_CONS, precedes_l0_def] >>
  qexists_tac ‘TAKE 3 stale_l0’ >> simp[] >>
  simp[l0_read_def, l0_sent_def, l0_accepted_def, l0_ep_events_def,
       alistTheory.ADELKEY_def] >> EVAL_TAC
QED

(* Non-vacuity: two clients on the same reused fd, each GETs x and is
   answered 404, in full, by the kernel *)
Definition kv_ideal_def:
  kv_ideal =
    [acc_ev 3w 4w; recv_ev 4w G; send_ev 4w missing (LENGTH missing); close_ev 4w;
     acc_ev 3w 4w; recv_ev 4w G; send_ev 4w missing (LENGTH missing)]
End

Theorem kv_ideal_tab[local]:
  n ≤ 7 ⇒
  l0_read j (TAKE n kv_ideal) =
    (if j = 0 ∧ 2 ≤ n ∨ j = 1 ∧ 6 ≤ n then G else []) ∧
  l0_sent j (TAKE n kv_ideal) =
    (if j = 0 ∧ 3 ≤ n ∨ j = 1 ∧ 7 ≤ n then missing else [])
Proof
  strip_tac >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7’ by simp[] >>
  (Cases_on ‘j < 2’
   >- (‘j = 0 ∨ j = 1’ by simp[] >> gvs[kv_ideal_def] >>
       simp[l0_sent_def, l0_read_def, l0_accepted_def, l0_ep_events_def,
            alistTheory.ADELKEY_def] >> EVAL_TAC) >>
   ‘LENGTH (l0_accepted (TAKE n kv_ideal)) ≤ 2’
     by (gvs[kv_ideal_def] >> simp[l0_accepted_def] >> EVAL_TAC) >>
   ‘LENGTH (l0_accepted (TAKE n kv_ideal)) ≤ j’
     by (irule LESS_EQ_TRANS >> first_assum (irule_at Any) >> decide_tac) >>
   simp[l0_beyond])
QED

Theorem rss_nil[local]:
  [] = brequests rs ++ rest ⇒ rs = []
Proof
  rw[] >> gvs[brequests_NIL]
QED

Theorem rss_g[local]:
  EVERY valid_brequest rs ∧ no_full_brequest rest ∧ G = brequests rs ++ rest ⇒
  rs = [gx]
Proof
  rw[] >> ‘valid_brequest gx’ by EVAL_TAC >>
  ‘rs = [] ∨ rs = [gx] ∧ rest = []’ by metis_tac[brequests_of_one] >>
  gvs[brequests_CONS, no_full_brequest_def] >>
  metis_tac[IS_PREFIX_REFL, brequests_CONS, APPEND_NIL]
QED

(* The second GET's reply cannot precede the first GET's read *)
Theorem kv_ideal_rt[local]:
  n ≤ 7 ∧ replies rss order 1 = [NotFound] ∧
  precedes_l0 rss order (TAKE n kv_ideal) (1, 0) (0, 0) ⇒ F
Proof
  rpt strip_tac >> gvs[precedes_l0_def] >>
  qpat_x_assum ‘_ ≼ TAKE n kv_ideal’
    (strip_assume_tac o REWRITE_RULE [prefix_take]) >>
  ‘LENGTH kv_ideal = 7’ by simp[kv_ideal_def] >>
  ‘n' ≤ n ∧ n' ≤ 7’ by gvs[LENGTH_TAKE_EQ] >>
  gvs[TAKE_TAKE] >>
  qspecl_then [‘n'’, ‘1’] mp_tac (Q.GENL [‘n’, ‘j’] kv_ideal_tab) >>
  qspecl_then [‘n'’, ‘0’] mp_tac (Q.GENL [‘n’, ‘j’] kv_ideal_tab) >>
  simp[] >> rpt strip_tac >> fs[] >>
  Cases_on ‘7 ≤ n'’ >> fs[]
  >- (qpat_x_assum ‘_ ≼ _’ mp_tac >> EVAL_TAC) >>
  qpat_x_assum ‘missing = []’ mp_tac >> EVAL_TAC
QED

Theorem kv_ideal_safe:
  kv_safe_l0 (fromList kv_ideal)
Proof
  rw[kv_safe_l0_def, LPREFIX_fromList_fromList] >>
  qpat_x_assum ‘_ ≼ kv_ideal’ (strip_assume_tac o REWRITE_RULE [prefix_take]) >>
  ‘LENGTH kv_ideal = 7’ by simp[kv_ideal_def] >> gvs[] >>
  ‘rss = λj. if j = 0 ∧ 2 ≤ n ∨ j = 1 ∧ 6 ≤ n then [gx] else []’
    by (simp[FUN_EQ_THM] >> gen_tac >>
        first_x_assum (qspec_then ‘j’ strip_assume_tac) >>
        qspecl_then [‘n’, ‘j’] mp_tac (GEN_ALL kv_ideal_tab) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_x_assum ‘l0_read _ _ = _ ++ _’ mp_tac >> asm_rewrite_tac[] >>
        Cases_on ‘j = 0 ∧ 2 ≤ n ∨ j = 1 ∧ 6 ≤ n’ >> asm_rewrite_tac[] >>
        metis_tac[rss_nil, rss_g]) >>
  qpat_x_assum ‘∀j. _’ kall_tac >>
  ‘∀j. l0_sent j (TAKE n kv_ideal) =
       if j = 0 ∧ 3 ≤ n ∨ j = 1 ∧ 7 ≤ n then missing else []’
    by metis_tac[kv_ideal_tab] >>
  qexists_tac ‘(if 2 ≤ n then [(0, 0)] else []) ++ (if 6 ≤ n then [(1, 0)] else [])’ >>
  ‘n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7’ by simp[] >>
  (gvs[] >> rpt conj_tac >>
   TRY (rw[is_order_l0_def] >> Cases_on ‘j = 0’ >> Cases_on ‘j = 1’ >> gvs[] >>
        EVAL_TAC >> NO_TAC) >>
   TRY (simp[] >> rpt strip_tac >> gvs[earlier_CONS] >>
        drule_at (Pos last) kv_ideal_rt >> simp[] >> EVAL_TAC >> NO_TAC) >>
   gen_tac >> Cases_on ‘j = 0’ >> Cases_on ‘j = 1’ >> gvs[] >> EVAL_TAC)
QED
