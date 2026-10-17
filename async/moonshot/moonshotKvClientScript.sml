(*
  The moonshot's safety, step 1 (design/45 §4.1): the client's view of the
  KV store, and the pure trace lemma that moves KV's linearizability
  (kv_safe2) to the client.

  Both are stated over PROJECTIONS of a trace (what was read and written
  on episode j), so that they apply to whatever level the traces are at:
  EchoSpec2's version-2 events (kv_safe2 is the instance kv_safe_g ep_read
  ep_written: kv_safe2_g), or a process's raw L0 trace in the system run
  (design/45 §4.1's proof chain, step 11).

  - kv_safe_g rd wr: kv_safe2, with rd and wr for ep_read and ep_written.
  - kv_client_safe snt crd: the client observes one sequential store.
    Some prefix of what it sent on each episode (snt) took effect, in an
    order respecting real time, and what it read (crd) is a prefix of
    those requests' replies.  Real time is precedes_g with the roles
    swapped: the client had READ all of x's reply before it SENT any byte
    of y.
  - kv_client_view_safe: if, at every instant, per paired episode, the
    client sent at least what KV read and read at most what KV wrote, KV's
    linearizability is the client's.
*)
Theory moonshotKvClient
Ancestors
  HttpSpec HttpSpecBodies HttpKvSpec EchoSpec2 HttpKvSpec2 endpointBufferHttp
  rich_list llist
Libs
  preamble

(* ------------------------------------------------------------------------
   KV's safety over any projections
   ------------------------------------------------------------------------ *)

(* Real time: at some point evs1 of evs, the whole reply to (j, i) was
   visible (wr) and no byte of (k, l) was (rd) *)
Definition precedes_g_def:
  precedes_g rd wr rss order evs (j, i) (k, l) ⇔
    ∃evs1. evs1 ≼ evs ∧
           reply_bytes (TAKE (SUC i) (replies rss order j)) ≼ wr j evs1 ∧
           rd k evs1 ≼ brequests (TAKE l (rss k))
End

Definition kv_safe_g_def:
  kv_safe_g rd wr io ⇔
    ∀evs rss rests.
      LPREFIX (fromList evs) io ∧
      (∀j. EVERY valid_brequest (rss j) ∧ no_full_brequest (rests j) ∧
           rd j evs = brequests (rss j) ++ rests j) ⇒
      ∃order.
        is_order2 rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedes_g rd wr rss order evs x y ⇒ earlier order x y) ∧
        ∀j. wr j evs ≼ reply_bytes (replies rss order j)
End

Theorem precedes2_g:
  precedes2 = precedes_g ep_read ep_written
Proof
  simp[FUN_EQ_THM, FORALL_PROD, precedes2_def, precedes_g_def]
QED

Theorem kv_safe2_g:
  kv_safe2 io ⇔ kv_safe_g ep_read ep_written io
Proof
  simp[kv_safe2_def, kv_safe_g_def, precedes2_g]
QED

(* ------------------------------------------------------------------------
   The client's view
   ------------------------------------------------------------------------ *)

Definition kv_client_safe_def:
  kv_client_safe snt crd io ⇔
    ∀evs. LPREFIX (fromList evs) io ⇒
      ∃rss order.
        (∀j. EVERY valid_brequest (rss j) ∧ brequests (rss j) ≼ snt j evs) ∧
        is_order2 rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedes_g snt crd rss order evs x y ⇒ earlier order x y) ∧
        ∀j. crd j evs ≼ reply_bytes (replies rss order j)
End

(* ------------------------------------------------------------------------
   Lemmas
   ------------------------------------------------------------------------ *)

Theorem brequests_CONS:
  brequests (r :: rs) = brequests [r] ++ brequests rs
Proof
  simp[brequests_def, bytes_def]
QED

Theorem brequests_NIL[simp]:
  brequests [] = [] ∧ (brequests rs = [] ⇔ rs = [])
Proof
  simp[brequests_def, bytes_def] >> Cases_on ‘rs’ >> simp[] >>
  rename1 ‘print_brequest r’ >> Cases_on ‘r’ >> simp[print_brequest_def]
QED

(* Any bytes are some complete valid requests, then no complete one *)
Theorem brequests_split:
  ∀bs. ∃rs rest. EVERY valid_brequest rs ∧ no_full_brequest rest ∧
                 bs = brequests rs ++ rest
Proof
  gen_tac >> completeInduct_on ‘LENGTH bs’ >> rw[] >>
  Cases_on ‘no_full_brequest bs’
  >- (qexistsl_tac [‘[]’, ‘bs’] >> simp[]) >>
  fs[no_full_brequest_def, IS_PREFIX_APPEND] >> rename1 ‘bs = brequests [r] ++ bs'’ >>
  ‘brequests [r] ≠ []’ by simp[] >>
  first_x_assum (qspec_then ‘LENGTH bs'’ mp_tac) >>
  impl_tac >- (gvs[] >> Cases_on ‘brequests [r]’ >> gvs[]) >>
  disch_then (qspec_then ‘bs'’ mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [‘r :: rs’, ‘rest’] >> gvs[] >> ONCE_REWRITE_TAC [brequests_CONS] >> simp[]
QED

Theorem LPREFIX_fromList_prefix:
  evs1 ≼ evs ∧ LPREFIX (fromList evs) io ⇒ LPREFIX (fromList evs1) io
Proof
  strip_tac >> irule LPREFIX_TRANS >> qexists_tac ‘fromList evs’ >>
  simp[LPREFIX_fromList, from_toList]
QED

Theorem LENGTH_kv_run[simp]:
  ∀st rs. LENGTH (kv_run st rs) = LENGTH rs
Proof
  Induct_on ‘rs’ >> simp[kv_run_def] >> rpt gen_tac >> pairarg_tac >> simp[]
QED

(* Renaming episodes by g, injective on the order's episodes *)
Theorem filter_rename:
  ∀order. (∀d. MEM d (MAP FST order) ⇒ (g d = c' ⇔ d = c)) ⇒
          MAP SND (FILTER (λx. FST x = c') (MAP (λ(d, i). (g d, i)) order)) =
          MAP SND (FILTER (λx. FST x = c) order)
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem filter_rename_none:
  ∀order. (∀d. MEM d (MAP FST order) ⇒ g d ≠ c') ⇒
          FILTER (λx. FST x = c') (MAP (λ(d, i). (g d, i)) order) = []
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem zip_filter_rename:
  ∀order ys. LENGTH ys = LENGTH order ∧
             (∀d. MEM d (MAP FST order) ⇒ (g d = g c ⇔ d = c)) ⇒
             MAP SND (FILTER (λ((d, i), a). d = g c) (ZIP (MAP (λ(d, i). (g d, i)) order, ys))) =
             MAP SND (FILTER (λ((d, i), a). d = c) (ZIP (order, ys)))
Proof
  Induct >> simp[FORALL_PROD] >> rpt gen_tac >> Cases_on ‘ys’ >> simp[] >>
  rw[] >> gvs[]
QED

Theorem replies_rename:
  (∀d. MEM d (MAP FST order) ⇒ r2 (g d) = r1 d ∧ (g d = g c ⇔ d = c)) ⇒
  replies r2 (MAP (λ(d, i). (g d, i)) order) (g c) = replies r1 order c
Proof
  strip_tac >> simp[replies_def] >>
  ‘MAP (λ(d, i). EL i (r2 d)) (MAP (λ(d, i). (g d, i)) order) =
   MAP (λ(d, i). EL i (r1 d)) order’
    by (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >> simp[FORALL_PROD] >>
        rw[] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  simp[] >> irule zip_filter_rename >> simp[]
QED

Theorem earlier_rename:
  earlier order (a, b) (c, d) ⇒
  earlier (MAP (λ(x, y). (g x, y)) order) (g a, b) (g c, d)
Proof
  rw[earlier_def] >> simp[MAP_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The transfer
   ------------------------------------------------------------------------ *)

(* kvs t and cls t: KV's and the client's traces at instant t.  e: the
   pairing of the client's episodes with KV's (partial, injective).  At
   every instant, per pair, KV has read at most what the client sent, and
   the client has read at most what KV wrote; an unpaired episode of
   either reads nothing *)
Theorem kv_client_view_safe:
  (∀(t:num) t'. t ≤ t' ⇒ kvs t ≼ kvs t' ∧ cls t ≼ cls t') ∧
  (∀t. LPREFIX (fromList (kvs t)) io_k) ∧
  (∀evs. LPREFIX (fromList evs) io_c ⇒ ∃t. cls t = evs) ∧
  (∀j1 j2 j'. e j1 = SOME j' ∧ e j2 = SOME j' ⇒ j1 = j2) ∧
  (∀t j. e j = NONE ⇒ crd j (cls t) = []) ∧
  (∀t j j'. e j = SOME j' ⇒
     krd j' (kvs t) ≼ snt j (cls t) ∧ crd j (cls t) ≼ kwr j' (kvs t)) ∧
  (∀t j'. (∀j. e j ≠ SOME j') ⇒ krd j' (kvs t) = []) ∧
  kv_safe_g krd kwr io_k ⇒
  kv_client_safe snt crd io_c
Proof
  rw[kv_client_safe_def] >>
  ‘∃t. cls t = evs’ by metis_tac[] >>
  qpat_x_assum ‘cls t = evs’ (SUBST_ALL_TAC o SYM) >>
  ‘∀j'. ∃rs rest. EVERY valid_brequest rs ∧ no_full_brequest rest ∧
                  krd j' (kvs t) = brequests rs ++ rest’ by metis_tac[brequests_split] >>
  fs[SKOLEM_THM] >> rename1 ‘krd _ (kvs t) = brequests (rssK _) ++ restsK _’ >>
  qpat_x_assum ‘kv_safe_g _ _ _’ (mp_tac o REWRITE_RULE [kv_safe_g_def]) >>
  disch_then (qspecl_then [‘kvs t’, ‘rssK’, ‘restsK’] mp_tac) >> simp[] >>
  disch_then (qx_choose_then ‘orderK’ strip_assume_tac) >>
  qabbrev_tac ‘g = λj'. @j. e j = SOME j'’ >>
  ‘∀j j'. e j = SOME j' ⇒ g j' = j’
    by (rw[Abbr ‘g’] >> SELECT_ELIM_TAC >> metis_tac[]) >>
  (* every episode in KV's order is paired *)
  ‘∀d. MEM d (MAP FST orderK) ⇒ e (g d) = SOME d’
    by (rpt strip_tac >>
        ‘∃j. e j = SOME d’
          suffices_by (strip_tac >> ‘g d = j’ by metis_tac[] >> simp[]) >>
        CCONTR_TAC >>
        ‘krd d (kvs t) = []’
          by (qpat_x_assum ‘∀t j'. (∀j. _) ⇒ _’ irule >> metis_tac[]) >>
        ‘rssK d = []’
          by (qpat_x_assum ‘∀j'. _ ∧ _ ∧ krd _ _ = _’ (qspec_then ‘d’ mp_tac) >>
              simp[]) >>
        qpat_x_assum ‘is_order2 _ _’ (mp_tac o Q.SPEC ‘d’ o REWRITE_RULE [is_order2_def]) >>
        simp[COUNT_LIST_def, FILTER_EQ_NIL, EVERY_MEM] >>
        gvs[MEM_MAP] >> metis_tac[]) >>
  qexistsl_tac [‘λj. case e j of NONE => [] | SOME j' => rssK j'’,
                ‘MAP (λ(d, i). (g d, i)) orderK’] >>
  ‘∀d j j0. MEM d (MAP FST orderK) ∧ e j = SOME j0 ⇒ (g d = j ⇔ d = j0)’
    by (rpt strip_tac >> eq_tac >> strip_tac
        >- (‘e (g d) = SOME d’ by (qpat_assum ‘∀d. MEM d _ ⇒ _’ irule >> simp[]) >>
            gvs[]) >>
        gvs[] >> qpat_assum ‘∀j j'. e j = SOME j' ⇒ g j' = j’ irule >> simp[]) >>
  ‘∀j0. (∃j. e j = SOME j0) ⇒
        replies (λj. case e j of NONE => [] | SOME j' => rssK j')
          (MAP (λ(d, i). (g d, i)) orderK) (g j0) = replies rssK orderK j0’
    by (rpt strip_tac >>
        ‘e (g j0) = SOME j0’
          by (‘g j0 = j’ by (qpat_assum ‘∀j j'. e j = SOME j' ⇒ g j' = j’ irule >>
                             first_assum ACCEPT_TAC) >>
              pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        irule replies_rename >> rpt strip_tac
        >- (‘e (g d) = SOME d’ by (qpat_assum ‘∀d. MEM d _ ⇒ e _ = _’ irule >>
                                   first_assum ACCEPT_TAC) >>
            pop_assum (fn th => simp[th])) >>
        qpat_assum ‘∀d j j0. _ ⇒ (_ ⇔ _)’ irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac
  >- (gen_tac >> Cases_on ‘e j’ >> simp[] >> rename1 ‘e j = SOME j0’ >>
      qpat_assum ‘∀j'. _ ∧ _ ∧ krd _ _ = _’ (qspec_then ‘j0’ strip_assume_tac) >>
      simp[] >> irule IS_PREFIX_TRANS >> qexists_tac ‘krd j0 (kvs t)’ >>
      conj_tac >- simp[IS_PREFIX_APPEND3] >>
      qpat_assum ‘∀t j j'. e j = SOME j' ⇒ _’ (qspecl_then [‘t’, ‘j’, ‘j0’] mp_tac) >>
      simp[])
  >- (rw[is_order2_def] >> Cases_on ‘e j’ >>
      pop_assum (fn th => REWRITE_TAC [th] >> assume_tac th) >> simp[]
      >- (‘FILTER (λx. FST x = j) (MAP (λ(d, i). (g d, i)) orderK) = []’
            by (irule filter_rename_none >> rpt strip_tac >>
                ‘e (g d) = SOME d’ by (qpat_assum ‘∀d. MEM d _ ⇒ e _ = _’ irule >> simp[]) >>
                gvs[]) >>
          pop_assum (fn th => simp[th, COUNT_LIST_def])) >>
      rename1 ‘e j = SOME j0’ >>
      ‘MAP SND (FILTER (λx. FST x = j) (MAP (λ(d, i). (g d, i)) orderK)) =
       MAP SND (FILTER (λx. FST x = j0) orderK)’
        by (irule filter_rename >> rpt strip_tac >> qpat_assum ‘∀d j j0. _’ irule >> simp[]) >>
      pop_assum SUBST1_TAC >>
      qpat_x_assum ‘is_order2 rssK orderK’ (mp_tac o REWRITE_RULE [is_order2_def]) >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘MEM x _’
        (qx_choosel_then [‘j0’, ‘i’] strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_MAP, EXISTS_PROD]) >>
      qpat_x_assum ‘MEM y _’
        (qx_choosel_then [‘k0’, ‘l’] strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_MAP, EXISTS_PROD]) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      ‘MEM j0 (MAP FST orderK) ∧ MEM k0 (MAP FST orderK)’
        by (simp[MEM_MAP, EXISTS_PROD] >> conj_tac
            >- (qexists_tac ‘i’ >> first_assum ACCEPT_TAC) >>
            qexists_tac ‘l’ >> first_assum ACCEPT_TAC) >>
      ‘e (g j0) = SOME j0 ∧ e (g k0) = SOME k0’
        by (conj_tac >> qpat_assum ‘∀d. MEM d _ ⇒ e _ = _’ irule >> first_assum ACCEPT_TAC) >>
      ‘j0 ≠ k0’
        by (strip_tac >> pop_assum SUBST_ALL_TAC >>
            qpat_x_assum ‘FST _ ≠ FST _’ mp_tac >> simp[]) >>
      ‘replies (λj. case e j of NONE => [] | SOME j' => rssK j')
         (MAP (λ(d, i). (g d, i)) orderK) (g j0) = replies rssK orderK j0’
        by (qpat_assum ‘∀j0. (∃j. _) ⇒ _’ irule >> qexists_tac ‘g j0’ >>
            first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘precedes_g _ _ _ _ _ _ _’
        (strip_assume_tac o SIMP_RULE (srw_ss()) [precedes_g_def]) >>
      qpat_x_assum ‘replies _ _ (g j0) = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      qpat_x_assum ‘e (g k0) = SOME k0’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
                                                 assume_tac th) >>
      ‘∃t1. cls t1 = evs1’
        by (qpat_assum ‘∀evs. LPREFIX _ io_c ⇒ _’ irule >> irule LPREFIX_fromList_prefix >>
            qexists_tac ‘cls t’ >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      ‘∃t2:num. t2 ≤ (t:num) ∧ cls t2 = evs1’
        by (DISJ_CASES_TAC (Q.SPECL [‘t1:num’, ‘t:num’] LESS_EQ_CASES)
            >- (qexists_tac ‘t1’ >> conj_tac >> first_assum ACCEPT_TAC) >>
            qexists_tac ‘t’ >> simp[] >>
            ‘cls t ≼ cls t1’ by (qpat_assum ‘∀(t:num) t'. t ≤ t' ⇒ _’ (qspecl_then [‘t’, ‘t1’] mp_tac) >>
                                 impl_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
            irule IS_PREFIX_ANTISYM >> qpat_x_assum ‘cls t1 = evs1’ SUBST_ALL_TAC >>
            conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘cls t2 = evs1’ (SUBST_ALL_TAC o SYM) >>
      irule earlier_rename >>
      qpat_assum ‘∀x y. MEM x orderK ∧ _ ⇒ _’ irule >> simp[precedes_g_def] >>
      qexists_tac ‘kvs t2’ >> rpt conj_tac
      >- (qpat_assum ‘∀(t:num) t'. t ≤ t' ⇒ _’ (qspecl_then [‘t2’, ‘t’] mp_tac) >> simp[])
      >- (irule IS_PREFIX_TRANS >> qexists_tac ‘crd (g j0) (cls t2)’ >> conj_tac >>
          TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
          qpat_assum ‘∀t j j'. e j = SOME j' ⇒ _’ (qspecl_then [‘t2’, ‘g j0’, ‘j0’] mp_tac) >>
          impl_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])
      >> irule IS_PREFIX_TRANS >> qexists_tac ‘snt (g k0) (cls t2)’ >> conj_tac >>
      TRY (qpat_x_assum ‘snt (g k0) (cls t2) ≼ _’ mp_tac >> simp[] >> NO_TAC) >>
      qpat_assum ‘∀t j j'. e j = SOME j' ⇒ _’ (qspecl_then [‘t2’, ‘g k0’, ‘k0’] mp_tac) >>
      impl_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])
  >> gen_tac >> Cases_on ‘e j’
  >- (‘crd j (cls t) = []’
        by (qpat_assum ‘∀t j. e j = NONE ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
      pop_assum (fn th => simp[th]))
  >> rename1 ‘e j = SOME j0’ >>
  ‘g j0 = j’ by (qpat_assum ‘∀j j'. e j = SOME j' ⇒ g j' = j’ irule >> first_assum ACCEPT_TAC) >>
  ‘replies (λj. case e j of NONE => [] | SOME j' => rssK j')
     (MAP (λ(d, i). (g d, i)) orderK) (g j0) = replies rssK orderK j0’
    by (qpat_assum ‘∀j0. (∃j. _) ⇒ _’ irule >> qexists_tac ‘j’ >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘g j0 = j’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  pop_assum SUBST1_TAC >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘kwr j0 (kvs t)’ >> conj_tac >>
  TRY (qpat_assum ‘∀j. kwr j (kvs t) ≼ _’ (qspec_then ‘j0’ ACCEPT_TAC) >> NO_TAC) >>
  qpat_assum ‘∀t j j'. e j = SOME j' ⇒ _’ (qspecl_then [‘t’, ‘j’, ‘j0’] mp_tac) >>
  impl_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED
