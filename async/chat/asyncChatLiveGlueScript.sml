(*
  Delivery for the chat server, part 3: gluing the writer-local facts
  (asyncChatLiveCover) to the run, through the library's view of a
  connection's handler (view_wrap_ans).  Helpers first.
*)
Theory asyncChatLiveGlue
Ancestors
  pair list rich_list arithmetic option string words alist sorting
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncServerV asyncServerVLive asyncServerVLiveA
  asyncServerVPushLive asyncWithStore asyncWithTap asyncChatSW
  asyncChatModel asyncChatSafe asyncChatLiveV asyncChatLiveDeliver
  asyncChatLiveCover
Libs
  BasicProvers dep_rewrite

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem nfa_APPEND[local]:
  nfa fd (a ++ b) = nfa fd a + nfa fd b
Proof
  simp[FILTER_APPEND]
QED

(* More answered Fetches in A ++ B than in A: one of them is in B *)
Theorem nfa_split_exists:
  nfa fd A < nfa fd (A ++ B) ⇒
  ∃p. LENGTH A ≤ p ∧ p < LENGTH (A ++ B) ∧ afetch fd (EL p (A ++ B))
Proof
  simp[FILTER_APPEND] >> strip_tac >>
  ‘FILTER (afetch fd) B ≠ []’ by (strip_tac >> fs[]) >>
  ‘∃x. MEM x (FILTER (afetch fd) B)’ by (Cases_on ‘FILTER (afetch fd) B’ >> fs[] >> metis_tac[MEM]) >>
  fs[MEM_FILTER, MEM_EL] >>
  qexists_tac ‘LENGTH A + n’ >> simp[EL_APPEND2] >> metis_tac[]
QED

(* The k-th entry of FILTER (P o FST) (with_state TR), for the entry at p *)
Theorem FILTER_with_state_EL:
  p < LENGTH TR ∧ P (EL p TR) ⇒
  LENGTH (FILTER P (TAKE p TR)) < LENGTH (FILTER (P ∘ FST) (with_state TR)) ∧
  EL (LENGTH (FILTER P (TAKE p TR))) (FILTER (P ∘ FST) (with_state TR)) =
    (EL p TR, tap_fold chat_tap chat_delta empty_store (TAKE p TR))
Proof
  strip_tac >>
  ‘with_state TR =
     with_state (TAKE p TR) ++
     [(EL p TR, tap_fold chat_tap chat_delta empty_store (TAKE p TR))] ++
     DROP (SUC p) (with_state TR)’
    by (‘with_state TR = TAKE (SUC p) (with_state TR) ++ DROP (SUC p) (with_state TR)’
          by simp[] >>
        pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        simp[TAKE_with_state] >>
        ‘TAKE (SUC p) TR = TAKE p TR ++ [EL p TR]’
          by simp[GSYM SNOC_EL_TAKE, SNOC_APPEND] >>
        simp[with_state_def, GENLIST, SNOC_APPEND] >>
        simp[GENLIST_FUN_EQ, EL_APPEND1, TAKE_APPEND1, EL_APPEND2,
             TAKE_LENGTH_APPEND] >>
        rw[EL_APPEND1, TAKE_APPEND1, TAKE_TAKE]) >>
  pop_assum SUBST1_TAC >>
  ‘LENGTH (FILTER (P ∘ FST) (with_state (TAKE p TR))) = LENGTH (FILTER P (TAKE p TR))’
    by metis_tac[LENGTH_MAP, MAP_FST_FILTER_FST, MAP_FST_with_state] >>
  simp[FILTER_APPEND, EL_APPEND2] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND2]
QED

(* ------------------------------------------------------------------------
   Lines and joins
   ------------------------------------------------------------------------ *)

(* Unanswered entries complete no lines *)
Theorem lines_done_NONE:
  ∀V U. EVERY (λp. SND p = NONE) V ⇒ lines_done (U ++ V) = lines_done U
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rw[SNOC_APPEND, EVERY_APPEND] >>
  qspecl_then [‘U ++ V’, ‘x’] mp_tac (Q.GENL [‘tr’, ‘p’] lines_done_SNOC) >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> disch_then SUBST1_TAC >>
  ‘comp (U ++ V) x = ""’
    by (PairCases_on ‘x’ >> gvs[comp_def] >> every_case_tac >> gvs[]) >>
  simp[]
QED

(* Joins are never forgotten, and an accept makes one *)
Theorem joins_mono:
  ∀TR st. (∃j. ALOOKUP st.joins k = SOME j) ⇒
          ∃j. ALOOKUP (tap_fold chat_tap chat_delta st TR).joins k = SOME j
Proof
  Induct >> simp[tap_fold_def] >> PairCases >> Cases_on ‘h0’ >>
  simp[tap_fold_def] >> rpt strip_tac >> first_x_assum irule
  >- (every_case_tac >> simp[] >>
      rename1 ‘chat_tap st a r’ >> Cases_on ‘a’ >> Cases_on ‘r’ >>
      simp[chat_tap_def] >> every_case_tac >> simp[ALOOKUP_def] >> rw[])
  >> PairCases_on ‘q’ >> Cases_on ‘q1’ >> simp[chat_delta_def] >>
  every_case_tac >> simp[]
QED

Theorem joins_accept:
  ∀TR st. MEM (Sock (Accept l), SOME (SockR (Accepted d))) TR ⇒
          ∃j. ALOOKUP (tap_fold chat_tap chat_delta st TR).joins (n2w d) = SOME j
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[tap_fold_def]
  >- (irule joins_mono >> simp[chat_tap_def])
  >> PairCases_on ‘h’ >> Cases_on ‘h0’ >> simp[tap_fold_def]
QED

(* ------------------------------------------------------------------------
   The handler's writer
   ------------------------------------------------------------------------ *)

(* The writer's part of a handler's run, on the writer's view *)
Theorem chat_handler_writer_views:
  prompt (chat_handler fd) (g : (event, (canswer, asyncServer$response) kres) snapshot list) ⇒
  ∃(G : (event, (canswer, asyncServer$response) kres) snapshot list).
      LENGTH G = LENGTH g ∧ prompt (writer fd) G ∧
      ∀j. FILTER (wq fd) (trans (chat_handler fd) (TAKE j g)) =
          trans (writer fd) (TAKE j G)
Proof
  simp[chat_handler_def] >> strip_tac >> drule prompt_both >> strip_tac >>
  first_assum (irule_at Any) >> simp[] >> gen_tac >>
  DEP_REWRITE_TAC[trans_both_filter_right] >> conj_tac
  >- (simp[FILTER_EQ_NIL] >>
      irule EVERY_MONOTONIC >> qexists ‘λp. FST p = Sock (Read fd)’ >>
      simp[reader_entries, wq_def])
  >> simp[writer_filter, views_TAKE]
QED

(* An answered Fetch is a writer entry, and a handler's entries are fd's *)
Theorem afetch_wq:
  afetch fd p ⇒ wq fd p
Proof
  rw[afetch_def, wq_def] >> simp[]
QED

Theorem nfa_FILTER_wq:
  nfa fd (FILTER (wq fd) tr) = nfa fd tr
Proof
  simp[FILTER_FILTER] >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM] >> metis_tac[afetch_wq]
QED

Theorem wq_on_fd_v[local]:
  wq fd p ⇒ on_fd_v chatV fd p
Proof
  rw[wq_def, on_fd_v_def, chatV_def] >> simp[]
QED

Theorem FILTER_wq_on_fd_v:
  FILTER (wq fd) (FILTER (on_fd_v chatV fd) tr) = FILTER (wq fd) tr
Proof
  simp[FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM] >> metis_tac[wq_on_fd_v]
QED

Theorem kanswers_on_fd_v_wq:
  EVERY (on_fd_v chatV fd) tr ⇒ kanswers chatV (FILTER (wq fd) tr) = kanswers chatV tr
Proof
  Induct_on ‘tr’ >> simp[kanswers_def] >> PairCases >>
  rw[] >> gvs[wq_def, on_fd_v_def, chatV_def] >>
  every_case_tac >> gvs[] >> fs[kanswers_def] >> metis_tac[PAIR]
QED

Theorem on_fd_v_on_fdc:
  on_fd_v chatV fd p ⇔ on_fdc fd p
Proof
  PairCases_on ‘p’ >> Cases_on ‘p0’ >>
  simp[on_fd_v_def, chatV_def, on_fdc_def, on_fd_def]
  >- (Cases_on ‘a’ >> simp[] >> metis_tac[])
  >> PairCases_on ‘q’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Unanswered tails
   ------------------------------------------------------------------------ *)

Theorem untag_NONE:
  ∀V. EVERY (λp. SND p = NONE) V ⇒ EVERY (λp. SND p = NONE) (untag V)
Proof
  Induct >> simp[untag_def] >> PairCases >> Cases_on ‘h0’ >> rw[] >>
  gvs[untag_def]
QED

Theorem acceptedc_NONE:
  ∀V. EVERY (λp. SND p = NONE) V ⇒ acceptedc V = []
Proof
  Induct >> simp[acceptedc_def] >> PairCases >> rw[] >> gvs[acceptedc_def] >>
  every_case_tac >> simp[]
QED

Theorem SPLITP_acc_of_NONE[local]:
  ∀V. EVERY (λp. SND p = NONE) V ⇒ rich_list$SPLITP (acc_of fd) V = (V, [])
Proof
  Induct >> simp[SPLITP] >> PairCases >> rw[] >> gvs[acc_of_def, SPLITP]
QED

Theorem SPLITP_NIL_SND[local]:
  ∀l. SND (rich_list$SPLITP P l) = [] ⇔ ¬EXISTS P l
Proof
  Induct >> simp[SPLITP] >> rw[]
QED

Theorem owed_m_NONE:
  EVERY (λp. SND p = NONE) V ⇒ owed_m fd (U ++ V) = owed_m fd U
Proof
  strip_tac >> imp_res_tac SPLITP_acc_of_NONE >> simp[owed_m_def, SPLITP_APPEND] >>
  Cases_on ‘EXISTS (acc_of fd) U’ >> simp[]
  >- (‘SND (SPLITP (acc_of fd) U) ≠ []’ by metis_tac[SPLITP_NIL_SND] >>
      Cases_on ‘SPLITP (acc_of fd) U’ >> gvs[] >>
      rename1 ‘(_, r)’ >> Cases_on ‘r’ >> gvs[lines_done_NONE])
  >> ‘SND (SPLITP (acc_of fd) U) = []’ by metis_tac[SPLITP_NIL_SND] >>
  Cases_on ‘SPLITP (acc_of fd) U’ >> gvs[] >>
  fs[] >> Cases_on ‘SPLITP (acc_of fd) V’ >> gvs[]
QED

(* The first accept of fd splits every prefix that contains it the same way *)
Theorem SPLITP_prefix_same:
  ∀L Q L1 L2. SPLITP P L = (L1, L2) ∧ Q ≼ L ∧ SND (SPLITP P Q) ≠ [] ⇒
              FST (SPLITP P Q) = L1
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘Q’ >> simp[SPLITP] >>
  rw[] >> gvs[SPLITP] >>
  Cases_on ‘SPLITP P L’ >> gvs[] >>
  Cases_on ‘SPLITP P t’ >> gvs[] >>
  first_x_assum (qspecl_then [‘t’, ‘q’, ‘r’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The writer's first entry
   ------------------------------------------------------------------------ *)

Theorem writer_HD_answered:
  prompt (writer fd) (s :: G) ⇒
  ∃r. trans (writer fd) (s :: G) ≠ [] ∧
      HD (trans (writer fd) (s :: G)) = (Kv (fd, Start), SOME r)
Proof
  simp[asyncChatModelTheory.writer_def] >> strip_tac >>
  drule bind_emit_step >> strip_tac >> simp[]
QED

Theorem trans_writer_NIL:
  trans (writer fd) [] = [(Kv (fd, Start), NONE)]
Proof
  simp[asyncChatModelTheory.writer_def, trans_def, round_trans_def,
       responses_at_def, new_actions_def, log_of_def, bind_emit_NIL, zipr_def]
QED

(* ------------------------------------------------------------------------
   Prefixes of what the writer was told
   ------------------------------------------------------------------------ *)

Theorem told_TAKE_prefix:
  CONCAT (cout (DROP 1 (kanswers chatV (TAKE n L)))) ≼
  CONCAT (cout (DROP 1 (kanswers chatV L)))
Proof
  ‘L = TAKE n L ++ DROP n L’ by simp[] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  REWRITE_TAC[kanswers_APPEND] >>
  qspec_tac (‘kanswers chatV (TAKE n L)’, ‘A’) >>
  qspec_tac (‘kanswers chatV (DROP n L)’, ‘B’) >> rpt gen_tac >>
  Cases_on ‘A’ >> simp[] >> simp[DROP_APPEND] >> rw[] >>
  simp[FLAT_APPEND, cout_simps]
QED
