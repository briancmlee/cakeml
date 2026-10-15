(*
  ChatSpec's second liveness clause (reads), part 2: the chat handler, in
  every environment the library's world gives it (henv_t), eventually reads
  all of the data D its client sent.  As asyncEchoLiveLib's echo_reads,
  with the chat reader's progress (reader_progress) lifted to the handler
  (both reader writer) through its left view.
*)
Theory asyncChatLiveReads
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncServerV asyncServerVLive asyncServerVPushLive
  asyncServerWithLiveFlat asyncWithStore asyncChatModel asyncChatSafe
  asyncChatLiveV asyncChatLiveRead
Libs
  BasicProvers dep_rewrite

Overload cwriter = “λfd. (writer fd : rh -> (ract, unit option) asyncCore$outcome)”
Overload chtr = “λfd q. sproj chatV (trans (chat_handler fd) q)”

(* ------------------------------------------------------------------------
   The handler reads through its reader
   ------------------------------------------------------------------------ *)

Theorem views_ready_g:
  i < LENGTH (q : rh) ⇒
  (EL i (left_view (creader fd) (cwriter fd) q)).ready = (EL i q).ready
Proof
  strip_tac
  >> qspecl_then [‘log_of (creader fd)’, ‘log_of (cwriter fd)’, ‘q’] mp_tac
       (Q.GENL [‘a1’, ‘a2’] par_views_world)
  >> rw[left_view_def, right_view_def]
  >> qpat_x_assum ‘MAP _ (FST _) = _’ (mp_tac o Q.AP_TERM ‘EL i’)
  >> simp[EL_MAP, LENGTH_par_views]
QED

Theorem writer_no_reads[local]:
  nreadc fd' (cwriter fd h).actions = 0
Proof
  ‘(cwriter fd h).actions = MAP FST (trans (cwriter fd) h)’
    by simp[MAP_FST_trans, wf_writer] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘fd’, ‘h’] mp_tac (Q.GENL [‘fd’, ‘hh’] writer_entries) >>
  qspec_tac (‘trans (cwriter fd) h’, ‘tr’) >>
  Induct >> simp[] >> PairCases >> rw[wq_def] >> gvs[]
QED

Theorem chat_handler_nreadc:
  nreadc fd' (chat_handler fd h).actions =
  nreadc fd' (creader fd (left_view (creader fd) (cwriter fd) h)).actions
Proof
  simp[chat_handler_def, map_def] >>
  ‘∀acts. nreadc fd' acts = count (λa. a = Sock (Read fd')) acts’
    by simp[nreadc_def, count_def] >>
  simp[] >> DEP_REWRITE_TAC[count_both] >> simp[wf_reader, wf_writer] >>
  simp[GSYM nreadc_def |> SIMP_RULE std_ss [count_def]] >>
  fs[count_def, GSYM nreadc_def, writer_no_reads]
QED

Theorem reader_FILTER_reads[local]:
  FILTER (λp. FST p = Sock (Read fd)) (trans (chat_handler fd) g) =
  FILTER (λp. FST p = Sock (Read fd))
    (trans (creader fd) (left_view (creader fd) (cwriter fd) g))
Proof
  simp[chat_handler_def] >>
  DEP_REWRITE_TAC[trans_both_filter_left] >>
  simp[FILTER_EQ_NIL] >>
  irule EVERY_MONOTONIC >> qexists ‘wq fd’ >> simp[writer_entries] >>
  rw[wq_def] >> simp[]
QED

(* MAIN: progress of the handler's reads *)
Theorem chat_handler_progress:
  prompt (chat_handler fd) g ∧ k + 3 ≤ LENGTH g ∧
  (∀j. k ≤ j ∧ j < k + 3 ⇒ Readable fd ∈ (EL j g).ready) ∧
  ¬MEM (Sock (Read fd), SOME (SockR Eof)) (trans (chat_handler fd) g) ⇒
  nreadc fd (chat_handler fd (TAKE k g)).actions <
  nreadc fd (chat_handler fd (TAKE (k + 3) g)).actions
Proof
  strip_tac >> simp[chat_handler_nreadc, views_TAKE] >>
  irule reader_progress >> rpt conj_tac
  >~ [‘prompt (creader _) _’] >- (fs[chat_handler_def] >> drule prompt_both >> simp[])
  >~ [‘Readable _ ∈ (EL _ (left_view _ _ _)).ready’]
  >- (rpt strip_tac >> ‘j < LENGTH g’ by simp[] >>
      qspecl_then [‘j’, ‘g’, ‘fd’] mp_tac (Q.GENL [‘i’, ‘q’, ‘fd’] views_ready_g) >>
      simp[])
  >~ [‘MEM _ (trans (creader _) _)’]
  >- (strip_tac >>
      ‘MEM (Sock (Read fd), SOME (SockR Eof))
         (FILTER (λp. FST p = Sock (Read fd)) (trans (chat_handler fd) g))’
        by (REWRITE_TAC[reader_FILTER_reads] >> simp[MEM_FILTER]) >>
      fs[MEM_FILTER])
  >> simp[]
QED

(* ------------------------------------------------------------------------
   Reads only grow
   ------------------------------------------------------------------------ *)

Theorem read_sproj_NONE[local]:
  ∀V'. EVERY (λp. SND p = NONE) V' ⇒ read fd (sproj chatV V') = []
Proof
  Induct >- simp[sproj_def, read_def] >> PairCases >> rw[] >>
  ‘(h0, NONE) :: V' = [(h0, NONE)] ++ V'’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC[sproj_APPEND] >> simp[] >>
  Cases_on ‘h0’ >> simp[sproj_def, chatV_def, read_def] >>
  every_case_tac >> simp[]
QED

Theorem zipr_NIL_NONE_r[local]:
  ∀acts. EVERY (λp. SND p = NONE) (zipr acts [])
Proof
  Induct >> simp[zipr_def]
QED

Theorem hread_chat_mono:
  j ≤ k ⇒
  CONCAT (read fd (chtr fd' (TAKE j g))) ≼ CONCAT (read fd (chtr fd' (TAKE k g)))
Proof
  strip_tac >>
  ‘∀i. i ≤ LENGTH g ⇒
       read fd (chtr fd' (TAKE i g)) =
       read fd (sproj chatV (FLAT (GENLIST (round_trans (chat_handler fd') g) i)))’
    by (rpt strip_tac >> simp[trans_TAKE_split] >>
        simp[read_def, sproj_APPEND] >>
        ‘read fd (sproj chatV (zipr (new_actions (log_of (chat_handler fd')) (TAKE i g)) [])) = []’
          by (irule read_sproj_NONE >> simp[zipr_NIL_NONE_r]) >>
        fs[read_def]) >>
  Cases_on ‘LENGTH g ≤ j’
  >- (‘TAKE j g = g ∧ TAKE k g = g’ by simp[TAKE_LENGTH_TOO_LONG] >> simp[]) >>
  Cases_on ‘LENGTH g ≤ k’
  >- (‘TAKE k g = TAKE (LENGTH g) g’ by metis_tac[TAKE_LENGTH_TOO_LONG, TAKE_LENGTH_ID] >>
      pop_assum SUBST1_TAC >>
      ‘j ≤ LENGTH g’ by simp[] >> simp[] >>
      ‘LENGTH g = (LENGTH g − j) + j’ by simp[] >>
      pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >>
      simp[sproj_APPEND, read_def])
  >> ‘j ≤ LENGTH g ∧ k ≤ LENGTH g’ by simp[] >> simp[] >>
  ‘k = (k − j) + j’ by simp[] >> pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >>
  simp[sproj_APPEND, read_def]
QED

(* ------------------------------------------------------------------------
   The handler reads everything its client sent
   ------------------------------------------------------------------------ *)

Theorem nreadc_step_wf:
  ∀d. wf (m : rh -> (ract, 'x option) asyncCore$outcome) ∧
      nreadc fd (m (TAKE i h)).actions < nreadc fd (m (TAKE (i + d) h)).actions ⇒
      ∃k. i < k ∧ k ≤ i + d ∧ MEM (Sock (Read fd)) (new_actions (log_of m) (TAKE k h))
Proof
  Induct >- simp[] >> rpt strip_tac >>
  Cases_on ‘nreadc fd (m (TAKE i h)).actions < nreadc fd (m (TAKE (i + d) h)).actions’
  >- (first_x_assum drule_all >> strip_tac >> qexists_tac ‘k’ >> simp[]) >>
  qexists_tac ‘i + SUC d’ >> simp[] >>
  ‘i + SUC d ≤ LENGTH h’
    by (CCONTR_TAC >>
        ‘TAKE (i + SUC d) h = h ∧ TAKE (i + d) h = h’ by simp[TAKE_LENGTH_TOO_LONG] >>
        gvs[]) >>
  ‘TAKE (i + SUC d) h = TAKE (i + d) h ++ [EL (i + d) h]’
    by (‘i + SUC d = SUC (i + d)’ by simp[] >> pop_assum SUBST1_TAC >>
        simp[GSYM SNOC_EL_TAKE, SNOC_APPEND]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘(m (TAKE (i + d) h ++ [EL (i + d) h])).actions =
   (m (TAKE (i + d) h)).actions ++
   new_actions (log_of m) (TAKE (i + d) h ++ [EL (i + d) h])’
    by (qspecl_then [‘log_of m’, ‘TAKE (i + d) h’, ‘EL (i + d) h’] mp_tac
          (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix) >>
        simp[log_of_def, wf_SNOC_actions]) >>
  gvs[nreadc_def, FILTER_APPEND_DISTRIB] >> CCONTR_TAC >>
  ‘FILTER (λa. a = Sock (Read fd))
     (new_actions (log_of m) (TAKE (i + d) h ++ [EL (i + d) h])) = []’
    by simp[FILTER_EQ_NIL, EVERY_MEM] >>
  gvs[]
QED

Theorem chatV_sres[local,simp]:
  chatV.sres (SockR y) = SOME y ∧ chatV.sres (KvR b) = NONE
Proof
  simp[chatV_def]
QED

Theorem MEM_sproj_Sock[local]:
  MEM (Sock x, r) tr ⇒ MEM (x, OPTION_BIND r chatV.sres) (sproj chatV tr)
Proof
  simp[sproj_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> strip_tac >>
  first_assum (irule_at Any) >> simp[chatV_def]
QED

(* MAIN: in every environment henv_t, the chat handler eventually reads all
   of D.  n bounds what of D is still unread at round j. *)
Theorem chat_reads:
  ∀n j. prompt (chat_handler fd) g ∧ henv_t fd (chtr fd) g j0 D ∧ j0 ≤ j ∧
        LENGTH D ≤ LENGTH (hread_t fd (chtr fd) g j) + n ∧
        j + 4 * (n + 1) ≤ LENGTH g ⇒
        ∃j'. j' ≤ LENGTH g ∧ D ≼ hread_t fd (chtr fd) g j'
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  qpat_assum ‘henv_t _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [henv_t_def]) >>
  Cases_on ‘D ≼ hread_t fd (chtr fd) g j’
  >- (qexists_tac ‘j’ >> simp[]) >>
  ‘j ≤ LENGTH g’ by fs[] >>
  ‘hread_t fd (chtr fd) g j ≼ D’ by metis_tac[] >>
  ‘LENGTH (hread_t fd (chtr fd) g j) < LENGTH D’
    by (CCONTR_TAC >> fs[NOT_LESS] >> imp_res_tac IS_PREFIX_LENGTH >>
        metis_tac[IS_PREFIX_LENGTH_ANTI, LESS_EQUAL_ANTISYM, IS_PREFIX_REFL]) >>
  ‘0 < n’ by simp[] >>
  Cases_on ‘∃i. j ≤ i ∧ i < j + 3 ∧ Readable fd ∉ (EL i g).ready’
  >- (fs[] >> qexists_tac ‘SUC i’ >> simp[] >>
      qpat_x_assum ‘∀j. _ ∧ _ ∧ Readable fd ∉ _ ⇒ _’ irule >> simp[]) >>
  fs[] >>
  Cases_on ‘MEM (Read fd, SOME Eof) (chtr fd (TAKE (j + 3) g))’
  >- (qexists_tac ‘j + 3’ >> simp[] >>
      qpat_x_assum ‘∀j. _ ∧ _ ∧ MEM (Read fd, SOME Eof) _ ⇒ _’ irule >> simp[]) >>
  ‘¬MEM (Sock (Read fd), SOME (SockR Eof)) (trans (chat_handler fd) (TAKE (j + 3) g))’
    by (strip_tac >> drule MEM_sproj_Sock >> simp[]) >>
  ‘nreadc fd (chat_handler fd (TAKE j g)).actions <
   nreadc fd (chat_handler fd (TAKE (j + 3) g)).actions’
    by (qspecl_then [‘fd’, ‘TAKE (j + 3) g’, ‘j’] mp_tac
          (Q.GENL [‘fd’, ‘g’, ‘k’] chat_handler_progress) >>
        impl_tac
        >- (simp[prompt_TAKE, LENGTH_TAKE] >> rpt strip_tac >> simp[EL_TAKE] >>
            qpat_x_assum ‘∀i. _ ∨ _ ∨ _’ (qspec_then ‘j'’ mp_tac) >> simp[]) >>
        simp[TAKE_TAKE]) >>
  qspecl_then [‘3’] mp_tac
    (Q.GENL [‘m’, ‘i’, ‘h’] nreadc_step_wf |> Q.ISPEC ‘chat_handler fd’ |> Q.SPECL [‘j’, ‘g’]) >>
  simp[wf_chat_handler] >> strip_tac >>
  drule new_action_unanswered >> strip_tac >>
  drule MEM_sproj_Sock >> simp[] >> strip_tac >>
  ‘k < LENGTH g ∧ j0 ≤ k’ by simp[] >>
  Cases_on ‘D ≼ hread_t fd (chtr fd) g k’
  >- (qexists_tac ‘k’ >> simp[]) >>
  qpat_x_assum ‘∀j. _ ∧ _ ∧ MEM (Read fd, NONE) _ ∧ _ ⇒ _’ (qspec_then ‘k’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (qexists_tac ‘SUC k’ >> simp[]) >>
  ‘hread_t fd (chtr fd) g j ≼ hread_t fd (chtr fd) g k’
    by simp[hread_t_def, hread_chat_mono] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  qpat_x_assum ‘∀m. m < n ⇒ _’ (qspec_then ‘n − 1’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘SUC k’ mp_tac) >> simp[]
QED
