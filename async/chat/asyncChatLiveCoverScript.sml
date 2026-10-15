(*
  Delivery for the chat server, part 2: the hub's answers to a writer
  eventually cover what its client is owed.

  Writer-local facts (any history, an abstract log oracle):
   - wloop_told / writer_told (telescoping): the lines a writer has been
     told, up to an answered Fetch, are exactly the log at that Fetch
     from the writer's join position;
   - writer_nfa_lower / writer_nfa_upper (progress, as counting): on a
     history of n snapshots answered promptly, with Fetches answered by
     lines and Start by a position, the writer has at least (n - 1) DIV 2
     and at most n answered Fetches.  So over a long enough window, a new
     answered Fetch appears.
*)
Theory asyncChatLiveCover
Ancestors
  pair list rich_list arithmetic option string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncServerV asyncServerVLive asyncServerVLiveA
  asyncServerVPushLive asyncWithStore asyncWithTap asyncChatSW
  asyncChatModel asyncChatSafe asyncChatLiveV asyncChatLiveDeliver
Libs
  BasicProvers

(* An answered Fetch of fd *)
Definition afetch_def:
  afetch fd (p : (asyncServer$action, num # cquery) kact #
                  (canswer, asyncServer$response) kres option) ⇔
    ∃i b. p = (Kv (fd, Fetch i), SOME (KvR b))
End

Overload nfa = “λfd tr. LENGTH (FILTER (afetch fd) tr)”

(* The hub's kind of answers: lines to a Fetch, a position to a Start *)
Definition answers_kind_def:
  answers_kind fd tr ⇔
    (∀i r. MEM (Kv (fd, Fetch i), SOME r) tr ⇒ ∃s. r = KvR (Lines s)) ∧
    (∀r. MEM (Kv (fd, Start), SOME r) tr ⇒ ∃j. r = KvR (Pos j))
End

Theorem answers_kind_CONS[local]:
  answers_kind fd (e :: tr) ⇒ answers_kind fd tr
Proof
  rw[answers_kind_def] >> metis_tac[]
QED

Theorem trans_emit_running[local]:
  (∀n. n ≤ LENGTH h ⇒ (emit a (TAKE n h)).result = NONE) ⇒
  trans (emit a) h = [(a, NONE)]
Proof
  rw[trans_emit] >> Cases_on ‘h’ >> gvs[] >>
  first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def] >>
  rename1 ‘oHD s.results’ >> Cases_on ‘s.results’ >> simp[]
QED

(* Under prompt answering, an emit on a non-empty history is answered *)
Theorem prompt_emit_answered[local]:
  prompt (bind (emit a) f) (s :: q) ⇒ ∃r. oHD s.results = SOME r
Proof
  rw[prompt_def] >> first_x_assum (qspec_then ‘0’ mp_tac) >>
  simp[responses_at_def, new_actions_def, log_of_def, bind_emit_NIL] >>
  Cases_on ‘s.results’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Counting the answered Fetches
   ------------------------------------------------------------------------ *)

Theorem wloop_nfa_upper:
  ∀G i. nfa fd (trans (wloop (fd, i)) G) ≤ LENGTH G
Proof
  gen_tac >> measureInduct_on ‘LENGTH G’ >> gen_tac >>
  ONCE_REWRITE_TAC[asyncChatModelTheory.wloop_unfold] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Fetch i))) K0) G’ >>
  qspecl_then [‘emit (Kv (fd, Fetch i))’, ‘K0’, ‘G’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[afetch_def]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >>
  Cases_on ‘res’ >> simp[afetch_def, Abbr ‘K0’] >>
  Cases_on ‘b’ >> simp[afetch_def] >>
  rename1 ‘Lines ln’ >> Cases_on ‘ln = ""’ >> simp[] >>
  TRY (first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit WR) K1) h2’ >>
  qspecl_then [‘emit WR’, ‘K1’, ‘h2’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[afetch_def, Abbr ‘WR’]) >>
  drule first_done_emit >> strip_tac >>
  gvs[trans_emit, Abbr ‘K1’, Abbr ‘WR’, afetch_def] >>
  first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘i + STRLEN ln’ mp_tac) >> simp[]
QED

(* One answered emit under prompt answering *)
Theorem bind_emit_step[local]:
  prompt (bind (emit a) f) (s :: q) ⇒
  ∃r. oHD s.results = SOME r ∧ prompt (f r) q ∧
      trans (bind (emit a) f) (s :: q) = (a, SOME r) :: trans (f r) q
Proof
  strip_tac >> drule prompt_emit_answered >> strip_tac >>
  qexists_tac ‘r’ >> simp[] >>
  ‘first_done (emit a) [s] r’ by simp[first_done_emit_SOME] >>
  conj_tac
  >- (irule prompt_bind >> qexistsl [‘[s]’, ‘emit a’] >> simp[wf_emit, settled_emit])
  >> qspecl_then [‘emit a’, ‘[s]’, ‘r’, ‘f’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues) >>
  simp[wf_emit, settled_emit, trans_emit]
QED

Theorem wloop_nfa_lower:
  ∀G i. prompt (wloop (fd, i)) G ∧ answers_kind fd (trans (wloop (fd, i)) G) ⇒
        LENGTH G DIV 2 ≤ nfa fd (trans (wloop (fd, i)) G)
Proof
  gen_tac >> measureInduct_on ‘LENGTH G’ >> rpt gen_tac >>
  Cases_on ‘G’ >> simp[] >> rename1 ‘s :: G'’ >> strip_tac >>
  qpat_x_assum ‘prompt _ _’ mp_tac >> qpat_x_assum ‘answers_kind _ _’ mp_tac >>
  ONCE_REWRITE_TAC[asyncChatModelTheory.wloop_unfold] >>
  qmatch_goalsub_abbrev_tac ‘bind (emit (Kv (fd, Fetch i))) K0’ >>
  rpt strip_tac >>
  drule bind_emit_step >> strip_tac >> gvs[] >>
  ‘∃ln. r = KvR (Lines ln)’ by gvs[answers_kind_def] >>
  gvs[Abbr ‘K0’, afetch_def] >>
  drule answers_kind_CONS >> strip_tac >>
  Cases_on ‘ln = ""’ >> gvs[]
  >- (first_x_assum (qspec_then ‘G'’ mp_tac) >> simp[] >>
      disch_then (qspec_then ‘i’ mp_tac) >> simp[] >> strip_tac >>
      ‘SUC (LENGTH G') DIV 2 ≤ SUC (LENGTH G' DIV 2)’
        by (simp[ADD1] >> intLib.ARITH_TAC) >>
      simp[]) >>
  Cases_on ‘G'’ >> simp[] >> rename1 ‘s' :: G''’ >>
  drule bind_emit_step >> strip_tac >> gvs[afetch_def] >>
  drule answers_kind_CONS >> strip_tac >>
  first_x_assum (qspec_then ‘G''’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘i + STRLEN ln’ mp_tac) >> simp[] >> strip_tac >>
  ‘SUC (SUC (LENGTH G'')) DIV 2 = SUC (LENGTH G'' DIV 2)’
    by (simp[ADD1] >> ‘LENGTH G'' + 1 + 1 = LENGTH G'' + 1 * 2’ by simp[] >>
        pop_assum SUBST1_TAC >> simp[ADD_DIV_RWT]) >>
  simp[]
QED

Theorem writer_nfa_upper:
  nfa fd (trans (writer fd) G) ≤ LENGTH G
Proof
  simp[asyncChatModelTheory.writer_def] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Start))) K0) G’ >>
  qspecl_then [‘emit (Kv (fd, Start))’, ‘K0’, ‘G’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[afetch_def]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >>
  Cases_on ‘res’ >> simp[afetch_def, Abbr ‘K0’] >>
  Cases_on ‘b’ >> simp[afetch_def] >>
  qspecl_then [‘h2’, ‘n’] mp_tac wloop_nfa_upper >> simp[]
QED

Theorem writer_nfa_lower:
  prompt (writer fd) G ∧ answers_kind fd (trans (writer fd) G) ⇒
  (LENGTH G - 1) DIV 2 ≤ nfa fd (trans (writer fd) G)
Proof
  Cases_on ‘G’ >> simp[] >> rename1 ‘s :: G'’ >>
  simp[asyncChatModelTheory.writer_def] >>
  qmatch_goalsub_abbrev_tac ‘bind (emit (Kv (fd, Start))) K0’ >>
  rpt strip_tac >>
  drule bind_emit_step >> strip_tac >> gvs[] >>
  ‘∃j. r = KvR (Pos j)’ by gvs[answers_kind_def] >>
  gvs[Abbr ‘K0’, afetch_def] >>
  drule answers_kind_CONS >> strip_tac >>
  irule wloop_nfa_lower >> simp[]
QED

(* ------------------------------------------------------------------------
   Telescoping
   ------------------------------------------------------------------------ *)

Theorem cout_kanswers_sing[local]:
  CONCAT (cout (kanswers chatV [(Kv q, SOME (KvR (Lines s)))])) = s
Proof
  simp[kanswers_def, chatV_def] >> rw[]
QED

Theorem kanswers_CONS2[local]:
  kanswers chatV ((Kv q, SOME (KvR b)) :: tr) = SOME b :: kanswers chatV tr ∧
  kanswers chatV ((Sock x, r) :: tr) = kanswers chatV tr
Proof
  rw[kanswers_def, chatV_def] >> Cases_on ‘r’ >> simp[]
QED

Theorem kanswers_TAKE_CONS[local]:
  kanswers chatV (TAKE (SUC k) (e :: tr)) =
  kanswers chatV [e] ++ kanswers chatV (TAKE k tr)
Proof
  simp[GSYM kanswers_APPEND]
QED

(* MAIN: the lines the write loop from i was told, up to an answered
   Fetch, are the log at that Fetch from i *)
Theorem wloop_told:
  ∀R i lg.
    mono_log lg ∧ fits_log fd lg (trans (wloop (fd, i)) R) ∧
    i ≤ LENGTH (lg 0) ⇒
    ∀k. k < LENGTH (trans (wloop (fd, i)) R) ∧
        afetch fd (EL k (trans (wloop (fd, i)) R)) ⇒
        CONCAT (cout (kanswers chatV (TAKE (SUC k) (trans (wloop (fd, i)) R)))) =
        DROP i (lg k)
Proof
  gen_tac >> measureInduct_on ‘LENGTH R’ >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘fits_log _ _ _’ mp_tac >>
  ONCE_REWRITE_TAC[asyncChatModelTheory.wloop_unfold] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Fetch i))) K0) R’ >>
  qspecl_then [‘emit (Kv (fd, Fetch i))’, ‘K0’, ‘R’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[afetch_def]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rename1 ‘oHD s.results = SOME res’ >> strip_tac >>
  ‘(∀b. res ≠ KvR b) ∨ res = KvR (Lines (DROP i (lg 0)))’
    by (qpat_x_assum ‘fits_log _ _ _’
          (qspecl_then [‘0’, ‘i’] mp_tac o REWRITE_RULE[fits_log_def]) >>
        Cases_on ‘res’ >> simp[])
  >- (Cases_on ‘res’ >> gvs[Abbr ‘K0’, afetch_def] >>
      Cases >> simp[afetch_def]) >>
  gvs[Abbr ‘K0’] >>
  drule fits_log_CONS >> strip_tac >>
  ‘lg 0 ≼ lg 1’ by fs[mono_log_def] >>
  Cases >- simp[cout_kanswers_sing] >>
  rename1 ‘SUC k’ >> strip_tac >>
  ONCE_REWRITE_TAC[kanswers_TAKE_CONS] >>
  Cases_on ‘DROP i (lg 0) = ""’ >> gvs[]
  >- ((* nothing new: the same loop, one entry later *)
      ‘DROP i (lg 0) = ""’ by gvs[DROP_LENGTH_TOO_LONG] >>
      pop_assum SUBST1_TAC >> simp[kanswers_CONS2] >>
      first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >>
      disch_then (qspecl_then [‘i’, ‘λk. lg (k + 1)’] mp_tac) >>
      impl_tac
      >- (simp[mono_log_shift] >> imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
      disch_then (qspec_then ‘k’ mp_tac) >> simp[ADD1])
  >> qmatch_asmsub_abbrev_tac ‘trans (bind (emit WR) K1) h2’ >>
  qspecl_then [‘emit WR’, ‘K1’, ‘h2’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (gvs[] >> drule trans_emit_running >> strip_tac >> gvs[afetch_def, Abbr ‘WR’] >>
      Cases_on ‘k’ >> gvs[afetch_def])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘WR’, Abbr ‘K1’] >>
  Cases_on ‘k’ >> gvs[afetch_def] >> rename1 ‘SUC (SUC k)’ >>
  qpat_x_assum ‘fits_log _ (λk. _) (_ :: _)’ (assume_tac o MATCH_MP fits_log_CONS) >>
  fs[] >>
  ‘DROP i (lg 0) ≠ ""’ by fs[] >>
  ‘lg 0 ≼ lg (k + 2) ∧ lg 0 ≼ lg 2’ by fs[mono_log_def] >>
  first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
  disch_then (qspecl_then [‘STRLEN (lg 0)’, ‘λk. lg (k + 2)’] mp_tac) >>
  impl_tac
  >- (simp[mono_log_shift |> Q.GEN ‘n’ |> Q.SPEC ‘2’ |> SIMP_RULE arith_ss []] >>
      imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
  disch_then (qspec_then ‘k’ mp_tac) >> simp[afetch_def] >> strip_tac >>
  simp[kanswers_CONS2] >>
  ‘SUC (SUC k) = k + 2’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘LENGTH (lg 0) = i + LENGTH (DROP i (lg 0))’ by fs[] >>
  pop_assum (fn th => REWRITE_TAC[Once th]) >>
  irule DROP_grow >> qexists ‘lg 0’ >> simp[]
QED

(* MAIN: a writer told it joined at j has been told, up to an answered
   Fetch, the log at that Fetch from j *)
Theorem writer_told:
  mono_log lg ∧ fits_log fd lg (trans (writer fd) R) ∧
  trans (writer fd) R ≠ [] ∧
  SND (HD (trans (writer fd) R)) = SOME (KvR (Pos j)) ∧ j ≤ LENGTH (lg 0) ⇒
  ∀k. k < LENGTH (trans (writer fd) R) ∧ afetch fd (EL k (trans (writer fd) R)) ⇒
      CONCAT (cout (DROP 1 (kanswers chatV (TAKE (SUC k) (trans (writer fd) R))))) =
      DROP j (lg k)
Proof
  strip_tac >> qpat_x_assum ‘fits_log _ _ _’ mp_tac >>
  qpat_x_assum ‘SND (HD _) = _’ mp_tac >> qpat_x_assum ‘trans _ _ ≠ []’ mp_tac >>
  simp[asyncChatModelTheory.writer_def] >>
  qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Kv (fd, Start))) K0) R’ >>
  qspecl_then [‘emit (Kv (fd, Start))’, ‘K0’, ‘R’] mp_tac
    (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (ASM_REWRITE_TAC[] >> drule trans_emit_running >> simp[]) >>
  drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  rpt strip_tac >> gvs[Abbr ‘K0’] >>
  drule fits_log_CONS >> strip_tac >>
  ‘lg 0 ≼ lg 1’ by fs[mono_log_def] >>
  Cases_on ‘k’ >> gvs[afetch_def] >> rename1 ‘SUC k’ >>
  qspecl_then [‘h2’, ‘j’, ‘λk. lg (k + 1)’] mp_tac wloop_told >>
  impl_tac
  >- (simp[mono_log_shift] >> imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
  disch_then (qspec_then ‘k’ mp_tac) >> simp[afetch_def, ADD1] >>
  strip_tac >> simp[kanswers_CONS2]
QED
