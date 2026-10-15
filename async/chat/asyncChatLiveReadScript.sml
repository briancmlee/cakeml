(*
  ChatSpec's second liveness clause (reads), part 1: progress of the chat
  reader.  The development follows the echo handler's (model/asyncProgress:
  handler_progress), at the chat handler's types and without the write.

  MAIN: reader_progress.  If fd is readable in three snapshots in a row and
  the world answers promptly, the reader reads fd during those rounds,
  unless it has already seen end-of-file.
*)
Theory asyncChatLiveRead
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncWithStore asyncChatModel asyncChatSafe
Libs
  BasicProvers

Type rh = “: (event, (canswer, asyncServer$response) kres) snapshot list”
Type ract = “: (asyncServer$action, num # cquery) kact”

Overload creader = “λfd. (reader fd : rh -> (ract, unit option) outcome)”

(* The reads of fd among some actions *)
Definition nreadc_def:
  nreadc fd (acts : ract list) = LENGTH (FILTER (λa. a = Sock (Read fd)) acts)
End

Theorem nreadc_simps[simp]:
  nreadc fd [] = 0 ∧
  nreadc fd (a :: as) = (if a = Sock (Read fd) then 1 else 0) + nreadc fd as ∧
  nreadc fd (as ++ bs) = nreadc fd as + nreadc fd bs
Proof
  rw[nreadc_def, FILTER_APPEND_DISTRIB]
QED

(* h ends with the first snapshot in which fd is readable *)
Definition first_readable_c_def:
  first_readable_c fd (h : rh) ⇔
    first_done (readable fd : rh -> (ract, unit option) outcome) h ()
End

Theorem first_readable_c_nonempty:
  first_readable_c fd h1 ⇒ h1 ≠ []
Proof
  rw[first_readable_c_def, first_done_def, readable_def, wait_def]
  >> strip_tac >> gvs[first_some_def]
QED

Theorem readable_c_not_before:
  first_readable_c fd h1 ∧ j + 1 < LENGTH h1 ⇒
  Readable fd ∉ (EL j h1).ready
Proof
  rw[first_readable_c_def, first_done_def] >> first_x_assum (qspec_then ‘j + 1’ mp_tac)
  >> simp[readable_def, wait_def] >> strip_tac
  >> ‘∀l : rh.
        first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) l = NONE ⇒
          ∀j. j < LENGTH l ⇒ Readable fd ∉ (EL j l).ready’
       by (Induct >> simp[first_some_def] >> rw[] >> Cases_on ‘j'’ >> gvs[])
  >> first_x_assum drule >> disch_then (qspec_then ‘j’ mp_tac)
  >> simp[EL_TAKE]
QED

Theorem readable_c_now:
  Readable fd ∈ (s : (event, (canswer, asyncServer$response) kres) snapshot).ready ⇒
  first_readable_c fd [s]
Proof
  rw[first_readable_c_def, first_done_def, readable_def, wait_def, first_some_def]
QED

(* If fd is readable somewhere in h, waiting for it finishes in h *)
Theorem readable_c_split:
  j < LENGTH (h : rh) ∧ Readable fd ∈ (EL j h).ready ⇒
  ∃h1 h2. h = h1 ++ h2 ∧ first_readable_c fd h1 ∧ LENGTH h1 ≤ j + 1
Proof
  strip_tac
  >> qspecl_then [‘readable fd : rh -> (ract, unit option) outcome’, ‘h’]
       strip_assume_tac history_split
  >- (first_x_assum (qspec_then ‘j + 1’ mp_tac)
      >> simp[readable_def, wait_def]
      >> ‘∀(l : rh) j.
            j < LENGTH l ∧ Readable fd ∈ (EL j l).ready ⇒
                first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) l ≠ NONE’
           by (Induct >> simp[first_some_def] >> rw[] >> Cases_on ‘j'’ >> gvs[]
               >> metis_tac[])
      >> strip_tac >> first_x_assum (qspecl_then [‘TAKE (j + 1) h’, ‘j’] mp_tac)
      >> simp[EL_TAKE])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[]
  >> qexistsl_tac [‘h1’, ‘h2’] >> simp[first_readable_c_def]
  >> CCONTR_TAC >> gvs[NOT_LESS_EQUAL]
  >> ‘first_readable_c fd h1’ by simp[first_readable_c_def]
  >> drule readable_c_not_before >> disch_then (qspec_then ‘j’ mp_tac)
  >> gvs[EL_APPEND1]
QED

(* ------------------------------------------------------------------------
   The reader, step by step
   ------------------------------------------------------------------------ *)

Definition after_read_c_def:
  after_read_c fd (res : (canswer, asyncServer$response) kres) =
    case res of
      SockR Eof => (return () : rh -> (ract, unit option) outcome)
    | _ => creader fd
End

Theorem reader_steps:
  creader fd =
    bind (readable fd) (λu. bind (emit (Sock (Read fd))) (after_read_c fd))
Proof
  simp[Once reader_unfold] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, after_read_c_def]
QED

Theorem reader_waiting:
  first_readable_c fd h1 ∧ n < LENGTH h1 ⇒ (creader fd (TAKE n h1)).actions = []
Proof
  rw[] >> ONCE_REWRITE_TAC[reader_steps]
  >> ‘bind (readable fd) (λu. bind (emit (Sock (Read fd))) (after_read_c fd)) (TAKE n h1) =
      <|actions := (readable fd (TAKE n h1)).actions; result := NONE|>’
       by (irule bind_before_first_done >> gvs[first_readable_c_def] >> metis_tac[])
  >> simp[readable_def, wait_def]
QED

Theorem reader_reads:
  first_readable_c fd h1 ⇒
  creader fd (h1 ++ q) = bind (emit (Sock (Read fd))) (after_read_c fd) q
Proof
  rw[first_readable_c_def] >> ONCE_REWRITE_TAC[reader_steps]
  >> drule_then (qspecl_then [‘λu. bind (emit (Sock (Read fd))) (after_read_c fd)’, ‘q’]
                 mp_tac) bind_continues
  >> simp[new_actions_def, log_of_def, readable_def, wait_def]
  >> simp[outcome_component_equality]
QED

Theorem reader_fresh_reads:
  q ≠ [] ∧ Readable fd ∈ (HD q).ready ∧ 1 ≤ i ⇒
  1 ≤ nreadc fd (creader fd (TAKE i q)).actions
Proof
  Cases_on ‘q’ >> rw[]
  >> drule readable_c_now >> strip_tac
  >> ‘TAKE i (h::t) = [h] ++ TAKE (i - 1) t’ by (Cases_on ‘i’ >> gvs[])
  >> drule_then (qspec_then ‘TAKE (i - 1) t’ mp_tac) reader_reads
  >> simp[] >> strip_tac
  >> qspecl_then [‘Sock (Read fd)’, ‘after_read_c fd’, ‘TAKE (i - 1) t’] strip_assume_tac
       (Q.GENL [‘a’, ‘f’, ‘q’] bind_emit_starts)
  >> simp[]
QED

Theorem reader_after_read:
  first_readable_c fd h1 ∧ oHD s.results = SOME r ⇒
  (creader fd (h1 ++ s :: q)).actions = Sock (Read fd) :: (after_read_c fd r q).actions
Proof
  rpt strip_tac >> drule_then (qspec_then ‘s :: q’ SUBST1_TAC) reader_reads
  >> qspecl_then [‘s’, ‘r’, ‘Sock (Read fd)’, ‘after_read_c fd’, ‘q’] mp_tac
       (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS)
  >> simp[]
QED

Theorem reader_trans_read:
  first_readable_c fd h1 ∧ oHD s.results = SOME r ⇒
  trans (creader fd) (h1 ++ s :: q) =
    (Sock (Read fd), SOME r) :: trans (after_read_c fd r) q
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[reader_steps]
  >> qspecl_then [‘readable fd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Sock (Read fd))) (after_read_c fd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> impl_tac >- gvs[first_readable_c_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> disch_then kall_tac
  >> qspecl_then [‘emit (Sock (Read fd))’, ‘[s]’, ‘r’, ‘after_read_c fd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] trans_bind_continues)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME, trans_emit, readable_def]
QED

Theorem reader_new_read:
  first_readable_c fd h1 ⇒
  new_actions (log_of (creader fd)) h1 = [Sock (Read fd)]
Proof
  rw[] >> drule first_readable_c_nonempty >> strip_tac
  >> ‘(creader fd h1).actions = [Sock (Read fd)]’
       by (drule_then (qspec_then ‘[]’ mp_tac) reader_reads >> simp[bind_emit_NIL])
  >> ‘(creader fd (FRONT h1)).actions = []’
       by (‘FRONT h1 = TAKE (LENGTH h1 - 1) h1’ by simp[FRONT_BY_TAKE]
           >> simp[] >> irule reader_waiting >> simp[]
           >> Cases_on ‘h1’ >> gvs[])
  >> simp[new_actions_def, log_of_def]
QED

Theorem prompt_reader_answered:
  prompt (creader fd) (h1 ++ s :: q) ∧ first_readable_c fd h1 ⇒
  ∃r. oHD s.results = SOME r
Proof
  rw[prompt_def] >> first_x_assum (qspec_then ‘LENGTH h1’ mp_tac)
  >> simp[TAKE_LENGTH_APPEND, responses_at_def, EL_APPEND2]
  >> drule reader_new_read >> simp[]
  >> Cases_on ‘s.results’ >> simp[]
QED

Theorem prompt_reader_after:
  prompt (creader fd) (h1 ++ s :: q) ∧ first_readable_c fd h1 ∧
  oHD s.results = SOME r ⇒
  prompt (after_read_c fd r) q
Proof
  rpt strip_tac
  >> qpat_x_assum ‘prompt _ _’ (mp_tac o ONCE_REWRITE_RULE[reader_steps])
  >> strip_tac
  >> qspecl_then [‘readable fd’, ‘h1’, ‘()’,
                  ‘λu. bind (emit (Sock (Read fd))) (after_read_c fd)’, ‘s :: q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> impl_tac >- gvs[first_readable_c_def, readable_def, wf_wait, settled_wait]
  >> simp[] >> strip_tac
  >> qspecl_then [‘emit (Sock (Read fd))’, ‘[s]’, ‘r’, ‘after_read_c fd’, ‘q’] mp_tac
       (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘q’] prompt_bind)
  >> simp[wf_emit, settled_emit, first_done_emit_SOME]
QED

Theorem TAKE_after_c[local]:
  LENGTH h1 ≤ i ⇒ TAKE i (h1 ++ h2) = h1 ++ TAKE (i - LENGTH h1) h2
Proof
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem TAKE_before_c[local]:
  i ≤ LENGTH h1 ⇒ TAKE i (h1 ++ h2) = TAKE i h1
Proof
  simp[TAKE_APPEND1]
QED

(* MAIN: progress of the reader *)
Theorem reader_progress:
  ∀g k. prompt (creader fd) g ∧ k + 3 ≤ LENGTH g ∧
        (∀j. k ≤ j ∧ j < k + 3 ⇒ Readable fd ∈ (EL j g).ready) ∧
        ¬MEM (Sock (Read fd), SOME (SockR Eof)) (trans (creader fd) g) ⇒
        nreadc fd (creader fd (TAKE k g)).actions <
        nreadc fd (creader fd (TAKE (k + 3) g)).actions
Proof
  gen_tac >> measureInduct_on ‘LENGTH g’ >> rpt strip_tac
  >> qspecl_then [‘k’, ‘g’, ‘fd’] mp_tac (Q.GENL [‘j’, ‘h’, ‘fd’] readable_c_split)
  >> simp[] >> strip_tac >> gvs[]
  >> Cases_on ‘LENGTH h1 = k + 1’
  >- (‘(creader fd (TAKE k (h1 ++ h2))).actions = []’
        by simp[TAKE_before_c, reader_waiting]
      >> simp[TAKE_after_c] >> drule_then (qspec_then ‘TAKE 2 h2’ SUBST1_TAC) reader_reads
      >> qspecl_then [‘Sock (Read fd)’, ‘after_read_c fd’, ‘TAKE 2 h2’] strip_assume_tac
           (Q.GENL [‘a’, ‘f’, ‘q’] bind_emit_starts)
      >> simp[])
  >> ‘LENGTH h1 ≤ k’ by simp[] >> Cases_on ‘h2’ >- gvs[] >> rename1 ‘h1 ++ s1 :: h3’
  >> drule_all prompt_reader_answered >> strip_tac
  >> ‘∀i. LENGTH h1 + 1 ≤ i ⇒
          nreadc fd (creader fd (TAKE i (h1 ++ s1 :: h3))).actions =
          1 + nreadc fd (after_read_c fd r (TAKE (i - LENGTH h1 - 1) h3)).actions’
       by (rpt strip_tac >> simp[TAKE_after_c]
           >> ‘TAKE (i − LENGTH h1) (s1::h3) = s1 :: TAKE (i - LENGTH h1 - 1) h3’
                by (Cases_on ‘i - LENGTH h1’ >> gvs[])
           >> drule_all reader_after_read
           >> disch_then (qspec_then ‘TAKE (i − (LENGTH h1 + 1)) h3’
                (fn th => REWRITE_TAC[REWRITE_RULE[GSYM APPEND_ASSOC, APPEND] th]))
           >> simp[])
  >> ‘nreadc fd (creader fd (TAKE (LENGTH h1) (h1 ++ s1 :: h3))).actions = 1’
       by (simp[TAKE_LENGTH_APPEND] >> ‘h1 = h1 ++ []’ by simp[]
           >> pop_assum SUBST1_TAC >> drule reader_reads >> simp[bind_emit_NIL])
  >> ‘r ≠ SockR Eof’
       by (strip_tac >> gvs[] >> drule_all reader_trans_read
           >> disch_then (qspec_then ‘h3’
                (fn th => gvs[REWRITE_RULE[GSYM APPEND_ASSOC, APPEND] th])))
  >> ‘after_read_c fd r = creader fd’
       by (Cases_on ‘r’ >> simp[after_read_c_def] >> every_case_tac >> gvs[])
  >> ‘trans (creader fd) (h1 ++ s1 :: h3) =
      (Sock (Read fd), SOME r) :: trans (creader fd) h3’
       by (drule_all reader_trans_read
           >> disch_then (qspec_then ‘h3’
                (fn th => REWRITE_TAC[REWRITE_RULE[GSYM APPEND_ASSOC, APPEND] th]))
           >> simp[])
  >> gvs[]
  >> Cases_on ‘LENGTH h1 + 1 ≤ k’
  >- (first_x_assum (qspec_then ‘h3’ mp_tac) >> simp[]
      >> disch_then (qspec_then ‘k - LENGTH h1 - 1’ mp_tac)
      >> impl_tac
      >- (rpt conj_tac
          >- (drule_all prompt_reader_after >> simp[])
          >- simp[]
          >> rpt strip_tac
          >> ‘EL j h3 = EL (j + LENGTH h1 + 1) (h1 ++ s1 :: h3)’
               by simp[EL_APPEND2, EL_CONS, PRE_SUB1]
          >> simp[])
      >> ‘k − LENGTH h1 − 1 + 3 = k + 2 − LENGTH h1 ∧
          k − LENGTH h1 − 1 = k − (LENGTH h1 + 1)’ by simp[]
      >> simp[])
  >> ‘k = LENGTH h1’ by simp[] >> gvs[]
  >> ‘h3 ≠ [] ∧ Readable fd ∈ (HD h3).ready’
       by (Cases_on ‘h3’ >> gvs[]
           >> qpat_x_assum ‘∀j. _ ≤ j ∧ _ ⇒ _’ (qspec_then ‘LENGTH h1 + 1’ mp_tac)
           >> simp[EL_APPEND2, EL_CONS, PRE_SUB1])
  >> qspecl_then [‘h3’, ‘fd’, ‘2’] mp_tac (Q.GENL [‘q’, ‘fd’, ‘i’] reader_fresh_reads)
  >> simp[]
QED
