(*
  What makes the echo server act (model).

  The progress lemmas (echoProgress) say: once fd is readable, the
  handler reads it soon.  Quiescence needs the converse: the handler
  emits a new action only because of the newest snapshot, i.e. its fd
  became readable in it, or it brought the response Data d to a read
  (which the handler echoes).  Nothing else wakes it up.

  MAIN: handler_cause.
*)
Theory echoCause
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncTranscript echoServer
  echoServerSafety echoProgress
Libs
  preamble

(* The wait for fd finishes exactly at the snapshot that has fd readable *)
Theorem first_readable_last:
  first_readable fd (q ++ [s]) ⇒ Readable fd ∈ s.ready
Proof
  rw[first_readable_def, first_done_def, readable_def, wait_def] >>
  CCONTR_TAC >>
  ‘∀l : (event, response) snapshot list.
     first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) (l ++ [s]) =
     first_some (λs. if Readable fd ∈ s.ready then SOME () else NONE) l’
    by (Induct >> simp[first_some_def] >> rw[]) >>
  gvs[] >>
  first_x_assum (qspec_then ‘LENGTH q’ mp_tac) >> simp[TAKE_LENGTH_APPEND]
QED

(* An emit whose response did not arrive in its first snapshot never
   finishes (emit's result is the first snapshot's first result) *)
Theorem bind_emit_unanswered:
  oHD s.results = NONE ⇒ (bind (emit a) f (s :: t)).actions = [a]
Proof
  strip_tac >>
  ‘bind (emit a) f (s :: t) = <| actions := (emit a (s :: t)).actions; result := NONE |>’
    by (irule bind_running >> Cases >> simp[emit_def]) >>
  simp[emit_def]
QED

Theorem handler_NIL:
  (handler fd []).actions = []
Proof
  ONCE_REWRITE_TAC[handler_steps] >> DEP_REWRITE_TAC[bind_running] >>
  simp[readable_def, wait_def, first_some_def]
QED

(* MAIN: the handler's actions change with a new snapshot s only if fd is
   readable in s, or s brings Data in response to a read *)
Theorem handler_cause:
  ∀q s. (handler fd (q ++ [s])).actions ≠ (handler fd q).actions ⇒
        Readable fd ∈ s.ready ∨ ∃d. oHD s.results = SOME (Data d)
Proof
  gen_tac >> completeInduct_on ‘LENGTH q’ >> rpt strip_tac >> gvs[PULL_FORALL] >>
  qspecl_then [‘readable fd : (event, response) snapshot list ->
                              (action, unit option) outcome’, ‘q ++ [s]’]
    strip_assume_tac history_split
  (* still waiting after s: no actions either way *)
  >- (‘(handler fd (q ++ [s])).actions = [] ∧ (handler fd q).actions = []’
        by (ONCE_REWRITE_TAC[handler_steps] >>
            ‘∀h. h ≼ q ++ [s] ⇒
                 (bind (readable fd) (λu. bind (emit (Read fd)) (after_read fd)) h).actions = []’
              by (rpt strip_tac >>
                  ‘bind (readable fd) (λu. bind (emit (Read fd)) (after_read fd)) h =
                   <| actions := (readable fd h).actions; result := NONE |>’
                    by (irule bind_running >> rpt strip_tac >>
                        gvs[IS_PREFIX_EQ_TAKE] >>
                        first_x_assum (qspec_then ‘MIN n n'’ mp_tac) >>
                        simp[TAKE_TAKE_MIN]) >>
                  simp[readable_def, wait_def]) >>
            simp[]) >>
      gvs[])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[] >>
  ‘first_readable fd h1’ by simp[first_readable_def] >>
  Cases_on ‘h2’ using SNOC_CASES
  (* the wait finished at s itself *)
  >- (disj1_tac >> gvs[] >> metis_tac[first_readable_last])
  >> ‘s = x ∧ q = h1 ++ l’
       by (‘SNOC s q = SNOC x (h1 ++ l)’ by gvs[SNOC_APPEND] >> fs[SNOC_11])
  >> gvs[] >> rename1 ‘h1 ++ q2’ >> Cases_on ‘q2’
  (* s brings the response to the read *)
  >- (gvs[] >> drule handler_reads >> strip_tac >>
      first_assum (qspec_then ‘[]’ (assume_tac o SIMP_RULE (srw_ss()) [])) >>
      gvs[bind_emit_NIL] >>
      Cases_on ‘oHD s.results’ >- gvs[bind_emit_unanswered] >>
      rename1 ‘oHD s.results = SOME r’ >>
      drule_all handler_after_read >> disch_then (qspec_then ‘[]’ assume_tac) >>
      gvs[] >>
      Cases_on ‘r’ >> gvs[after_read_def, bind_emit_NIL, return_def, handler_NIL])
  (* after the read's response r, in s1: as after_read fd r *)
  >> rename1 ‘h1 ++ s1 :: q3’ >>
  qpat_x_assum ‘_ ≠ _’ (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >>
  Cases_on ‘oHD s1.results’
  >- (drule handler_reads >> strip_tac >> qpat_x_assum ‘_ ≠ _’ mp_tac >>
      ASM_REWRITE_TAC[] >> simp[bind_emit_unanswered])
  >> rename1 ‘oHD s1.results = SOME r’ >> drule_all handler_after_read >>
  disch_then (fn th => qpat_x_assum ‘_ ≠ _’ (mp_tac o REWRITE_RULE[th])) >> simp[] >>
  Cases_on ‘r’
  (* Data d: the write, then the handler again *)
  >- (rename1 ‘Data d’ >> Cases_on ‘q3’
      >- (simp[after_read_data_NIL] >> Cases_on ‘oHD s.results’
          >- simp[after_read_def, bind_emit_unanswered]
          >> drule after_read_data_CONS >> simp[handler_NIL])
      >> rename1 ‘s2 :: q4’ >> Cases_on ‘oHD s2.results’
      >- simp[after_read_def, bind_emit_unanswered]
      >> drule after_read_data_CONS >> simp[] >> strip_tac >>
      first_x_assum (qspecl_then [‘q4’, ‘s’] mp_tac) >> simp[])
  (* EOF: finished; other responses: the handler again *)
  >> simp[after_read_def, return_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘q3’, ‘s’] mp_tac) >> simp[]
QED
