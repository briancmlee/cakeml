(*
  The HTTP handler as a per-round state machine (model).

  Between rounds, the handler of connection fd (http_handler_h files (fd, b),
  asyncHttpServer) is always in one of three states:

     HA b   about to act on its buffer b: if b starts with a complete
            request, write its response this round; if b is incomplete,
            wait until fd is readable; if b is invalid, stop;
     HB b   reading fd this round (fd was reported readable), buffer b;
     HD b   stopped (invalid input, or end-of-file), buffer b.

  hacts: the actions of a round; hstep: the next state, given the next
  snapshot.  hcomp turns a state into the model computation it stands for,
  and suspended_hcomp says that the model's "one poll later" is the
  machine's step.  So, on a history where the world answers promptly, the
  handler's actions round by round are the machine's (hmachine_new_actions),
  and so is its transcript (hmachine_trans).
*)
Theory asyncHttpMachineH
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncCfActModel asyncProgress HttpSpec asyncHttpParse
  asyncHttpServer HttpSpecHeaders asyncHttpParseH asyncHttpServerH
Libs
  BasicProvers

Datatype:
  hst = HA string | HB string | HD string
End

(* What the handler does with the response to its read *)
Definition hafter_def:
  hafter files fd b res =
    case res of
      Data d => http_handler_h files (fd, b ++ d)
    | Eof => return ()
    | _ => http_handler_h files (fd, b)
End

(* The model computation a state stands for *)
Definition hcomp_def:
  hcomp files fd (HA b) = http_handler_h files (fd, b) ∧
  hcomp files fd (HB b) = bind (emit (Read fd)) (hafter files fd b) ∧
  hcomp files fd (HD b) = return ()
End

(* The response the handler writes for its buffer's first request *)
Definition hpend_def:
  hpend files (HA b) =
    (case parse_hrequest b of
       HComplete req rest => [print_response (handle files (hpath req))]
     | _ => []) ∧
  hpend files (HB b) = [] ∧
  hpend files (HD b) = []
End

(* The actions of a round *)
Definition hacts_def:
  hacts files fd (HA b) = MAP (Write fd) (hpend files (HA b)) ∧
  hacts files fd (HB b) = [Read fd] ∧
  hacts files fd (HD b) = []
End

(* The next state, given the next snapshot *)
Definition hstep_def:
  hstep files fd (HA b) s =
    (case parse_hrequest b of
       HComplete req rest => HA rest
     | HIncomplete => if Readable fd ∈ s.ready then HB b else HA b
     | HInvalid => HD b) ∧
  hstep files fd (HB b) s =
    (case oHD s.results of
       SOME (Data d) => HA (b ++ d)
     | SOME Eof => HD b
     | _ => HA b) ∧
  hstep files fd (HD b) s = HD b
End

(* The state after a history *)
Definition hrun_def:
  hrun files fd st g = FOLDL (hstep files fd) st g
End

Definition hbuf_def:
  hbuf (HA b) = b ∧ hbuf (HB b) = b ∧ hbuf (HD b) = b
End

Theorem hrun_SNOC:
  hrun files fd st (g ++ [s]) = hstep files fd (hrun files fd st g) s
Proof
  simp[hrun_def, FOLDL_APPEND]
QED

(* ------------------------------------------------------------------------
   The machine simulates the handler
   ------------------------------------------------------------------------ *)

Theorem prepend_NIL[local]:
  prepend [] g = g
Proof
  simp[FUN_EQ_THM, prepend_def, outcome_component_equality]
QED

Theorem skipping_0[local]:
  skipping 0 g = g
Proof
  simp[FUN_EQ_THM, skipping_def]
QED

Theorem bind_finished_NIL[local]:
  bind (finished [] x) f = f x
Proof
  simp[bind_finished, prepend_NIL, skipping_0]
QED

(* The handler in state HA b, for an incomplete buffer: wait, then read *)
Theorem http_handler_incomplete:
  parse_hrequest b = HIncomplete ⇒
  http_handler_h files (fd, b) =
    bind (readable fd) (λu. bind (emit (Read fd)) (hafter files fd b))
Proof
  strip_tac >> simp[Once http_handler_h_unfold] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  Cases >> simp[hafter_def]
QED

Theorem http_handler_complete:
  parse_hrequest b = HComplete req rest ⇒
  http_handler_h files (fd, b) =
    bind (emit (Write fd (print_response (handle files (hpath req)))))
         (λw. http_handler_h files (fd, rest))
Proof
  strip_tac >> simp[Once http_handler_h_unfold]
QED

Theorem http_handler_invalid:
  parse_hrequest b = HInvalid ⇒ http_handler_h files (fd, b) = return ()
Proof
  strip_tac >> simp[Once http_handler_h_unfold]
QED

Theorem wf_hcomp:
  wf (hcomp files fd st)
Proof
  Cases_on ‘st’ >> simp[hcomp_def, wf_http_handler_h, wf_return] >>
  irule wf_bind >> simp[wf_emit] >> Cases >>
  simp[hafter_def, wf_http_handler_h, wf_return]
QED

Theorem bind_wait_NIL[local]:
  (bind (wait p) f []).actions = []
Proof
  simp[bind_def, Once first_prefix_def, wait_def, first_some_def]
QED

(* The actions of the first round are the machine's *)
Theorem hcomp_NIL_actions:
  (hcomp files fd st []).actions = hacts files fd st
Proof
  Cases_on ‘st’ >> simp[hcomp_def, hacts_def, hpend_def, return_def]
  >- (Cases_on ‘parse_hrequest s’ >> simp[]
      >- (drule http_handler_complete >> simp[bind_emit_NIL])
      >- (drule http_handler_incomplete >> simp[] >>
          simp[readable_def, bind_wait_NIL])
      >> drule http_handler_invalid >> simp[return_def])
  >> simp[bind_emit_NIL]
QED

(* MAIN: one poll of a state's computation is the machine's step, given
   that the round's action (if any) is answered in the snapshot *)
Theorem suspended_hcomp:
  (hacts files fd st ≠ [] ⇒ s.results ≠ []) ⇒
  suspended (hcomp files fd st) [s] = hcomp files fd (hstep files fd st s)
Proof
  Cases_on ‘st’ >> simp[hcomp_def, hacts_def, hpend_def, hstep_def]
  >- (Cases_on ‘parse_hrequest s'’ >> simp[]
      >- (rename1 ‘HComplete req rest’ >> strip_tac >>
          drule http_handler_complete >> simp[] >> disch_then kall_tac >>
          Cases_on ‘s.results’ >> gvs[] >>
          simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
          ‘suspended (emit (Write fd (print_response (handle files (hpath req))))) [s] =
           finished [] h’ by metis_tac[suspended_emit_CONS] >>
          simp[bind_finished_NIL, hcomp_def])
      >- (rpt strip_tac >> drule http_handler_incomplete >> simp[] >> disch_then kall_tac >>
          simp[suspended_bind, readable_def, wf_wait, wait_needs_snapshot] >>
          qmatch_goalsub_abbrev_tac ‘suspended (wait P) [s]’ >> rw[]
          >- (‘suspended (wait P : (event, asyncServer$response) snapshot list -> (asyncServer$action, unit option) asyncCore$outcome) [s] = finished [] ()’
                by (irule suspended_wait_SOME >> simp[Abbr ‘P’]) >>
              pop_assum SUBST1_TAC >> simp[bind_finished_NIL, hcomp_def])
          >> ‘suspended (wait P : (event, asyncServer$response) snapshot list -> (asyncServer$action, unit option) asyncCore$outcome) [s] = wait P’
               by (irule suspended_wait_NONE >> simp[Abbr ‘P’]) >>
          pop_assum SUBST1_TAC >> simp[hcomp_def] >> drule http_handler_incomplete >> simp[Abbr ‘P’, readable_def])
      >> rpt strip_tac >> drule http_handler_invalid >> simp[hcomp_def] >>
      simp[return_finished, suspended_finished_one])
  >- (strip_tac >> Cases_on ‘s.results’ >> gvs[] >>
      simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
      ‘suspended (emit (Read fd)) [s] = finished [] h’
        by metis_tac[suspended_emit_CONS] >>
      simp[bind_finished_NIL] >>
      Cases_on ‘h’ >> simp[hafter_def, hcomp_def])
  >> simp[return_finished, suspended_finished_one]
QED

(* ------------------------------------------------------------------------
   Iterating: the state after a history, and the actions round by round
   ------------------------------------------------------------------------ *)

(* MAIN: after a history in which every round's action is answered, the
   computation is the machine's state *)
Theorem hrun_suspended:
  ∀g st.
    (∀j. j < LENGTH g ∧ hacts files fd (hrun files fd st (TAKE j g)) ≠ [] ⇒
         (EL j g).results ≠ []) ⇒
    suspended (hcomp files fd st) g = hcomp files fd (hrun files fd st g)
Proof
  Induct_on ‘g’ using SNOC_INDUCT >- simp[hrun_def] >>
  rpt strip_tac >> simp[SNOC_APPEND, hrun_SNOC] >>
  ‘suspended (hcomp files fd st) (g ++ [x]) =
   suspended (suspended (hcomp files fd st) g) [x]’
    by simp[suspended_suspended_one, wf_hcomp] >>
  pop_assum SUBST1_TAC >>
  ‘suspended (hcomp files fd st) g = hcomp files fd (hrun files fd st g)’
    by (first_x_assum irule >> rpt strip_tac >>
        first_x_assum (qspec_then ‘j’ mp_tac) >>
        simp[SNOC_APPEND, TAKE_APPEND1, EL_APPEND1]) >>
  pop_assum SUBST1_TAC >> irule suspended_hcomp >> strip_tac >>
  first_x_assum (qspec_then ‘LENGTH g’ mp_tac) >>
  simp[SNOC_APPEND, TAKE_LENGTH_APPEND, EL_APPEND2]
QED

(* With a prompt world, every round's action is answered *)
Theorem hmachine_answered:
  prompt (hcomp files fd st) g ⇒
  ∀j. j < LENGTH g ⇒
      LENGTH (hacts files fd (hrun files fd st (TAKE j g))) ≤ LENGTH (EL j g).results
Proof
  strip_tac >> completeInduct_on ‘j’ >> strip_tac >>
  ‘hacts files fd (hrun files fd st (TAKE j g)) =
   new_actions (log_of (hcomp files fd st)) (TAKE j g)’
    by (‘hrun files fd st (TAKE j g) = hrun files fd st (TAKE j g)’ by simp[] >>
        simp[GSYM hcomp_NIL_actions, GSYM suspended_first_poll, wf_hcomp] >>
        AP_TERM_TAC >> AP_THM_TAC >> CONV_TAC SYM_CONV >> irule hrun_suspended >>
        rpt strip_tac >> ‘j' < j’ by gvs[LENGTH_TAKE] >>
        gvs[TAKE_TAKE, EL_TAKE] >>
        first_x_assum (qspec_then ‘j'’ mp_tac) >> simp[] >>
        Cases_on ‘hacts files fd (hrun files fd st (TAKE j' g))’ >> gvs[]) >>
  gvs[prompt_def] >> first_x_assum drule >> simp[responses_at_def]
QED

(* MAIN: with a prompt world, the actions of each round are the machine's *)
Theorem hmachine_new_actions:
  prompt (hcomp files fd st) g ∧ j ≤ LENGTH g ⇒
  new_actions (log_of (hcomp files fd st)) (TAKE j g) =
  hacts files fd (hrun files fd st (TAKE j g))
Proof
  strip_tac >>
  simp[GSYM hcomp_NIL_actions, GSYM suspended_first_poll, wf_hcomp] >>
  AP_TERM_TAC >> AP_THM_TAC >> irule hrun_suspended >>
  rpt strip_tac >> gvs[LENGTH_TAKE_EQ, TAKE_TAKE_MIN, EL_TAKE] >>
  drule hmachine_answered >> disch_then (qspec_then ‘j'’ mp_tac) >>
  simp[MIN_DEF] >> gvs[MIN_DEF] >>
  Cases_on ‘(EL j' g).results’ >> simp[] >>
  Cases_on ‘hacts files fd (hrun files fd st (TAKE j' g))’ >> gvs[]
QED

(* MAIN: with a prompt world, the transcript is the machine's: each round's
   actions paired with the next snapshot's responses *)
Theorem hmachine_trans:
  prompt (hcomp files fd st) g ⇒
  trans (hcomp files fd st) g =
  FLAT (GENLIST (λj. zipr (hacts files fd (hrun files fd st (TAKE j g)))
                          (responses_at g j)) (SUC (LENGTH g)))
Proof
  strip_tac >> simp[trans_def] >> AP_TERM_TAC >>
  simp[GENLIST_FUN_EQ, round_trans_def] >> rpt strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> irule hmachine_new_actions >> simp[]
QED

(* ------------------------------------------------------------------------
   What the handler has read and written, in terms of its state
   ------------------------------------------------------------------------ *)

(* The transcript up to round n *)
Theorem hmachine_trans_TAKE:
  prompt (hcomp files fd st0) g ∧ n ≤ LENGTH g ⇒
  trans (hcomp files fd st0) (TAKE n g) =
  FLAT (GENLIST (λi. zipr (hacts files fd (hrun files fd st0 (TAKE i g)))
                          (if i < n then (EL i g).results else [])) (SUC n))
Proof
  strip_tac >>
  ‘prompt (hcomp files fd st0) (TAKE n g)’ by simp[prompt_TAKE] >>
  drule hmachine_trans >> simp[LENGTH_TAKE] >> disch_then kall_tac >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ] >> rpt strip_tac >>
  simp[TAKE_TAKE, responses_at_def, EL_TAKE, LENGTH_TAKE]
QED

(* The transcript up to round j, and up to round j + 1 *)
Theorem hmachine_trans_SUC:
  prompt (hcomp files fd st0) g ∧ j < LENGTH g ⇒
  let TR = FLAT (GENLIST (λi. zipr (hacts files fd (hrun files fd st0 (TAKE i g)))
                                    (EL i g).results) j) in
  trans (hcomp files fd st0) (TAKE j g) =
    TR ++ zipr (hacts files fd (hrun files fd st0 (TAKE j g))) [] ∧
  trans (hcomp files fd st0) (TAKE (SUC j) g) =
    TR ++ zipr (hacts files fd (hrun files fd st0 (TAKE j g))) (EL j g).results ++
    zipr (hacts files fd (hrun files fd st0 (TAKE (SUC j) g))) []
Proof
  strip_tac >> simp[] >>
  ‘∀k. k ≤ j ⇒
       GENLIST (λi. zipr (hacts files fd (hrun files fd st0 (TAKE i g)))
                        (if i < k then (EL i g).results else [])) k =
       GENLIST (λi. zipr (hacts files fd (hrun files fd st0 (TAKE i g)))
                        (EL i g).results) k’
    by simp[GENLIST_FUN_EQ] >>
  ‘∀k. k ≤ SUC j ⇒
       GENLIST (λi. zipr (hacts files fd (hrun files fd st0 (TAKE i g)))
                        (if i < SUC j then (EL i g).results else [])) k =
       GENLIST (λi. zipr (hacts files fd (hrun files fd st0 (TAKE i g)))
                        (EL i g).results) k’
    by simp[GENLIST_FUN_EQ] >>
  simp[hmachine_trans_TAKE, GENLIST, SNOC_APPEND]
QED

Theorem read_zipr_NIL[simp]:
  ∀as. read fd (zipr as []) = []
Proof
  Induct >> simp[zipr_def] >> Cases >> simp[]
QED

(* The strings written to fd by a list of actions, whatever the responses *)
Definition writes_def:
  writes fd as =
    FLAT (MAP (λa. case a of Write fd' d => if fd' = fd then [d] else [] | _ => []) as)
End

Theorem written_zipr:
  ∀as rs. written fd (zipr as rs) = writes fd as
Proof
  Induct >> simp[zipr_def, writes_def] >> Cases >> simp[writes_def]
QED

Theorem writes_hacts[simp]:
  writes fd (hacts files fd st) = hpend files st
Proof
  Cases_on ‘st’ >> simp[hacts_def, hpend_def, writes_def] >>
  CASE_TAC >> simp[]
QED

Theorem parse_all_h_print:
  ∀rs. EVERY valid_hrequest rs ⇒
       parse_all_h (FLAT (MAP print_hrequest rs) ++ s) = rs ++ parse_all_h s
Proof
  Induct >> rw[] >>
  ‘parse_hrequest (print_hrequest h ++ (FLAT (MAP print_hrequest rs) ++ s)) =
   HComplete h (FLAT (MAP print_hrequest rs) ++ s)’ by simp[parse_hprint] >>
  drule parse_all_h_Complete >> REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED

(* MAIN: the handler's accounting.  Started on buffer b0, after any prompt
   history, there are valid requests rs that it has completely handled:
   its buffer before, followed by what it has read, is rs printed,
   followed by its current buffer; and what it has written is the
   responses to rs, followed by the response it is writing this round (if
   its buffer starts with a complete request).  It only reads with an
   incomplete buffer, and it stops only on a buffer that does not start
   with a complete request. *)
Theorem hmachine_inv:
  prompt (hcomp files fd (HA b0)) g ⇒
  ∀j. j ≤ LENGTH g ⇒
    ∃rs. EVERY valid_hrequest rs ∧
         b0 ++ CONCAT (read fd (trans (hcomp files fd (HA b0)) (TAKE j g))) =
           FLAT (MAP print_hrequest rs) ++ hbuf (hrun files fd (HA b0) (TAKE j g)) ∧
         written fd (trans (hcomp files fd (HA b0)) (TAKE j g)) =
           MAP (print_response o handle files o hpath) rs ++
           hpend files (hrun files fd (HA b0) (TAKE j g)) ∧
         (∀b. hrun files fd (HA b0) (TAKE j g) = HB b ⇒ parse_hrequest b = HIncomplete) ∧
         (∀b r rest. hrun files fd (HA b0) (TAKE j g) = HD b ⇒
                     parse_hrequest b ≠ HComplete r rest)
Proof
  strip_tac >> Induct
  >- (simp[hrun_def, hbuf_def] >> qexists_tac ‘[]’ >>
      simp[trans_def, round_trans_def, responses_at_def, written_zipr] >>
      simp[new_actions_NIL, log_of_def, hcomp_NIL_actions])
  >> strip_tac >> gvs[]
  >> drule_then (qspec_then ‘j’ mp_tac) hmachine_trans_SUC >> simp[] >> strip_tac
  >> qmatch_asmsub_abbrev_tac ‘TR ++ zipr _ []’
  >> ‘TAKE (SUC j) g = TAKE j g ++ [EL j g]’ by simp[GSYM SNOC_EL_TAKE, SNOC_APPEND]
  >> qabbrev_tac ‘st = hrun files fd (HA b0) (TAKE j g)’
  >> ‘hrun files fd (HA b0) (TAKE (SUC j) g) = hstep files fd st (EL j g)’
       by simp[hrun_SNOC, Abbr ‘st’]
  >> drule_then (qspec_then ‘j’ mp_tac) hmachine_answered >> simp[] >> strip_tac
  >> gvs[written_zipr]
  >> Cases_on ‘st’ >> gvs[hstep_def, hbuf_def, hpend_def, hacts_def]
  (* HA s *)
  >- (Cases_on ‘parse_hrequest s’ >> gvs[hbuf_def, hpend_def]
      (* a complete request: its response is written; continue with rest *)
      >- (rename1 ‘HComplete req rest’ >>
          Cases_on ‘(EL j g).results’ >> gvs[zipr_def] >>
          drule parse_hcomplete >> strip_tac >>
          qexists_tac ‘rs ++ [req]’ >> gvs[written_zipr, writes_def])
      (* incomplete: wait, or read next round *)
      >- (rw[hbuf_def, hpend_def] >> qexists_tac ‘rs’ >> simp[zipr_def] >>
          gvs[hpend_def, zipr_def])
      (* invalid: stop *)
      >> qexists_tac ‘rs’ >> gvs[hbuf_def, hpend_def, zipr_def])
  (* HB s: the read's response arrives *)
  >- (Cases_on ‘(EL j g).results’ >> gvs[zipr_def] >>
      rename1 ‘_ = r :: _’ >> Cases_on ‘r’ >> gvs[hbuf_def, hpend_def] >>
      qexists_tac ‘rs’ >> simp[] >> gvs[])
  (* HD s *)
  >> qexists_tac ‘rs’ >> gvs[hbuf_def, hpend_def, zipr_def]
QED
