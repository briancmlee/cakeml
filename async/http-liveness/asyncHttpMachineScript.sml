(*
  The HTTP handler as a per-round state machine (model).

  Between rounds, the handler of connection fd (http_handler files (fd, b),
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
Theory asyncHttpMachine
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncCfActModel asyncProgress HttpSpec asyncHttpParse
  asyncHttpServer
Libs
  BasicProvers

Datatype:
  hst = HA string | HB string | HD string
End

(* What the handler does with the response to its read *)
Definition hafter_def:
  hafter files fd b res =
    case res of
      Data d => http_handler files (fd, b ++ d)
    | Eof => return ()
    | _ => http_handler files (fd, b)
End

(* The model computation a state stands for *)
Definition hcomp_def:
  hcomp files fd (HA b) = http_handler files (fd, b) ∧
  hcomp files fd (HB b) = bind (emit (Read fd)) (hafter files fd b) ∧
  hcomp files fd (HD b) = return ()
End

(* The response the handler writes for its buffer's first request *)
Definition hpend_def:
  hpend files (HA b) =
    (case parse_request b of
       Complete req rest => [print_response (handle files req)]
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
    (case parse_request b of
       Complete req rest => HA rest
     | Incomplete => if Readable fd ∈ s.ready then HB b else HA b
     | Invalid => HD b) ∧
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
  parse_request b = Incomplete ⇒
  http_handler files (fd, b) =
    bind (readable fd) (λu. bind (emit (Read fd)) (hafter files fd b))
Proof
  strip_tac >> simp[Once http_handler_unfold] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  Cases >> simp[hafter_def]
QED

Theorem http_handler_complete:
  parse_request b = Complete req rest ⇒
  http_handler files (fd, b) =
    bind (emit (Write fd (print_response (handle files req))))
         (λw. http_handler files (fd, rest))
Proof
  strip_tac >> simp[Once http_handler_unfold]
QED

Theorem http_handler_invalid:
  parse_request b = Invalid ⇒ http_handler files (fd, b) = return ()
Proof
  strip_tac >> simp[Once http_handler_unfold]
QED

Theorem wf_hcomp:
  wf (hcomp files fd st)
Proof
  Cases_on ‘st’ >> simp[hcomp_def, wf_http_handler, wf_return] >>
  irule wf_bind >> simp[wf_emit] >> Cases >>
  simp[hafter_def, wf_http_handler, wf_return]
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
  >- (Cases_on ‘parse_request s’ >> simp[]
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
  >- (Cases_on ‘parse_request s'’ >> simp[]
      >- (rename1 ‘Complete req rest’ >> strip_tac >>
          drule http_handler_complete >> simp[] >> disch_then kall_tac >>
          Cases_on ‘s.results’ >> gvs[] >>
          simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
          ‘suspended (emit (Write fd (print_response (handle files req)))) [s] =
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
