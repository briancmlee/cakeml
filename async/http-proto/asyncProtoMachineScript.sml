(*
  The generic handler (asyncProtoServer's proto_handler P resp) as a
  per-round state machine: asyncHttpMachineB with the protocol's parser
  and response function (design/32 phase 3).

  Between rounds, the handler of connection fd is in one of three states:

     PA b   about to act on its buffer b: if b starts with a complete
            request, write its response this round; if b is incomplete,
            wait until fd is readable; if b is invalid, stop;
     PB b   reading fd this round (fd was reported readable), buffer b;
     PD b   stopped (invalid input, or end-of-file), buffer b.

  pacts: the actions of a round; pstep: the next state, given the next
  snapshot.  pcomp turns a state into the model computation it stands for,
  and suspended_pcomp says that the model's "one poll later" is the
  machine's step.  So, on a history where the world answers promptly, the
  handler's actions round by round are the machine's (pmachine_new_actions),
  and so is its transcript (pmachine_trans).  Only pmachine_inv uses
  facts about the parser, and so assumes proto_ok P.
*)
Theory asyncProtoMachine
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncCfActModel asyncProgress asyncProto asyncProtoServer
Libs
  BasicProvers

(* Lemmas that need proto_ok P, with that hypothesis undischarged: they are
   used inside proofs whose goals have proto_ok P as an assumption *)
fun ok th = th |> SPEC_ALL |> UNDISCH_ALL_OK |> GEN_ALL
and UNDISCH_ALL_OK th =
  let val (a, _) = dest_imp (concl th)
  in if is_conj a andalso same_const (fst (strip_comb (fst (dest_conj a)))) “proto_ok”
     then UNDISCH (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th)
     else UNDISCH th
  end


(* proto_all's equation, without its length check, under proto_ok *)
Theorem proto_all_eqn:
  proto_ok P ⇒
  proto_all P s = case P.parse s of PComplete r rest => r :: proto_all P rest | _ => []
Proof
  strip_tac >> Cases_on ‘P.parse s’ >> simp[Once proto_all_def] >>
  drule_all proto_complete_shorter >> simp[]
QED

val pcomplete = ok proto_complete;
val pall_print = ok proto_all_print;

Datatype:
  pst = PA string | PB string | PD string
End

(* What the handler does with the response to its read *)
Definition pafter_def:
  pafter P resp fd b res =
    case res of
      Data d => proto_handler P resp (fd, b ++ d)
    | Eof => return ()
    | _ => proto_handler P resp (fd, b)
End

(* The model computation a state stands for *)
Definition pcomp_def:
  pcomp P resp fd (PA b) = proto_handler P resp (fd, b) ∧
  pcomp P resp fd (PB b) = bind (emit (Read fd)) (pafter P resp fd b) ∧
  pcomp P resp fd (PD b) = return ()
End

(* The response the handler writes for its buffer's first request *)
Definition ppend_def:
  ppend P resp (PA b) =
    (case P.parse b of
       PComplete req rest => [resp req]
     | _ => []) ∧
  ppend P resp (PB b) = [] ∧
  ppend P resp (PD b) = []
End

(* The actions of a round *)
Definition pacts_def:
  pacts P resp fd (PA b) = MAP (Write fd) (ppend P resp (PA b)) ∧
  pacts P resp fd (PB b) = [Read fd] ∧
  pacts P resp fd (PD b) = []
End

(* The next state, given the next snapshot *)
Definition pstep_def:
  pstep P resp fd (PA b) s =
    (case P.parse b of
       PComplete req rest => PA rest
     | PIncomplete => if Readable fd ∈ s.ready then PB b else PA b
     | PInvalid => PD b) ∧
  pstep P resp fd (PB b) s =
    (case oHD s.results of
       SOME (Data d) => PA (b ++ d)
     | SOME Eof => PD b
     | _ => PA b) ∧
  pstep P resp fd (PD b) s = PD b
End

(* The state after a history *)
Definition prun_def:
  prun P resp fd st g = FOLDL (pstep P resp fd) st g
End

Definition pbuf_def:
  pbuf (PA b) = b ∧ pbuf (PB b) = b ∧ pbuf (PD b) = b
End

Theorem prun_SNOC:
  prun P resp fd st (g ++ [s]) = pstep P resp fd (prun P resp fd st g) s
Proof
  simp[prun_def, FOLDL_APPEND]
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

(* The handler in state PA b, for an incomplete buffer: wait, then read *)
Theorem proto_handler_incomplete:
  P.parse b = PIncomplete ⇒
  proto_handler P resp (fd, b) =
    bind (readable fd) (λu. bind (emit (Read fd)) (pafter P resp fd b))
Proof
  strip_tac >> simp[Once proto_handler_unfold] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  Cases >> simp[pafter_def]
QED

Theorem proto_handler_complete:
  P.parse b = PComplete req rest ⇒
  proto_handler P resp (fd, b) =
    bind (emit (Write fd (resp req)))
         (λw. proto_handler P resp (fd, rest))
Proof
  strip_tac >> simp[Once proto_handler_unfold]
QED

Theorem proto_handler_invalid:
  P.parse b = PInvalid ⇒ proto_handler P resp (fd, b) = return ()
Proof
  strip_tac >> simp[Once proto_handler_unfold]
QED

Theorem wf_pcomp:
  wf (pcomp P resp fd st)
Proof
  Cases_on ‘st’ >> simp[pcomp_def, wf_proto_handler, wf_return] >>
  irule wf_bind >> simp[wf_emit] >> Cases >>
  simp[pafter_def, wf_proto_handler, wf_return]
QED

Theorem bind_wait_NIL[local]:
  (bind (wait p) f []).actions = []
Proof
  simp[bind_def, Once first_prefix_def, wait_def, first_some_def]
QED

(* The actions of the first round are the machine's *)
Theorem pcomp_NIL_actions:
  (pcomp P resp fd st []).actions = pacts P resp fd st
Proof
  Cases_on ‘st’ >> simp[pcomp_def, pacts_def, ppend_def, return_def]
  >- (Cases_on ‘P.parse s’ >> simp[]
      >- (drule proto_handler_complete >> simp[bind_emit_NIL])
      >- (drule proto_handler_incomplete >> simp[] >>
          simp[readable_def, bind_wait_NIL])
      >> drule proto_handler_invalid >> simp[return_def])
  >> simp[bind_emit_NIL]
QED

(* MAIN: one poll of a state's computation is the machine's step, given
   that the round's action (if any) is answered in the snapshot *)
Theorem suspended_pcomp:
  (pacts P resp fd st ≠ [] ⇒ s.results ≠ []) ⇒
  suspended (pcomp P resp fd st) [s] = pcomp P resp fd (pstep P resp fd st s)
Proof
  Cases_on ‘st’ >> simp[pcomp_def, pacts_def, ppend_def, pstep_def]
  >- (Cases_on ‘P.parse s'’ >> simp[]
      >- (rename1 ‘PComplete req rest’ >> strip_tac >>
          drule proto_handler_complete >> simp[] >> disch_then kall_tac >>
          Cases_on ‘s.results’ >> gvs[] >>
          simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
          ‘suspended (emit (Write fd (resp req))) [s] =
           finished [] h’ by metis_tac[suspended_emit_CONS] >>
          simp[bind_finished_NIL, pcomp_def])
      >- (rpt strip_tac >> drule proto_handler_incomplete >> simp[] >> disch_then kall_tac >>
          simp[suspended_bind, readable_def, wf_wait, wait_needs_snapshot] >>
          qmatch_goalsub_abbrev_tac ‘suspended (wait Q) [s]’ >> rw[]
          >- (‘suspended (wait Q : (event, asyncServer$response) snapshot list -> (asyncServer$action, unit option) asyncCore$outcome) [s] = finished [] ()’
                by (irule suspended_wait_SOME >> simp[Abbr ‘Q’]) >>
              pop_assum SUBST1_TAC >> simp[bind_finished_NIL, pcomp_def])
          >> ‘suspended (wait Q : (event, asyncServer$response) snapshot list -> (asyncServer$action, unit option) asyncCore$outcome) [s] = wait Q’
               by (irule suspended_wait_NONE >> simp[Abbr ‘Q’]) >>
          pop_assum SUBST1_TAC >> simp[pcomp_def] >> drule proto_handler_incomplete >> simp[Abbr ‘Q’, readable_def])
      >> rpt strip_tac >> drule proto_handler_invalid >> simp[pcomp_def] >>
      simp[return_finished, suspended_finished_one])
  >- (strip_tac >> Cases_on ‘s.results’ >> gvs[] >>
      simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
      ‘suspended (emit (Read fd)) [s] = finished [] h’
        by metis_tac[suspended_emit_CONS] >>
      simp[bind_finished_NIL] >>
      Cases_on ‘h’ >> simp[pafter_def, pcomp_def])
  >> simp[return_finished, suspended_finished_one]
QED

(* ------------------------------------------------------------------------
   Iterating: the state after a history, and the actions round by round
   ------------------------------------------------------------------------ *)

(* MAIN: after a history in which every round's action is answered, the
   computation is the machine's state *)
Theorem prun_suspended:
  ∀g st.
    (∀j. j < LENGTH g ∧ pacts P resp fd (prun P resp fd st (TAKE j g)) ≠ [] ⇒
         (EL j g).results ≠ []) ⇒
    suspended (pcomp P resp fd st) g = pcomp P resp fd (prun P resp fd st g)
Proof
  Induct_on ‘g’ using SNOC_INDUCT >- simp[prun_def] >>
  rpt strip_tac >> simp[SNOC_APPEND, prun_SNOC] >>
  ‘suspended (pcomp P resp fd st) (g ++ [x]) =
   suspended (suspended (pcomp P resp fd st) g) [x]’
    by simp[suspended_suspended_one, wf_pcomp] >>
  pop_assum SUBST1_TAC >>
  ‘suspended (pcomp P resp fd st) g = pcomp P resp fd (prun P resp fd st g)’
    by (first_x_assum irule >> rpt strip_tac >>
        first_x_assum (qspec_then ‘j’ mp_tac) >>
        simp[SNOC_APPEND, TAKE_APPEND1, EL_APPEND1]) >>
  pop_assum SUBST1_TAC >> irule suspended_pcomp >> strip_tac >>
  first_x_assum (qspec_then ‘LENGTH g’ mp_tac) >>
  simp[SNOC_APPEND, TAKE_LENGTH_APPEND, EL_APPEND2]
QED

(* With a prompt world, every round's action is answered *)
Theorem pmachine_answered:
  prompt (pcomp P resp fd st) g ⇒
  ∀j. j < LENGTH g ⇒
      LENGTH (pacts P resp fd (prun P resp fd st (TAKE j g))) ≤ LENGTH (EL j g).results
Proof
  strip_tac >> completeInduct_on ‘j’ >> strip_tac >>
  ‘pacts P resp fd (prun P resp fd st (TAKE j g)) =
   new_actions (log_of (pcomp P resp fd st)) (TAKE j g)’
    by (‘prun P resp fd st (TAKE j g) = prun P resp fd st (TAKE j g)’ by simp[] >>
        simp[GSYM pcomp_NIL_actions, GSYM suspended_first_poll, wf_pcomp] >>
        AP_TERM_TAC >> AP_THM_TAC >> CONV_TAC SYM_CONV >> irule prun_suspended >>
        rpt strip_tac >> ‘j' < j’ by gvs[LENGTH_TAKE] >>
        gvs[TAKE_TAKE, EL_TAKE] >>
        first_x_assum (qspec_then ‘j'’ mp_tac) >> simp[] >>
        Cases_on ‘pacts P resp fd (prun P resp fd st (TAKE j' g))’ >> gvs[]) >>
  gvs[prompt_def] >> first_x_assum drule >> simp[responses_at_def]
QED

(* MAIN: with a prompt world, the actions of each round are the machine's *)
Theorem pmachine_new_actions:
  prompt (pcomp P resp fd st) g ∧ j ≤ LENGTH g ⇒
  new_actions (log_of (pcomp P resp fd st)) (TAKE j g) =
  pacts P resp fd (prun P resp fd st (TAKE j g))
Proof
  strip_tac >>
  simp[GSYM pcomp_NIL_actions, GSYM suspended_first_poll, wf_pcomp] >>
  AP_TERM_TAC >> AP_THM_TAC >> irule prun_suspended >>
  rpt strip_tac >> gvs[LENGTH_TAKE_EQ, TAKE_TAKE_MIN, EL_TAKE] >>
  drule pmachine_answered >> disch_then (qspec_then ‘j'’ mp_tac) >>
  simp[MIN_DEF] >> gvs[MIN_DEF] >>
  Cases_on ‘(EL j' g).results’ >> simp[] >>
  Cases_on ‘pacts P resp fd (prun P resp fd st (TAKE j' g))’ >> gvs[]
QED

(* MAIN: with a prompt world, the transcript is the machine's: each round's
   actions paired with the next snapshot's responses *)
Theorem pmachine_trans:
  prompt (pcomp P resp fd st) g ⇒
  trans (pcomp P resp fd st) g =
  FLAT (GENLIST (λj. zipr (pacts P resp fd (prun P resp fd st (TAKE j g)))
                          (responses_at g j)) (SUC (LENGTH g)))
Proof
  strip_tac >> simp[trans_def] >> AP_TERM_TAC >>
  simp[GENLIST_FUN_EQ, round_trans_def] >> rpt strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> irule pmachine_new_actions >> simp[]
QED

(* ------------------------------------------------------------------------
   What the handler has read and written, in terms of its state
   ------------------------------------------------------------------------ *)

(* The transcript up to round n *)
Theorem pmachine_trans_TAKE:
  prompt (pcomp P resp fd st0) g ∧ n ≤ LENGTH g ⇒
  trans (pcomp P resp fd st0) (TAKE n g) =
  FLAT (GENLIST (λi. zipr (pacts P resp fd (prun P resp fd st0 (TAKE i g)))
                          (if i < n then (EL i g).results else [])) (SUC n))
Proof
  strip_tac >>
  ‘prompt (pcomp P resp fd st0) (TAKE n g)’ by simp[prompt_TAKE] >>
  drule pmachine_trans >> simp[LENGTH_TAKE] >> disch_then kall_tac >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ] >> rpt strip_tac >>
  simp[TAKE_TAKE, responses_at_def, EL_TAKE, LENGTH_TAKE]
QED

(* The transcript up to round j, and up to round j + 1 *)
Theorem pmachine_trans_SUC:
  prompt (pcomp P resp fd st0) g ∧ j < LENGTH g ⇒
  let TR = FLAT (GENLIST (λi. zipr (pacts P resp fd (prun P resp fd st0 (TAKE i g)))
                                    (EL i g).results) j) in
  trans (pcomp P resp fd st0) (TAKE j g) =
    TR ++ zipr (pacts P resp fd (prun P resp fd st0 (TAKE j g))) [] ∧
  trans (pcomp P resp fd st0) (TAKE (SUC j) g) =
    TR ++ zipr (pacts P resp fd (prun P resp fd st0 (TAKE j g))) (EL j g).results ++
    zipr (pacts P resp fd (prun P resp fd st0 (TAKE (SUC j) g))) []
Proof
  strip_tac >> simp[] >>
  ‘∀k. k ≤ j ⇒
       GENLIST (λi. zipr (pacts P resp fd (prun P resp fd st0 (TAKE i g)))
                        (if i < k then (EL i g).results else [])) k =
       GENLIST (λi. zipr (pacts P resp fd (prun P resp fd st0 (TAKE i g)))
                        (EL i g).results) k’
    by simp[GENLIST_FUN_EQ] >>
  ‘∀k. k ≤ SUC j ⇒
       GENLIST (λi. zipr (pacts P resp fd (prun P resp fd st0 (TAKE i g)))
                        (if i < SUC j then (EL i g).results else [])) k =
       GENLIST (λi. zipr (pacts P resp fd (prun P resp fd st0 (TAKE i g)))
                        (EL i g).results) k’
    by simp[GENLIST_FUN_EQ] >>
  simp[pmachine_trans_TAKE, GENLIST, SNOC_APPEND]
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

Theorem writes_pacts[simp]:
  writes fd (pacts P resp fd st) = ppend P resp st
Proof
  Cases_on ‘st’ >> simp[pacts_def, ppend_def, writes_def] >>
  CASE_TAC >> simp[]
QED

(* MAIN: the handler's accounting.  Started on buffer b0, after any prompt
   history, there are valid requests rs that it has completely handled:
   its buffer before, followed by what it has read, is rs printed,
   followed by its current buffer; and what it has written is the
   responses to rs, followed by the response it is writing this round (if
   its buffer starts with a complete request).  It only reads with an
   incomplete buffer, and it stops only on a buffer that does not start
   with a complete request. *)
Theorem pmachine_inv:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA b0)) g ⇒
  ∀j. j ≤ LENGTH g ⇒
    ∃rs. EVERY P.valid rs ∧
         b0 ++ CONCAT (read fd (trans (pcomp P resp fd (PA b0)) (TAKE j g))) =
           FLAT (MAP P.print rs) ++ pbuf (prun P resp fd (PA b0) (TAKE j g)) ∧
         written fd (trans (pcomp P resp fd (PA b0)) (TAKE j g)) =
           MAP (resp) rs ++
           ppend P resp (prun P resp fd (PA b0) (TAKE j g)) ∧
         (∀b. prun P resp fd (PA b0) (TAKE j g) = PB b ⇒ P.parse b = PIncomplete) ∧
         (∀b r rest. prun P resp fd (PA b0) (TAKE j g) = PD b ⇒
                     P.parse b ≠ PComplete r rest))
Proof
  DISCH_TAC >>
  strip_tac >> Induct
  >- (simp[prun_def, pbuf_def] >> qexists_tac ‘[]’ >>
      simp[trans_def, round_trans_def, responses_at_def, written_zipr] >>
      simp[new_actions_NIL, log_of_def, pcomp_NIL_actions])
  >> strip_tac >> gvs[]
  >> drule_then (qspec_then ‘j’ mp_tac) pmachine_trans_SUC >> simp[] >> strip_tac
  >> qmatch_asmsub_abbrev_tac ‘TR ++ zipr _ []’
  >> ‘TAKE (SUC j) g = TAKE j g ++ [EL j g]’ by simp[GSYM SNOC_EL_TAKE, SNOC_APPEND]
  >> qabbrev_tac ‘st = prun P resp fd (PA b0) (TAKE j g)’
  >> ‘prun P resp fd (PA b0) (TAKE (SUC j) g) = pstep P resp fd st (EL j g)’
       by simp[prun_SNOC, Abbr ‘st’]
  >> drule_then (qspec_then ‘j’ mp_tac) pmachine_answered >> simp[] >> strip_tac
  >> gvs[written_zipr]
  >> Cases_on ‘st’ >> gvs[pstep_def, pbuf_def, ppend_def, pacts_def]
  (* PA s *)
  >- (Cases_on ‘P.parse s’ >> gvs[pbuf_def, ppend_def]
      (* a complete request: its response is written; continue with rest *)
      >- (rename1 ‘PComplete req rest’ >>
          Cases_on ‘(EL j g).results’ >> gvs[zipr_def] >>
          drule pcomplete >> strip_tac >>
          qexists_tac ‘rs ++ [req]’ >> gvs[written_zipr, writes_def])
      (* incomplete: wait, or read next round *)
      >- (rw[pbuf_def, ppend_def] >> qexists_tac ‘rs’ >> simp[zipr_def] >>
          gvs[ppend_def, zipr_def])
      (* invalid: stop *)
      >> qexists_tac ‘rs’ >> gvs[pbuf_def, ppend_def, zipr_def])
  (* PB s: the read's response arrives *)
  >- (Cases_on ‘(EL j g).results’ >> gvs[zipr_def] >>
      rename1 ‘_ = r :: _’ >> Cases_on ‘r’ >> gvs[pbuf_def, ppend_def] >>
      qexists_tac ‘rs’ >> simp[] >> gvs[])
  (* PD s *)
  >> qexists_tac ‘rs’ >> gvs[pbuf_def, ppend_def, zipr_def]
QED
