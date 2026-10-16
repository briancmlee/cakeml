(*
  The query handler (asyncProtoV's proto_handler_v V P ansq fin) as a
  per-round state machine: asyncProtoMachine with one more state, for the
  write that waits on a query's answer (design/32 §2.3, for KV).

     QA b          about to act on buffer b: a complete request whose
                   ansq is NONE is answered this round; one whose ansq is
                   SOME q has its query q emitted this round; incomplete:
                   wait until readable; invalid: stop;
     QW req rest k the query of req was answered with k: write
                   fin req k this round, then continue with rest;
     QB b          reading fd this round;
     QD b          stopped.

  qacts: the actions of a round; qstep: the next state, given the next
  snapshot (for QA with a query, the snapshot carries the answer);
  qcomp: the computation a state stands for.  As in asyncProtoMachine,
  with a prompt world the handler's actions round by round, and its
  transcript, are the machine's (qmachine_new_actions, qmachine_trans).
*)
Theory asyncProtoMachineV
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncCfActModel asyncProgress asyncServerV asyncServerVLive
  asyncServerVLiveA asyncProto asyncProtoServer asyncProtoV
Libs
  BasicProvers

Datatype:
  qst = QA string | QW 'r string ('k option) | QB string | QD string
End

(* What the handler does with the response to its read *)
Definition qafter_def:
  qafter V P ansq fin fd b res =
    case V.sres res of
      SOME (Data d) => proto_handler_v V P ansq fin (fd, b ++ d)
    | SOME Eof => return ()
    | _ => proto_handler_v V P ansq fin (fd, b)
End

(* The model computation a state stands for *)
Definition qcomp_def:
  qcomp V P ansq fin fd (QA b) = proto_handler_v V P ansq fin (fd, b) ∧
  qcomp V P ansq fin fd (QW req rest k) =
    bind (emit (V.wr fd (fin req k)))
         (λw. proto_handler_v V P ansq fin (fd, rest)) ∧
  qcomp V P ansq fin fd (QB b) = bind (emit (V.rd fd)) (qafter V P ansq fin fd b) ∧
  qcomp V P ansq fin fd (QD b) = return ()
End

(* The response written this round, if any *)
Definition qpend_def:
  qpend P ansq fin (QA b) =
    (case P.parse b of
       PComplete req rest =>
         (case ansq req of NONE => [fin req NONE] | SOME q => [])
     | _ => []) ∧
  qpend P ansq fin (QW req rest k) = [fin req k] ∧
  qpend P ansq fin (QB b) = [] ∧
  qpend P ansq fin (QD b) = []
End

(* The actions of a round *)
Definition qacts_def:
  qacts V P ansq fin fd (QA b) =
    (case P.parse b of
       PComplete req rest =>
         (case ansq req of
            NONE => [V.wr fd (fin req NONE)]
          | SOME q => [V.qry q])
     | _ => []) ∧
  qacts V P ansq fin fd (QW req rest k) = [V.wr fd (fin req k)] ∧
  qacts V P ansq fin fd (QB b) = [V.rd fd] ∧
  qacts V P ansq fin fd (QD b) = []
End

(* The next state, given the next snapshot *)
Definition qstep_def:
  qstep V P ansq fin fd (QA b) s =
    (case P.parse b of
       PComplete req rest =>
         (case ansq req of
            NONE => QA rest
          | SOME q => QW req rest (OPTION_BIND (oHD s.results) V.kans))
     | PIncomplete => if Readable fd ∈ s.ready then QB b else QA b
     | PInvalid => QD b) ∧
  qstep V P ansq fin fd (QW req rest k) s = QA rest ∧
  qstep V P ansq fin fd (QB b) s =
    (case OPTION_BIND (oHD s.results) V.sres of
       SOME (Data d) => QA (b ++ d)
     | SOME Eof => QD b
     | _ => QA b) ∧
  qstep V P ansq fin fd (QD b) s = QD b
End

(* The state after a history *)
Definition qrun_def:
  qrun V P ansq fin fd st g = FOLDL (qstep V P ansq fin fd) st g
End

(* The bytes a state holds: the buffer (for QW, its request, printed, and
   the rest) *)
Definition qbuf_def:
  qbuf P (QA b) = b ∧ qbuf P (QW req rest k) = P.print req ++ rest ∧
  qbuf P (QB b) = b ∧ qbuf P (QD b) = b
End

Theorem qrun_SNOC:
  qrun V P ansq fin fd st (g ++ [s]) =
  qstep V P ansq fin fd (qrun V P ansq fin fd st g) s
Proof
  simp[qrun_def, FOLDL_APPEND]
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

Theorem suspended_readable_yes[local]:
  Readable fd ∈ s.ready ⇒ suspended (readable fd) [s] = finished [] ()
Proof
  simp[readable_def] >> strip_tac >> irule suspended_wait_SOME >> simp[]
QED

Theorem suspended_readable_no[local]:
  Readable fd ∉ s.ready ⇒ suspended (readable fd) [s] = readable fd
Proof
  simp[readable_def] >> strip_tac >> irule suspended_wait_NONE >> simp[]
QED

Theorem bind_wait_NIL[local]:
  (bind (wait p) f []).actions = []
Proof
  simp[bind_def, Once first_prefix_def, wait_def, first_some_def]
QED

Theorem wf_qcomp:
  wf (qcomp V P ansq fin fd st)
Proof
  Cases_on ‘st’ >> simp[qcomp_def, wf_proto_handler_v, wf_return] >>
  irule wf_bind >> simp[wf_emit, wf_proto_handler_v] >>
  rw[qafter_def] >> rpt CASE_TAC >> simp[wf_proto_handler_v, wf_return]
QED

(* The actions of the first round are the machine's *)
Theorem qcomp_NIL_actions:
  (qcomp V P ansq fin fd st []).actions = qacts V P ansq fin fd st
Proof
  Cases_on ‘st’ >> simp[qcomp_def, qacts_def, return_def, bind_emit_NIL] >>
  simp[Once proto_handler_v_unfold] >>
  rpt CASE_TAC >> simp[bind_emit_NIL, return_def, readable_def, bind_wait_NIL]
QED

(* MAIN: one poll of a state's computation is the machine's step, given
   that the round's action (if any) is answered in the snapshot *)
Theorem suspended_qcomp:
  (qacts V P ansq fin fd st ≠ [] ⇒ s.results ≠ []) ⇒
  suspended (qcomp V P ansq fin fd st) [s] =
  qcomp V P ansq fin fd (qstep V P ansq fin fd st s)
Proof
  Cases_on ‘st’ >> simp[qcomp_def, qacts_def, qstep_def]
  (* QA b *)
  >- (simp[Once proto_handler_v_unfold] >>
      Cases_on ‘P.parse s'’ >> simp[]
      (* a complete request: answer, or query *)
      >- (rename1 ‘PComplete req rest’ >> Cases_on ‘ansq req’ >> simp[] >>
          strip_tac >> Cases_on ‘s.results’ >> gvs[] >>
          simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
          qmatch_goalsub_abbrev_tac ‘suspended (emit EA) [s]’ >>
          ‘suspended (emit EA) [s] = finished [] h’
            by (irule suspended_emit_CONS >> simp[]) >>
          simp[bind_finished_NIL, qcomp_def])
      (* incomplete: wait, or read next round *)
      >- (qmatch_goalsub_abbrev_tac ‘suspended (bind RDY KR) [s]’ >>
          ‘wf RDY ∧ (RDY []).result = NONE’
            by simp[Abbr ‘RDY’, readable_def, wf_wait, wait_needs_snapshot] >>
          simp[suspended_bind] >> qunabbrev_tac ‘RDY’ >>
          Cases_on ‘Readable fd ∈ s.ready’ >>
          simp[suspended_readable_yes, suspended_readable_no, bind_finished_NIL,
               qcomp_def]
          >- (simp[Abbr ‘KR’] >> AP_TERM_TAC >> simp[FUN_EQ_THM, qafter_def])
          >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [proto_handler_v_unfold])) >>
          simp[Abbr ‘KR’])
      (* invalid: stop *)
      >> simp[qcomp_def, return_finished, suspended_finished_one])
  (* QW: the write, then the handler on the rest *)
  >- (strip_tac >> Cases_on ‘s.results’ >> gvs[] >>
      simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
      qmatch_goalsub_abbrev_tac ‘suspended (emit EA) [s]’ >>
          ‘suspended (emit EA) [s] = finished [] h’
            by (irule suspended_emit_CONS >> simp[]) >>
      simp[bind_finished_NIL])
  (* QB: the read's response arrives *)
  >- (strip_tac >> Cases_on ‘s.results’ >> gvs[] >>
      simp[suspended_bind, wf_emit, emit_needs_snapshot] >>
      qmatch_goalsub_abbrev_tac ‘suspended (emit EA) [s]’ >>
          ‘suspended (emit EA) [s] = finished [] h’
            by (irule suspended_emit_CONS >> simp[]) >>
      simp[bind_finished_NIL, qafter_def] >>
      rpt CASE_TAC >> simp[qcomp_def])
  >> simp[return_finished, suspended_finished_one]
QED

(* ------------------------------------------------------------------------
   Iterating: the state after a history, and the actions round by round
   ------------------------------------------------------------------------ *)

(* MAIN: after a history in which every round's action is answered, the
   computation is the machine's state *)
Theorem qrun_suspended:
  ∀g st.
    (∀j. j < LENGTH g ∧ qacts V P ansq fin fd (qrun V P ansq fin fd st (TAKE j g)) ≠ [] ⇒
         (EL j g).results ≠ []) ⇒
    suspended (qcomp V P ansq fin fd st) g = qcomp V P ansq fin fd (qrun V P ansq fin fd st g)
Proof
  Induct_on ‘g’ using SNOC_INDUCT >- simp[qrun_def] >>
  rpt strip_tac >> simp[SNOC_APPEND, qrun_SNOC] >>
  ‘suspended (qcomp V P ansq fin fd st) (g ++ [x]) =
   suspended (suspended (qcomp V P ansq fin fd st) g) [x]’
    by simp[suspended_suspended_one, wf_qcomp] >>
  pop_assum SUBST1_TAC >>
  ‘suspended (qcomp V P ansq fin fd st) g = qcomp V P ansq fin fd (qrun V P ansq fin fd st g)’
    by (first_x_assum irule >> rpt strip_tac >>
        first_x_assum (qspec_then ‘j’ mp_tac) >>
        simp[SNOC_APPEND, TAKE_APPEND1, EL_APPEND1]) >>
  pop_assum SUBST1_TAC >> irule suspended_qcomp >> strip_tac >>
  first_x_assum (qspec_then ‘LENGTH g’ mp_tac) >>
  simp[SNOC_APPEND, TAKE_LENGTH_APPEND, EL_APPEND2]
QED

(* With a prompt world, every round's action is answered *)
Theorem qmachine_answered:
  prompt (qcomp V P ansq fin fd st) g ⇒
  ∀j. j < LENGTH g ⇒
      LENGTH (qacts V P ansq fin fd (qrun V P ansq fin fd st (TAKE j g))) ≤ LENGTH (EL j g).results
Proof
  strip_tac >> completeInduct_on ‘j’ >> strip_tac >>
  ‘qacts V P ansq fin fd (qrun V P ansq fin fd st (TAKE j g)) =
   new_actions (log_of (qcomp V P ansq fin fd st)) (TAKE j g)’
    by (‘qrun V P ansq fin fd st (TAKE j g) = qrun V P ansq fin fd st (TAKE j g)’ by simp[] >>
        simp[GSYM qcomp_NIL_actions, GSYM suspended_first_poll, wf_qcomp] >>
        AP_TERM_TAC >> AP_THM_TAC >> CONV_TAC SYM_CONV >> irule qrun_suspended >>
        rpt strip_tac >> ‘j' < j’ by gvs[LENGTH_TAKE] >>
        gvs[TAKE_TAKE, EL_TAKE] >>
        first_x_assum (qspec_then ‘j'’ mp_tac) >> simp[] >>
        Cases_on ‘qacts V P ansq fin fd (qrun V P ansq fin fd st (TAKE j' g))’ >> gvs[]) >>
  gvs[prompt_def] >> first_x_assum drule >> simp[responses_at_def]
QED

(* MAIN: with a prompt world, the actions of each round are the machine's *)
Theorem qmachine_new_actions:
  prompt (qcomp V P ansq fin fd st) g ∧ j ≤ LENGTH g ⇒
  new_actions (log_of (qcomp V P ansq fin fd st)) (TAKE j g) =
  qacts V P ansq fin fd (qrun V P ansq fin fd st (TAKE j g))
Proof
  strip_tac >>
  simp[GSYM qcomp_NIL_actions, GSYM suspended_first_poll, wf_qcomp] >>
  AP_TERM_TAC >> AP_THM_TAC >> irule qrun_suspended >>
  rpt strip_tac >> gvs[LENGTH_TAKE_EQ, TAKE_TAKE_MIN, EL_TAKE] >>
  drule qmachine_answered >> disch_then (qspec_then ‘j'’ mp_tac) >>
  simp[MIN_DEF] >> gvs[MIN_DEF] >>
  Cases_on ‘(EL j' g).results’ >> simp[] >>
  Cases_on ‘qacts V P ansq fin fd (qrun V P ansq fin fd st (TAKE j' g))’ >> gvs[]
QED

(* MAIN: with a prompt world, the transcript is the machine's: each round's
   actions paired with the next snapshot's responses *)
Theorem qmachine_trans:
  prompt (qcomp V P ansq fin fd st) g ⇒
  trans (qcomp V P ansq fin fd st) g =
  FLAT (GENLIST (λj. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st (TAKE j g)))
                          (responses_at g j)) (SUC (LENGTH g)))
Proof
  strip_tac >> simp[trans_def] >> AP_TERM_TAC >>
  simp[GENLIST_FUN_EQ, round_trans_def] >> rpt strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> irule qmachine_new_actions >> simp[]
QED

(* ------------------------------------------------------------------------
   What the handler has read and written, in terms of its state
   ------------------------------------------------------------------------ *)

(* The transcript up to round n *)
Theorem qmachine_trans_TAKE:
  prompt (qcomp V P ansq fin fd st0) g ∧ n ≤ LENGTH g ⇒
  trans (qcomp V P ansq fin fd st0) (TAKE n g) =
  FLAT (GENLIST (λi. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE i g)))
                          (if i < n then (EL i g).results else [])) (SUC n))
Proof
  strip_tac >>
  ‘prompt (qcomp V P ansq fin fd st0) (TAKE n g)’ by simp[prompt_TAKE] >>
  drule qmachine_trans >> simp[LENGTH_TAKE] >> disch_then kall_tac >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ] >> rpt strip_tac >>
  simp[TAKE_TAKE, responses_at_def, EL_TAKE, LENGTH_TAKE]
QED

(* The transcript up to round j, and up to round j + 1 *)
Theorem qmachine_trans_SUC:
  prompt (qcomp V P ansq fin fd st0) g ∧ j < LENGTH g ⇒
  let TR = FLAT (GENLIST (λi. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE i g)))
                                    (EL i g).results) j) in
  trans (qcomp V P ansq fin fd st0) (TAKE j g) =
    TR ++ zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE j g))) [] ∧
  trans (qcomp V P ansq fin fd st0) (TAKE (SUC j) g) =
    TR ++ zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE j g))) (EL j g).results ++
    zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE (SUC j) g))) []
Proof
  strip_tac >> simp[] >>
  ‘∀k. k ≤ j ⇒
       GENLIST (λi. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE i g)))
                        (if i < k then (EL i g).results else [])) k =
       GENLIST (λi. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE i g)))
                        (EL i g).results) k’
    by simp[GENLIST_FUN_EQ] >>
  ‘∀k. k ≤ SUC j ⇒
       GENLIST (λi. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE i g)))
                        (if i < SUC j then (EL i g).results else [])) k =
       GENLIST (λi. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd st0 (TAKE i g)))
                        (EL i g).results) k’
    by simp[GENLIST_FUN_EQ] >>
  simp[qmachine_trans_TAKE, GENLIST, SNOC_APPEND]
QED


(* ------------------------------------------------------------------------
   What the handler has read, written and been answered, in terms of its
   state
   ------------------------------------------------------------------------ *)

(* The responses to requests rs, given the answers ks to their queries in
   order (a request without a query is answered with NONE) *)
Definition resps_def:
  resps ansq fin [] ks = [] ∧
  resps ansq fin (r :: rs) ks =
    case ansq r of
      NONE => fin r NONE :: resps ansq fin rs ks
    | SOME q =>
        (case ks of [] => [] | k :: ks' => fin r k :: resps ansq fin rs ks')
End

(* The number of requests among rs that make a query *)
Definition nq_def:
  nq ansq rs = LENGTH (FILTER (λr. IS_SOME (ansq r)) rs)
End

(* The answer a QW state holds *)
Definition qlast_def:
  qlast (QW req rest k) = [k] ∧ qlast (QA b) = [] ∧ qlast (QB b) = [] ∧
  qlast (QD b) = []
End

Theorem resps_append:
  ∀rs ks rs2 ks2.
    LENGTH ks = nq ansq rs ⇒
    resps ansq fin (rs ++ rs2) (ks ++ ks2) =
    resps ansq fin rs ks ++ resps ansq fin rs2 ks2
Proof
  Induct >> simp[resps_def, nq_def] >> rpt gen_tac >>
  Cases_on ‘ansq h’ >> simp[] >- metis_tac[nq_def] >>
  Cases_on ‘ks’ >> simp[] >> metis_tac[nq_def]
QED

Theorem sproj_APPEND[local]:
  ∀a b. sproj V (a ++ b) = sproj V a ++ sproj V b
Proof
  Induct >> simp[] >> Cases >> simp[]
QED

Theorem kanswers_NIL[simp,local]:
  kanswers V [] = []
Proof
  simp[kanswers_def]
QED

Theorem kanswers_APPEND[local]:
  kanswers V (a ++ b) = kanswers V a ++ kanswers V b
Proof
  simp[kanswers_def]
QED

Theorem written_APPEND[local]:
  written fd (a ++ b) = written fd a ++ written fd b
Proof
  simp[written_def]
QED

Theorem read_APPEND[local]:
  read fd (a ++ b) = read fd a ++ read fd b
Proof
  simp[read_def]
QED

(* A round's actions, through the socket projection *)
Theorem qacts_written:
  vocab_ok V ∧ vocab_qok V ⇒
  written fd (sproj V (zipr (qacts V P ansq fin fd st) rs)) = qpend P ansq fin st
Proof
  rw[vocab_ok_def, vocab_qok_def] >>
  Cases_on ‘st’ >> simp[qacts_def, qpend_def, zipr_def, written_def] >>
  rpt CASE_TAC >> simp[zipr_def, written_def]
QED

Theorem qacts_read_NIL:
  vocab_ok V ∧ vocab_qok V ⇒
  read fd (sproj V (zipr (qacts V P ansq fin fd st) [])) = []
Proof
  rw[vocab_ok_def, vocab_qok_def] >>
  Cases_on ‘st’ >> simp[qacts_def, zipr_def, read_def] >>
  rpt CASE_TAC >> simp[zipr_def, read_def]
QED

Theorem qacts_kanswers_NIL:
  kanswers V (zipr (qacts V P ansq fin fd st) []) = []
Proof
  Cases_on ‘st’ >> simp[qacts_def, zipr_def, kanswers_def] >>
  rpt CASE_TAC >> simp[zipr_def, kanswers_def]
QED


(* The vocabulary's socket actions and queries *)
Theorem vocab_sact[local]:
  (vocab_ok V ⇒ V.sact (V.wr fd d) = SOME (Write fd d) ∧
                V.sact (V.rd fd) = SOME (Read fd)) ∧
  (vocab_qok V ⇒ V.sact (V.qry q) = NONE)
Proof
  rw[vocab_ok_def, vocab_qok_def]
QED

(* Single transcript entries, through the vocabulary *)
Theorem vocab_entries[local]:
  vocab_ok V ∧ vocab_qok V ⇒
  sproj V [(V.wr fd x, r)] = [(Write fd x, OPTION_BIND r V.sres)] ∧
  sproj V [(V.rd fd, r)] = [(Read fd, OPTION_BIND r V.sres)] ∧
  sproj V [(V.qry q, r)] = [] ∧
  kanswers V [(V.wr fd x, r)] = [] ∧
  kanswers V [(V.rd fd, r)] = [] ∧
  kanswers V [(V.qry q, SOME y)] = [V.kans y]
Proof
  strip_tac >> fs[vocab_ok_def, vocab_qok_def] >>
  Cases_on ‘r’ >> simp[kanswers_def]
QED

(* MAIN: the handler's accounting.  Started on buffer b0, after any prompt
   history, there are valid requests rs it has completely handled and
   the answers ks to their queries: its buffer before, followed by what it
   has read, is rs printed, followed by the bytes its state holds; the
   answers it has received are ks (and, in QW, the one it is about to
   use); and what it has written is the responses to rs given ks,
   followed by the response it is writing this round.  It only reads with
   an incomplete buffer, stops only on a buffer that does not start with a
   complete request, and waits (QW) only on a valid request's query. *)
Theorem qmachine_inv:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ⇒
  (prompt (qcomp V P ansq fin fd (QA b0)) g ⇒
  ∀j. j ≤ LENGTH g ⇒
    ∃rs ks.
      EVERY P.valid rs ∧
      b0 ++ CONCAT (read fd (sproj V (trans (qcomp V P ansq fin fd (QA b0)) (TAKE j g)))) =
        FLAT (MAP P.print rs) ++ qbuf P (qrun V P ansq fin fd (QA b0) (TAKE j g)) ∧
      kanswers V (trans (qcomp V P ansq fin fd (QA b0)) (TAKE j g)) =
        ks ++ qlast (qrun V P ansq fin fd (QA b0) (TAKE j g)) ∧
      LENGTH ks = nq ansq rs ∧
      written fd (sproj V (trans (qcomp V P ansq fin fd (QA b0)) (TAKE j g))) =
        resps ansq fin rs ks ++ qpend P ansq fin (qrun V P ansq fin fd (QA b0) (TAKE j g)) ∧
      (∀b. qrun V P ansq fin fd (QA b0) (TAKE j g) = QB b ⇒ P.parse b = PIncomplete) ∧
      (∀b r rest. qrun V P ansq fin fd (QA b0) (TAKE j g) = QD b ⇒
                  P.parse b ≠ PComplete r rest) ∧
      (∀req rest k. qrun V P ansq fin fd (QA b0) (TAKE j g) = QW req rest k ⇒
                    P.valid req ∧ IS_SOME (ansq req)))
Proof
  strip_tac >> strip_tac >> Induct
  >- (strip_tac >> qexistsl [‘[]’, ‘[]’] >>
      simp[qrun_def, qbuf_def, qlast_def, resps_def, nq_def] >>
      simp[trans_def, round_trans_def, responses_at_def, new_actions_NIL,
           log_of_def, qcomp_NIL_actions, qacts_written, qacts_read_NIL,
           qacts_kanswers_NIL, qpend_def])
  >> strip_tac >> gvs[]
  >> drule_then (qspec_then ‘j’ mp_tac) qmachine_trans_SUC >> simp[] >> strip_tac
  >> qmatch_asmsub_abbrev_tac ‘TR ++ zipr _ []’
  >> qabbrev_tac ‘TR0 = FLAT (GENLIST (λi. zipr (qacts V P ansq fin fd
                          (qrun V P ansq fin fd (QA b0) (TAKE i g))) (EL i g).results) j)’
  >> ‘TAKE (SUC j) g = TAKE j g ++ [EL j g]’ by simp[GSYM SNOC_EL_TAKE, SNOC_APPEND]
  >> qabbrev_tac ‘st = qrun V P ansq fin fd (QA b0) (TAKE j g)’
  >> ‘qrun V P ansq fin fd (QA b0) (TAKE (SUC j) g) = qstep V P ansq fin fd st (EL j g)’
       by simp[qrun_SNOC, Abbr ‘st’]
  >> drule_then (qspec_then ‘j’ mp_tac) qmachine_answered >> simp[] >> strip_tac
  >> gvs[sproj_APPEND, read_APPEND, written_APPEND, kanswers_APPEND,
         qacts_written, qacts_read_NIL, qacts_kanswers_NIL]
  >> Cases_on ‘st’ >> gvs[qstep_def, qbuf_def, qpend_def, qacts_def, qlast_def]
  (* QA s *)
  >- (Cases_on ‘P.parse s’ >> gvs[qbuf_def, qpend_def, qlast_def]
      (* a complete request *)
      >- (rename1 ‘PComplete req rest’ >>
          drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO] proto_complete |> UNDISCH) >>
          strip_tac >>
          Cases_on ‘ansq req’ >> gvs[qbuf_def, qpend_def, qlast_def] >>
          Cases_on ‘(EL j g).results’ >> gvs[zipr_def]
          (* no query: answered this round *)
          >- (qexists_tac ‘rs ++ [req]’ >>
              gvs[Abbr ‘TR’, kanswers_APPEND, sproj_APPEND, read_APPEND, written_APPEND,
                  vocab_entries, vocab_sact, read_def, nq_def, FILTER_APPEND] >>
              ‘resps ansq fin (rs ++ [req]) (kanswers V TR0 ++ []) =
               resps ansq fin rs (kanswers V TR0) ++ resps ansq fin [req] []’
                by (irule resps_append >> simp[nq_def]) >>
              gvs[resps_def])
          (* a query: its answer arrives *)
          >> qexistsl [‘rs’, ‘kanswers V TR0’] >>
          gvs[Abbr ‘TR’, kanswers_APPEND, sproj_APPEND, read_APPEND, written_APPEND,
              vocab_entries, vocab_sact, read_def, qbuf_def, nq_def])
      (* incomplete: wait, or read next round *)
      >- (rw[] >> qexistsl [‘rs’, ‘kanswers V TR0’] >>
          gvs[Abbr ‘TR’, zipr_def, qbuf_def, qpend_def, qlast_def, sproj_APPEND,
              read_APPEND, written_APPEND, kanswers_APPEND])
      (* invalid: stop *)
      >> qexists_tac ‘rs’ >>
      gvs[Abbr ‘TR’, qbuf_def, qpend_def, zipr_def, qlast_def, sproj_APPEND,
          read_APPEND, written_APPEND, kanswers_APPEND])
  (* QW: the response to req, with its answer *)
  >- (rename1 ‘QW req rest ko’ >>
      Cases_on ‘(EL j g).results’ >> gvs[zipr_def] >>
      qexists_tac ‘rs ++ [req]’ >>
      gvs[Abbr ‘TR’, kanswers_APPEND, sproj_APPEND, read_APPEND, written_APPEND,
          vocab_entries, vocab_sact, read_def, nq_def, FILTER_APPEND, qbuf_def] >>
      ‘resps ansq fin (rs ++ [req]) (ks ++ [ko]) =
       resps ansq fin rs ks ++ resps ansq fin [req] [ko]’
        by (irule resps_append >> simp[nq_def]) >>
      Cases_on ‘ansq req’ >> gvs[resps_def])
  (* QB s: the read's response arrives *)
  >- (Cases_on ‘(EL j g).results’ >> gvs[zipr_def] >>
      rename1 ‘_ = r :: _’ >>
      gvs[Abbr ‘TR’, kanswers_APPEND, sproj_APPEND, read_APPEND, written_APPEND,
          vocab_entries, vocab_sact, read_def] >>
      Cases_on ‘V.sres r’ >> gvs[qbuf_def, qpend_def, qlast_def] >>
      TRY (rename1 ‘V.sres r = SOME x’ >> Cases_on ‘x’) >>
      gvs[qbuf_def, qpend_def, qlast_def] >> qexists_tac ‘rs’ >> simp[])
  (* QD s *)
  >> qexists_tac ‘rs’ >>
  gvs[Abbr ‘TR’, qbuf_def, qpend_def, zipr_def, qlast_def, sproj_APPEND,
      read_APPEND, written_APPEND, kanswers_APPEND]
QED
