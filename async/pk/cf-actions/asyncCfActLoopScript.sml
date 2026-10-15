(*
  The never-ending event loop with actions, proved with CakeML's divergence
  CF (characteristic/cfDivScript.sml):

      fun step c = case c of (acts, s) =>
                     poll c (get_ready (), 0, perform acts)    (in order)
      fun run c = run (step c)

  Each iteration performs the current round's actions through the FFI
  (one `act` call each, in order), reads the ready byte, and polls the
  computation with the resulting snapshot.  The FFI is the self-contained
  model of asyncCfActWorldScript.sml.

  Result (run_spec): the loop diverges, and its I/O trace is the
  concatenation of round_events m ws i over all rounds i: the model's
  new actions of round i, each with the response the world gave, then the
  ready byte.  With trace_actions_rounds, the actions in the trace are
  exactly the model's action log over the world's snapshot sequence.
*)
Theory asyncCfActLoop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  asyncCfActSpec asyncCfActWorld cfDiv ml_translator mlbasicsProg
  Word8Prog Word8ArrayProof llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfActProg"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun do_act a =
    let
      val buf = Word8Array.array 1 a
      val _ = #(act) "" buf
    in Word8Array.sub buf 0 end;

  fun perform acts =
    case acts of
      [] => []
    | a :: rest => let val r = do_act a in r :: perform rest end;

  fun get_ready u =
    let
      val buf = Word8Array.array 1 (Word8.fromInt 0)
      val _ = #(ready) "" buf
    in Word8Array.sub buf 0 end;

  fun step c =
    case c of (acts, s) =>
      let
        val rs = perform acts
        val b = get_ready ()
      in poll c (b, 0, rs) end;
End

Quote add_cakeml:
  fun run c = run (step c);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Specs
   ------------------------------------------------------------------------ *)

(* The loop's snapshots carry one ready byte b, i.e. the ready set {b} *)
Definition READY1_def:
  READY1 rdy v ⇔ ∃b:word8. rdy = {b} ∧ WORD b v
End

Theorem sdrop_1[local]:
  sdrop 1 ws = ws o SUC
Proof
  simp[sdrop_def, FUN_EQ_THM, ADD1]
QED

(* do_act a performs a: it returns the response, the next byte of the
   stream, and records one act event. *)
Theorem do_act_spec:
  limited_parts io_names p ∧ WORD a av ⇒
  app (p:'ffi ffi_proj) do_act_v [av] (IOS ws evs)
    (POSTv v. &WORD (ws 0) v * IOS (sdrop 1 ws) (evs ++ [act_event a (ws 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "do_act_v_def") >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  ‘REPLICATE 1 a = [a]’ by EVAL_TAC >>
  xlet ‘POSTv u. W8ARRAY bv [ws 0] * IOS (sdrop 1 ws) (evs ++ [act_event a (ws 0)])’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘io_state ws’, ‘io_update’, ‘io_names’, ‘evs’] >>
      simp[io_names_def, IOS_def, io_update_next, act_event_def] >>
      xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

(* perform acts performs the actions in order: it returns their responses
   (the next LENGTH acts bytes) and records one act event per action. *)
Theorem perform_spec:
  ∀acts av ws evs.
    limited_parts io_names p ∧ LIST_TYPE WORD acts av ⇒
    app (p:'ffi ffi_proj) perform_v [av] (IOS ws evs)
      (POSTv v. &LIST_TYPE WORD (GENLIST ws (LENGTH acts)) v *
                IOS (sdrop (LENGTH acts) ws)
                   (evs ++ MAP2 act_event acts (GENLIST ws (LENGTH acts))))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "perform_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >- (xlet ‘POSTv r. &WORD (ws 0) r * IOS (sdrop 1 ws) (evs ++ [act_event h (ws 0)])’
      >- (xapp >> simp[]) >>
      xlet ‘POSTv rv. &LIST_TYPE WORD (GENLIST (sdrop 1 ws) (LENGTH acts)) rv *
              IOS (sdrop (LENGTH acts) (sdrop 1 ws))
                 (evs ++ [act_event h (ws 0)] ++
                  MAP2 act_event acts (GENLIST (sdrop 1 ws) (LENGTH acts)))’
      >- (xapp >> simp[]) >>
      xcon >> simp[sdrop_sdrop, GENLIST_CONS, GSYM sdrop_1, ADD1] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
      xsimpl >> simp[LIST_TYPE_def])
QED

(* get_ready returns the next byte of the stream and records one event. *)
Theorem get_ready_spec:
  limited_parts io_names p ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) get_ready_v [uv] (IOS ws evs)
    (POSTv v. &WORD (ws 0) v * IOS (sdrop 1 ws) (evs ++ [ready_event (ws 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "get_ready_v_def") >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  xlet ‘POSTv u. W8ARRAY bv [ws 0] * IOS (sdrop 1 ws) (evs ++ [ready_event (ws 0)])’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘io_state ws’, ‘io_update’, ‘io_names’, ‘evs’] >>
      simp[io_names_def, IOS_def, EVAL “REPLICATE 1 (0w:word8)”] >>
      simp[io_update_next, io_names_def, ready_event_def] >>
      xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

(* MAIN: one loop iteration.  If cv implements m, the iteration performs
   m's first-round actions against the stream ws (one event each, with the
   world's responses), reads the ready byte, and returns a value
   implementing m with the resulting snapshot delivered. *)
Theorem step_spec:
  limited_parts io_names p ∧
  COMP p WORD A (SNAPSHOT READY1 WORD) m cv ⇒
  app (p:'ffi ffi_proj) step_v [cv] (IOS ws [])
    (POSTv v. &COMP p WORD A (SNAPSHOT READY1 WORD)
                 (suspended m [world_snap ws (LENGTH (m []).actions)]) v *
              IOS (sdrop (LENGTH (m []).actions + 1) ws)
                 (round_events_of (m []).actions ws))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_v_def") >> xmatch >>
  qabbrev_tac ‘k = LENGTH (m []).actions’ >>
  xlet ‘POSTv rsv. &LIST_TYPE WORD (GENLIST ws k) rsv *
          IOS (sdrop k ws) (MAP2 act_event (m []).actions (GENLIST ws k))’
  >- (xapp >> qexistsl [‘emp’, ‘ws’, ‘[]’, ‘(m []).actions’] >>
      simp[Abbr ‘k’] >> xsimpl) >>
  xlet ‘POSTv u. &UNIT_TYPE () u * IOS (sdrop k ws)
          (MAP2 act_event (m []).actions (GENLIST ws k))’
  >- (xcon >> xsimpl) >>
  xlet ‘POSTv bv. &WORD (ws k) bv * IOS (sdrop 1 (sdrop k ws))
          (MAP2 act_event (m []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
  >- (xapp >>
      qexistsl [‘emp’, ‘sdrop k ws’,
                ‘MAP2 act_event (m []).actions (GENLIST ws k)’] >>
      ‘sdrop k ws 0 = ws k’ by simp[sdrop_def] >>
      simp[] >> xsimpl) >>
  xlet ‘POSTv wv. &SNAPSHOT READY1 WORD (world_snap ws k) wv *
          IOS (sdrop 1 (sdrop k ws))
             (MAP2 act_event (m []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, world_snap_def, READY1_def]) >>
  ‘app p poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p WORD A (SNAPSHOT READY1 WORD)
                 (suspended m [world_snap ws k]) v)’
    by (irule poll_spec >> simp[]) >>
  qpat_x_assum ‘app _ poll_v _ _ _’ xapp_spec >> xsimpl >>
  simp[sdrop_sdrop, round_events_of_def, Abbr ‘k’] >> xsimpl
QED

(* MAIN: the event loop never terminates, and its I/O trace is the
   concatenation, over all rounds i, of round_events m ws i: the model's new
   actions of round i (new_actions (log_of m) (hist m ws i)), each with the
   world's response, then the ready byte.  The history hist m ws i is built
   from exactly these responses and ready bytes (rounds_def), so by
   trace_actions_rounds the actions in the trace are the model's action log
   over the snapshot sequence the world provides.  (Invariant: after i
   iterations the loop holds a value implementing suspended m (hist m ws i).) *)
Theorem run_spec:
  limited_parts io_names p ∧ wf m ∧
  COMP p WORD A (SNAPSHOT READY1 WORD) m cv ⇒
  app (p:'ffi ffi_proj) run_v [cv] (IOS ws [])
    (POSTd io. io = LFLATTEN (LGENLIST (λi. fromList (round_events m ws i)) NONE))
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then [] else round_events m ws (i - 1)’ >>
  qexists_tac ‘λi cv. COMP p WORD A (SNAPSHOT READY1 WORD)
                        (suspended m (FST (rounds m ws i))) cv’ >>
  qexists_tac ‘λi. io_state (sdrop (SND (rounds m ws i)) ws)’ >>
  qexists_tac ‘io_update’ >>
  simp[CONJUNCT1 rounds_def] >> rpt conj_tac
  >- (simp[IOS_def] >> xsimpl)
  >- ((* one iteration: step_spec, with the model and the stream advanced *)
      rpt strip_tac >> simp[GSYM IOS_def] >>
      qabbrev_tac ‘h = FST (rounds m ws i)’ >>
      qabbrev_tac ‘pos = SND (rounds m ws i)’ >>
      ‘app p step_v [xv] (IOS (sdrop pos ws) [])
         (POSTv v.
            &COMP p WORD A (SNAPSHOT READY1 WORD)
               (suspended (suspended m h)
                  [world_snap (sdrop pos ws)
                     (LENGTH (suspended m h []).actions)]) v *
            IOS (sdrop (LENGTH (suspended m h []).actions + 1) (sdrop pos ws))
               (round_events_of (suspended m h []).actions (sdrop pos ws)))’
        by (irule step_spec >> simp[]) >>
      gvs[suspended_first_poll, suspended_suspended_one, sdrop_sdrop] >>
      xlet ‘POSTv v.
              &COMP p WORD A (SNAPSHOT READY1 WORD)
                 (suspended m (FST (rounds m ws (SUC i)))) v *
              IOS (sdrop (SND (rounds m ws (SUC i))) ws) (round_events m ws i)’
      >- (qpat_x_assum ‘app _ step_v _ _ _’ xapp_spec >> xsimpl >>
          simp[rounds_SUC, round_events_alt, Abbr ‘h’, Abbr ‘pos’] >>
          rpt strip_tac >> xsimpl) >>
      xvar >> xsimpl)
  >- ((* the trace: no events before the first iteration, then one round each *)
      simp[LFLATTEN_LGENLIST_shift])
QED
