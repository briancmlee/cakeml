(*
  The blocking event loop (Level 2), proved with CakeML's divergence CF.

      fun bstep c = case c of (acts, s) =>
        let val rs = bperform acts
            val b  = case s of Done2 x => bget_ready ()
                     | Pending2 es k => (case acts of [] => bselect es
                                                   | _ => bget_ready ())
        in poll2 c (b, 0, rs) end
      fun brun c = brun (bstep c)

  When the computation has no action to perform and is waiting, the loop
  does not poll: it blocks in `select` on the events the computation
  declares (its Level 2 interest), and the world lets the other rounds
  pass.  The FFI is loopBlock2Ffi (cf-actions' byte stream plus select).

  MAIN (brun_spec): the loop diverges, and its I/O trace is the
  concatenation of bround_events c ws i over all rounds i.  With
  trace_actions_brounds and blocking_same_actions, the actions in the
  trace are the model computation's action log, which is the same as
  under the polling loop of cf-actions (no busy waiting).
*)
Theory loopBlock2
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncSched2 libModel
  libProg libWorld loopBlock2Model loopBlock2Prog
  loopBlock2Spec loopBlock2World loopBlock2Ffi cfDiv ml_translator
  mlbasicsProg Word8Prog Word8ArrayProof llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "loopBlock2Prog"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

(* The declared events, as the config string of select *)
Definition byte_chr_def:
  byte_chr (w:word8) = CHR (w2n w)
End

val r = translate byte_chr_def;

Theorem byte_chr_side[local]:
  byte_chr_side w
Proof
  simp[fetch "-" "byte_chr_side_def", w2n_lt_256]
QED

val _ = update_precondition byte_chr_side;

Definition bytes_str_def:
  bytes_str l = implode (MAP byte_chr l)
End

val r = translate bytes_str_def;

Quote add_cakeml:
  fun bdo_act a =
    let
      val buf = Word8Array.array 1 a
      val _ = #(act) "" buf
    in Word8Array.sub buf 0 end;

  fun bperform acts =
    case acts of
      [] => []
    | a :: rest => let val r = bdo_act a in r :: bperform rest end;

  fun bget_ready u =
    let
      val buf = Word8Array.array 1 (Word8.fromInt 0)
      val _ = #(ready) "" buf
    in Word8Array.sub buf 0 end;

  fun bselect es =
    let
      val buf = Word8Array.array 1 (Word8.fromInt 0)
      val _ = #(select) (bytes_str es) buf
    in Word8Array.sub buf 0 end;

  fun bstep c =
    case c of (acts, s) =>
      let
        val rs = bperform acts
        val b = (case s of
                   Done2 x => bget_ready ()
                 | Pending2 es k =>
                     (case acts of [] => bselect es | a :: r => bget_ready ()))
      in poll2 c (b, 0, rs) end;
End

Quote add_cakeml:
  fun brun c = brun (bstep c);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Specs of the FFI wrappers
   ------------------------------------------------------------------------ *)


Definition BREADY1_def:
  BREADY1 rdy v ⇔ ∃b:word8. rdy = {b} ∧ WORD b v
End

Theorem sdrop_1[local]:
  sdrop 1 ws = ws o SUC
Proof
  simp[sdrop_def, FUN_EQ_THM, ADD1]
QED

Theorem bdo_act_spec:
  limited_parts io2_names p ∧ WORD a av ⇒
  app (p:'ffi ffi_proj) bdo_act_v [av] (IOS2 ws evs)
    (POSTv v. &WORD (ws 0) v * IOS2 (sdrop 1 ws) (evs ++ [act_event a (ws 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "bdo_act_v_def") >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  ‘REPLICATE 1 a = [a]’ by EVAL_TAC >>
  xlet ‘POSTv u. W8ARRAY bv [ws 0] * IOS2 (sdrop 1 ws) (evs ++ [act_event a (ws 0)])’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘io_state ws’, ‘io2_update’, ‘io2_names’, ‘evs’] >>
      simp[io2_names_def, IOS2_def, io2_update_act_ready, act_event_def] >>
      xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

Theorem bperform_spec:
  ∀acts av ws evs.
    limited_parts io2_names p ∧ LIST_TYPE WORD acts av ⇒
    app (p:'ffi ffi_proj) bperform_v [av] (IOS2 ws evs)
      (POSTv v. &LIST_TYPE WORD (GENLIST ws (LENGTH acts)) v *
                IOS2 (sdrop (LENGTH acts) ws)
                   (evs ++ MAP2 act_event acts (GENLIST ws (LENGTH acts))))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "bperform_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >- (xlet ‘POSTv r. &WORD (ws 0) r * IOS2 (sdrop 1 ws) (evs ++ [act_event h (ws 0)])’
      >- (xapp >> simp[]) >>
      xlet ‘POSTv rv. &LIST_TYPE WORD (GENLIST (sdrop 1 ws) (LENGTH acts)) rv *
              IOS2 (sdrop (LENGTH acts) (sdrop 1 ws))
                 (evs ++ [act_event h (ws 0)] ++
                  MAP2 act_event acts (GENLIST (sdrop 1 ws) (LENGTH acts)))’
      >- (xapp >> simp[]) >>
      xcon >> simp[sdrop_sdrop, GENLIST_CONS, GSYM sdrop_1, ADD1] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
      xsimpl >> simp[LIST_TYPE_def])
QED

Theorem bget_ready_spec:
  limited_parts io2_names p ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) bget_ready_v [uv] (IOS2 ws evs)
    (POSTv v. &WORD (ws 0) v * IOS2 (sdrop 1 ws) (evs ++ [ready_event (ws 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "bget_ready_v_def") >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  xlet ‘POSTv u. W8ARRAY bv [ws 0] * IOS2 (sdrop 1 ws) (evs ++ [ready_event (ws 0)])’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘io_state ws’, ‘io2_update’, ‘io2_names’, ‘evs’] >>
      simp[io2_names_def, IOS2_def, EVAL “REPLICATE 1 (0w:word8)”] >>
      simp[io2_update_act_ready, ready_event_def] >>
      xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

Theorem byte_chr_eq[local]:
  byte_chr = CHR o w2n
Proof
  simp[FUN_EQ_THM, byte_chr_def]
QED

(* MAIN: select on the declared events E blocks until the first declared
   byte of the stream, at position j = skips E ws 0, returns it, and
   records one select event; the bytes before it are consumed. *)
Theorem bselect_spec:
  limited_parts io2_names p ∧ EVLIST WORD E esv ∧ (∃j. ws j ∈ E) ⇒
  app (p:'ffi ffi_proj) bselect_v [esv] (IOS2 ws evs)
    (POSTv v. &WORD (ws (skips E ws 0)) v *
              IOS2 (sdrop (SUC (skips E ws 0)) ws)
                (evs ++ [select_event (SET_TO_LIST E) (ws (skips E ws 0))]))
Proof
  rpt strip_tac >> gvs[EVLIST_def] >>
  ‘io2_update «select» (SET_TO_LIST E) [0w:word8] (io_state ws) =
     SOME (FFIreturn [ws (skips E ws 0)]
             (io_state (sdrop (SUC (skips E ws 0)) ws)))’
    by (‘skips E ws 0 = skips (set (SET_TO_LIST E)) ws 0’
          by simp[SET_TO_LIST_INV] >>
        pop_assum SUBST1_TAC >> irule io2_update_select >>
        gvs[MEM_SET_TO_LIST] >> metis_tac[]) >>
  xcf_with_def (fetch "-" "bselect_v_def") >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  xlet ‘POSTv sv. &STRING_TYPE (bytes_str (SET_TO_LIST E)) sv * W8ARRAY bv [0w] *
                  IOS2 ws evs’
  >- (xapp >> xsimpl >> qexists_tac ‘SET_TO_LIST E’ >> simp[] >> EVAL_TAC) >>
  xlet ‘POSTv u. W8ARRAY bv [ws (skips E ws 0)] *
          IOS2 (sdrop (SUC (skips E ws 0)) ws)
            (evs ++ [select_event (SET_TO_LIST E) (ws (skips E ws 0))])’
  >- (xffi >> xsimpl >>
      gvs[STRING_TYPE_def, bytes_str_def, byte_chr_eq] >>
      qexistsl [‘SET_TO_LIST E’, ‘emp’, ‘io_state ws’, ‘io2_update’,
                ‘io2_names’, ‘evs’] >>
      gvs[io2_names_def, IOS2_def, select_event_def] >> xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

(* ------------------------------------------------------------------------
   One iteration
   ------------------------------------------------------------------------ *)


(* One round of the blocking loop for c (from c's first poll on) against
   the stream ws: the snapshot c is polled with, how many bytes are
   consumed, and the round's I/O events. *)
Definition bstep_world_def:
  bstep_world c ws =
    if blocks c [] then
      let j = skips (c.interest []) ws 0 in
        (idle_snap ws j, SUC j,
         [select_event (SET_TO_LIST (c.interest [])) (ws j)])
    else
      (world_snap ws (LENGTH (c.run []).actions), LENGTH (c.run []).actions + 1,
       round_events_of (c.run []).actions ws)
End

Theorem SNAPSHOT_world_snap[local]:
  WORD (ws k) bv ∧ LIST_TYPE WORD (GENLIST ws k) rsv ∧ NUM 0 nv ⇒
  SNAPSHOT BREADY1 WORD (world_snap ws k) (Conv NONE [bv; nv; rsv])
Proof
  simp[SNAPSHOT_def, world_snap_def, BREADY1_def]
QED

(* MAIN: one iteration of the blocking loop.  If cv implements c, the
   iteration either blocks in select on c's declared events (when c is
   waiting with no action to perform) or performs c's first-round actions
   and reads the ready byte; either way it returns a value implementing c
   with the round's snapshot delivered, as bstep_world says. *)
Theorem bstep_spec:
  limited_parts io2_names p ∧
  COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) c cv ∧
  (blocks c [] ⇒ ∃j. ws j ∈ c.interest []) ⇒
  app (p:'ffi ffi_proj) bstep_v [cv] (IOS2 ws [])
    (POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                 (suspended2 c [FST (bstep_world c ws)]) v *
              IOS2 (sdrop (FST (SND (bstep_world c ws))) ws)
                   (SND (SND (bstep_world c ws))))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP2 _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP2_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "bstep_v_def") >> xmatch >>
  qabbrev_tac ‘k = LENGTH (c.run []).actions’ >>
  xlet ‘POSTv rsv. &LIST_TYPE WORD (GENLIST ws k) rsv *
          IOS2 (sdrop k ws) (MAP2 act_event (c.run []).actions (GENLIST ws k))’
  >- (xapp >> qexistsl [‘emp’, ‘ws’, ‘[]’, ‘(c.run []).actions’] >>
      simp[Abbr ‘k’] >> xsimpl) >>
  qpat_x_assum ‘STEPA2 _ _ _ _ _ _ _’ mp_tac >> simp[Once STEPA2_cases] >>
  strip_tac >> gvs[]
  >- ((* Done2: never blocks; reads the ready byte *)
      ‘¬blocks c []’ by gvs[blocks_def, finished_def] >>
      simp[bstep_world_def] >>
      xlet ‘POSTv bv. &WORD (ws k) bv * IOS2 (sdrop 1 (sdrop k ws))
              (MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
      >- (xmatch >> xlet ‘POSTv u. &UNIT_TYPE () u *
                            IOS2 (sdrop k ws)
                              (MAP2 act_event (c.run []).actions (GENLIST ws k))’
          >- (xcon >> xsimpl) >>
          xapp >> qexistsl [‘emp’, ‘sdrop k ws’,
                            ‘MAP2 act_event (c.run []).actions (GENLIST ws k)’] >>
          ‘sdrop k ws 0 = ws k’ by simp[sdrop_def] >> simp[] >> xsimpl) >>
      xlet ‘POSTv wv. &SNAPSHOT BREADY1 WORD (world_snap ws k) wv *
              IOS2 (sdrop 1 (sdrop k ws))
                (MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
      >- (xcon >> xsimpl >> irule SNAPSHOT_world_snap >> simp[NUM_def, INT_def]) >>
      ‘app p poll2_v [Conv NONE [av; Done2V xv]; wv] emp
         (POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                     (suspended2 c [world_snap ws k]) v)’
        by (irule poll2_spec >> simp[]) >>
      qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl >>
      qunabbrev_tac ‘k’ >>
      fs[sdrop_sdrop, round_events_of_def, finished_def] >> xsimpl)
  >- ((* Pending2 *)
      Cases_on ‘(c.run []).actions = []’
      >- ((* no action to perform: block in select *)
          ‘blocks c []’ by gvs[blocks_def, new_actions_NIL, log_of_def] >>
          qunabbrev_tac ‘k’ >> gvs[LIST_TYPE_def] >> simp[bstep_world_def] >>
          qabbrev_tac ‘jb = skips (c.interest []) ws 0’ >>
          xlet ‘POSTv bv. &WORD (ws jb) bv *
                  IOS2 (sdrop (SUC jb) ws)
                    [select_event (SET_TO_LIST (c.interest [])) (ws jb)]’
          >- (xmatch >> xmatch >> xapp >>
              qexistsl [‘emp’, ‘ws’, ‘[]’, ‘c.interest []’] >>
              fs[Abbr ‘jb’] >> conj_tac >- metis_tac[] >> xsimpl) >>
          xlet ‘POSTv wv. &SNAPSHOT BREADY1 WORD (idle_snap ws jb) wv *
                  IOS2 (sdrop (SUC jb) ws)
                    [select_event (SET_TO_LIST (c.interest [])) (ws jb)]’
          >- (xcon >> xsimpl >>
              simp[SNAPSHOT_def, idle_snap_def, world_snap_def, BREADY1_def,
                   NUM_def, INT_def, LIST_TYPE_def, sdrop_def]) >>
          qpat_x_assum ‘COMP2 _ _ _ _ _ c _’ assume_tac >>
          drule_all poll2_spec >> strip_tac >>
          qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl)
      >- ((* actions to perform: poll *)
          Cases_on ‘(c.run []).actions’ >> gvs[LIST_TYPE_def] >>
          ‘¬blocks c []’ by gvs[blocks_def, new_actions_NIL, log_of_def] >>
          simp[bstep_world_def] >>
          xlet ‘POSTv bv. &WORD (ws k) bv * IOS2 (sdrop 1 (sdrop k ws))
                  (MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
          >- (xmatch >> xmatch >>
              xlet ‘POSTv u. &UNIT_TYPE () u *
                      IOS2 (sdrop k ws)
                        (MAP2 act_event (c.run []).actions (GENLIST ws k))’
              >- (xcon >> xsimpl) >>
              xapp >> qexistsl [‘emp’, ‘sdrop k ws’,
                                ‘MAP2 act_event (c.run []).actions (GENLIST ws k)’] >>
              ‘sdrop k ws 0 = ws k’ by simp[sdrop_def] >> simp[] >> xsimpl) >>
          xlet ‘POSTv wv. &SNAPSHOT BREADY1 WORD (world_snap ws k) wv *
                  IOS2 (sdrop 1 (sdrop k ws))
                    (MAP2 act_event (c.run []).actions (GENLIST ws k) ++ [ready_event (ws k)])’
          >- (xcon >> xsimpl >> irule SNAPSHOT_world_snap >> simp[NUM_def, INT_def]) >>
          qpat_x_assum ‘COMP2 _ _ _ _ _ c _’ assume_tac >>
          drule_all poll2_spec >> strip_tac >>
          qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl >>
          simp[sdrop_sdrop, round_events_of_def, Abbr ‘k’] >> xsimpl))
QED

(* ------------------------------------------------------------------------
   The loop
   ------------------------------------------------------------------------ *)


Theorem suspended2_NIL[simp]:
  suspended2 c [] = c
Proof
  simp[DB.fetch "asyncLevel2" "comp2_component_equality", suspended2_def,
       FUN_EQ_THM]
QED

Theorem suspended2_suspended2_one:
  wf c.run ⇒ suspended2 (suspended2 c r) [w] = suspended2 c (r ++ [w])
Proof
  strip_tac >>
  gvs[DB.fetch "asyncLevel2" "comp2_component_equality", suspended2_def,
      suspended_suspended_one, FUN_EQ_THM] >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
QED

Theorem blocks_suspended2:
  wf c.run ⇒
  (blocks (suspended2 c kept) [] ⇔ blocks c kept) ∧
  (suspended2 c kept).interest [] = c.interest kept ∧
  ((suspended2 c kept).run []).actions = new_actions (log_of c.run) kept
Proof
  strip_tac >>
  simp[blocks_def, suspended2_def, suspended_first_poll, new_actions_NIL,
       log_of_def]
QED

Theorem skips_sdrop[local]:
  skips E (sdrop pos ws) 0 = skips E ws pos
Proof
  simp[skips_def, sdrop_def]
QED

(* One round of brounds is one bstep_world of the suspended computation
   on the rest of the stream. *)
Theorem bstep_world_brounds:
  wf c.run ∧ brounds c ws i = (kept, full, pos) ⇒
  FST (brounds c ws (SUC i)) =
    kept ++ [FST (bstep_world (suspended2 c kept) (sdrop pos ws))] ∧
  SND (SND (brounds c ws (SUC i))) =
    pos + FST (SND (bstep_world (suspended2 c kept) (sdrop pos ws))) ∧
  bround_events c ws i = SND (SND (bstep_world (suspended2 c kept) (sdrop pos ws)))
Proof
  strip_tac >> drule blocks_suspended2 >> strip_tac >>
  simp[brounds_def, bstep_world_def, bround_events_def] >>
  rw[skips_sdrop, idle_snap_def, sdrop_sdrop, ADD1] >>
  simp[sdrop_def]
QED

(* MAIN: the blocking event loop never terminates, and its I/O trace is the
   concatenation of bround_events c ws i over all rounds i: either one
   select on c's declared events (when c waits with nothing to perform) or
   the round's actions and the ready byte.  By trace_actions_brounds, the
   actions in the trace are c's action log over the kept history, and by
   blocking_same_actions that is exactly the polling loop's (asyncCfActLoop)
   action log over the same stream: no busy waiting, same behaviour.
   Assumptions: wf c.run (every library computation) and blk_live c ws
   (whenever the loop blocks, a declared byte eventually arrives). *)
Theorem brun_spec:
  limited_parts io2_names p ∧ wf c.run ∧ blk_live c ws ∧
  COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) c cv ⇒
  app (p:'ffi ffi_proj) brun_v [cv] (IOS2 ws [])
    (POSTd io. io = LFLATTEN (LGENLIST (λi. fromList (bround_events c ws i)) NONE))
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "brun" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then [] else bround_events c ws (i - 1)’ >>
  qexists_tac ‘λi cv. COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                        (suspended2 c (FST (brounds c ws i))) cv’ >>
  qexists_tac ‘λi. io_state (sdrop (SND (SND (brounds c ws i))) ws)’ >>
  qexists_tac ‘io2_update’ >>
  simp[CONJUNCT1 brounds_def] >> rpt conj_tac
  >- (simp[IOS2_def] >> xsimpl)
  >- (rpt strip_tac >> simp[GSYM IOS2_def] >>
      ‘∃kept full pos. brounds c ws i = (kept, full, pos)’
        by metis_tac[pair_CASES] >>
      drule_all bstep_world_brounds >> strip_tac >>
      drule blocks_suspended2 >> strip_tac >>
      gvs[] >>
      qabbrev_tac ‘bw = bstep_world (suspended2 c kept) (sdrop pos ws)’ >>
      ‘app p bstep_v [xv] (IOS2 (sdrop pos ws) [])
         (POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                      (suspended2 (suspended2 c kept) [FST bw]) v *
                   IOS2 (sdrop (FST (SND bw)) (sdrop pos ws)) (SND (SND bw)))’
        by (simp[Abbr ‘bw’] >> irule bstep_spec >> simp[] >>
            gvs[blk_live_def, sdrop_def] >> rpt strip_tac >>
            first_x_assum drule >> simp[] >> metis_tac[ADD_COMM]) >>
      xlet ‘POSTv v. &COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD)
                        (suspended2 c (kept ++ [FST bw])) v *
                      IOS2 (sdrop (pos + FST (SND bw)) ws) (SND (SND bw))’
      >- (qpat_x_assum ‘app _ bstep_v _ _ _’ xapp_spec >> xsimpl >>
          simp[suspended2_suspended2_one, sdrop_sdrop] >> xsimpl) >>
      xvar >> xsimpl >> simp[IOS2_def] >> xsimpl)
  >- simp[LFLATTEN_LGENLIST_shift]
QED

(* MAIN (no busy waiting, end to end): after n+1 rounds of the blocking
   loop, the actions in its trace are exactly the actions in the trace of
   the polling loop of cf-actions (asyncCfActLoop.run_spec, round_events)
   after the same stretch of the stream -- LENGTH full + 1 polling rounds,
   most of which the blocking loop slept through in select. *)
Theorem blocking_trace_same_actions:
  wf c.run ∧ quiet c ∧ blk_live c ws ∧ brounds c ws n = (kept, full, pos) ⇒
  trace_actions (FLAT (GENLIST (bround_events c ws) (SUC n))) =
  trace_actions (FLAT (GENLIST (round_events c.run ws) (SUC (LENGTH full))))
Proof
  strip_tac >>
  drule_all blocking_same_actions >> strip_tac >>
  simp[trace_actions_brounds, trace_actions_rounds] >>
  metis_tac[]
QED
