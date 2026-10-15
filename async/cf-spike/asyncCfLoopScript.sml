(*
  A toy never-ending event loop, proved with CakeML's divergence CF
  (characteristic/cfDivScript.sml, Åman Pohjola, Rostedt and Myreen, ITP 2019).

      fun step s = poll s (get_snapshot ());
      fun run s = run (step s);

  get_snapshot is an FFI call against a minimal, self-contained FFI model
  (asyncCfSnapScript.sml): an infinite stream of one-byte world snapshots.  The loop
  never terminates; its I/O trace is the infinite sequence of get_snapshot
  events, and after i iterations the residual implements the model
  computation after the first i snapshots.  See async/design/03-cf-loop.md.
*)
Theory asyncCfLoop
Ancestors
  asyncCfModel asyncCfSnap asyncCfProg cfDiv ml_translator mlbasicsProg
  Word8Prog Word8ArrayProof llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfProg"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun get_snapshot u =
    let
      val a = Word8Array.array 1 (Word8.fromInt 0)
      val _ = #(get_snapshot) "" a
    in Word8Array.sub a 0 end;
End

Quote add_cakeml:
  fun step s = poll s (get_snapshot ());
End

Quote add_cakeml:
  fun run s = run (step s);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Specs
   ------------------------------------------------------------------------ *)

(* get_snapshot returns the next snapshot and records one event. *)
Theorem get_snapshot_spec:
  limited_parts snap_names p ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) get_snapshot_v [uv] (SNAP s evs)
    (POSTv v. &WORD (s 0) v * SNAP (stail s) (evs ++ [snap_event (s 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "get_snapshot_v_def") >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY av’ >>
  xlet ‘POSTv u. W8ARRAY av [s 0] * SNAP (stail s) (evs ++ [snap_event (s 0)])’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘snap_state s’, ‘snap_update’, ‘snap_names’, ‘evs’] >>
      simp[snap_names_def, SNAP_def, EVAL “REPLICATE 1 (0w:word8)”] >>
      simp[snap_update_get, snap_event_def] >>
      xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

(* MAIN: one loop iteration.  If the residual sv implements m, then after
   reading the next snapshot w = s 0 and polling, the new residual
   implements m after w, and exactly one get_snapshot event happened. *)
Theorem step_spec:
  limited_parts snap_names p ∧ STEP p A WORD m sv ⇒
  app (p:'ffi ffi_proj) step_v [sv] (SNAP s evs)
    (POSTv v. &STEP p A WORD (after (s 0) m) v *
              SNAP (stail s) (evs ++ [snap_event (s 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "step_v_def") >>
  xlet ‘POSTv u. &UNIT_TYPE () u * SNAP s evs’ >- (xcon >> xsimpl) >>
  xlet ‘POSTv w. &WORD (s 0) w * SNAP (stail s) (evs ++ [snap_event (s 0)])’
  >- (xapp >> simp[]) >>
  xapp_spec (INST_TYPE [beta |-> “:word8”] poll_spec) >> xsimpl >>
  qexistsl [‘s 0’, ‘m’, ‘WORD’, ‘A’] >> simp[]
QED

(* MAIN: the event loop never terminates, and its I/O trace is the infinite
   sequence of get_snapshot events, one per snapshot of the stream s.
   (The residual after i iterations implements after_list (GENLIST s i) m;
   see step_spec, which is the loop invariant.) *)
Theorem run_spec:
  limited_parts snap_names p ∧ STEP p A WORD (m : word8 list -> 'a option) sv ⇒
  app (p:'ffi ffi_proj) run_v [sv] (SNAP s [])
    (POSTd io. io = LGENLIST (λi. snap_event (s i)) NONE)
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then [] else [snap_event (s (i - 1))]’ >>
  qexists_tac ‘λi sv. STEP p A WORD (after_list (GENLIST s i) m) sv’ >>
  qexists_tac ‘λi. snap_state (λj. s (i + j))’ >>
  qexists_tac ‘snap_update’ >>
  gvs[after_list_NIL] >> rpt conj_tac
  >- (simp[SNAP_def, ETA_AX] >> xsimpl)
  >- ((* one iteration: step_spec, with the residual's model advanced *)
      rpt strip_tac >> simp[GSYM SNAP_def] >>
      xlet ‘POSTv v. &STEP p A WORD (after (s i) (after_list (GENLIST s i) m)) v *
                     SNAP (stail (λj. s (i + j))) [snap_event (s i)]’
      >- (xapp >> xsimpl >>
          qexistsl [‘emp’, ‘λj. s (i + j)’, ‘after_list (GENLIST s i) m’,
                    ‘[]’, ‘A’] >>
          simp[] >> xsimpl) >>
      xvar >> xsimpl >>
      ‘stail (λj. s (i + j)) = (λj. s (j + SUC i))’
        by (rw[stail_def, FUN_EQ_THM] >> AP_TERM_TAC >> decide_tac) >>
      gvs[GENLIST, SNOC_APPEND, after_after_list] >> xsimpl)
  >- ((* the trace: no event before the first iteration, then one each *)
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
      simp[combinTheory.o_DEF] >>
      simp[LFLATTEN_LGENLIST_singletons])
QED
