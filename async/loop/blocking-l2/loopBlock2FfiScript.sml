(*
  The FFI of the blocking event loop: cf-actions' byte-stream part (act,
  ready) plus a blocking `select`.

  select takes the declared events (bytes) as its config and a one-byte
  buffer.  It skips the stream's bytes that are not declared and returns
  the first declared one, consuming everything up to it.  If no declared
  byte ever comes, it blocks forever (FFIdiverge).
*)
Theory loopBlock2Ffi
Ancestors
  cfFFIType cfHeapsBase cfDiv ffi llist asyncCore asyncLevel1 asyncChoose
  asyncLevel2 libWorld loopBlock2World
Libs
  preamble

Definition io2_names_def:
  io2_names = [«act»; «ready»; «select»]
End

Definition io2_update_def:
  io2_update n conf bytes st =
    if n = «select» then
      if LENGTH bytes = 1 then
        case destStream st of
        | NONE => NONE
        | SOME ll =>
            if ∃j b. LNTH j ll = SOME b ∧ MEM (n2w b) conf then
              let j = LEAST j. ∃b. LNTH j ll = SOME b ∧ MEM (n2w b) conf in
                SOME (FFIreturn [n2w (THE (LNTH j ll))]
                                (Stream (THE (LDROP (SUC j) ll))))
            else SOME FFIdiverge
      else NONE
    else io_update n conf bytes st
End

(* IOS2 ws evs: the FFI, with remaining stream ws and past events evs *)
Definition IOS2_def:
  IOS2 ws evs = one (FFI_part (io_state ws) io2_update io2_names evs)
End

(* The I/O event of a select on the declared bytes l, returning b *)
Definition select_event_def:
  select_event (l : word8 list) (b : word8) =
    IO_event (ExtCall «select») l [(0w, b)]
End

Theorem io2_update_act_ready:
  (n = «act» ∨ n = «ready») ⇒
  io2_update n [] [b] (io_state ws) =
  SOME (FFIreturn [ws 0] (io_state (sdrop 1 ws)))
Proof
  strip_tac >> simp[io2_update_def] >>
  irule io_update_next >> gvs[io_names_def]
QED

Theorem LDROP_LGENLIST[local]:
  ∀k f. LDROP k (LGENLIST f NONE) = SOME (LGENLIST (λi. f (i + k)) NONE)
Proof
  Induct >> simp[ETA_AX] >> rw[] >>
  CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD]))) >>
  simp[LDROP_THM, combinTheory.o_DEF] >>
  simp[ADD1]
QED

(* select on the stream ws, when a declared byte comes: it returns the
   first one, at position skips (set l) ws 0, and consumes up to it. *)
Theorem io2_update_select:
  (∃j. ws j ∈ set l) ⇒
  io2_update «select» l [b] (io_state ws) =
  SOME (FFIreturn [ws (skips (set l) ws 0)]
                  (io_state (sdrop (SUC (skips (set l) ws 0)) ws)))
Proof
  strip_tac >>
  ‘(λj. ∃b. LNTH j (LGENLIST (λi. w2n (ws i)) NONE) = SOME b ∧ MEM (n2w b) l) =
   (λj. MEM (ws j) l)’ by simp[FUN_EQ_THM, LNTH_LGENLIST, n2w_w2n] >>
  ‘(LEAST j. MEM (ws j) l) = skips (set l) ws 0’ by simp[skips_def] >>
  ‘∃j. MEM (ws j) l’ by metis_tac[] >>
  simp[io2_update_def, io_state_def] >>
  pop_assum mp_tac >> pop_assum kall_tac >> strip_tac >>
  IF_CASES_TAC
  >- simp[LNTH_LGENLIST, n2w_w2n, LDROP_LGENLIST, sdrop_def, ADD1]
  >- metis_tac[]
QED

(* ------------------------------------------------------------------------
   The I/O events of the blocking loop, and the actions in its trace
   ------------------------------------------------------------------------ *)

(* Round n of the blocking loop: either one select on the declared events
   (the canonical list SET_TO_LIST), returning the first declared byte, or
   a polling round (the round's actions, then the ready byte) *)
Definition bround_events_def:
  bround_events c ws n =
    let (kept, full, pos) = brounds c ws n in
    if blocks c kept then
      [select_event (SET_TO_LIST (c.interest kept))
                    (ws (pos + skips (c.interest kept) ws pos))]
    else round_events_of (new_actions (log_of c.run) kept) (sdrop pos ws)
End

Theorem brounds_kept_SUC:
  ∃s. FST (brounds c ws (SUC n)) = FST (brounds c ws n) ++ [s]
Proof
  simp[brounds_def] >>
  ‘∃kept full pos. brounds c ws n = (kept, full, pos)’ by metis_tac[pair_CASES] >>
  simp[] >> rw[]
QED

Theorem trace_actions_bround_events:
  trace_actions (bround_events c ws n) =
  new_actions (log_of c.run) (FST (brounds c ws n))
Proof
  simp[bround_events_def] >>
  ‘∃kept full pos. brounds c ws n = (kept, full, pos)’ by metis_tac[pair_CASES] >>
  rw[trace_actions_round_events_of] >>
  gvs[blocks_def, trace_actions_def, select_event_def, event_action_def]
QED

(* MAIN: the actions performed in the first n+1 rounds of the blocking
   loop are exactly c's action log after the kept history (and so, by
   blocking_same_actions, the polling loop's). *)
Theorem trace_actions_brounds:
  wf c.run ⇒
  trace_actions (FLAT (GENLIST (bround_events c ws) (SUC n))) =
  (c.run (FST (brounds c ws n))).actions
Proof
  strip_tac >> Induct_on ‘n’
  >- simp[trace_actions_bround_events, brounds_def, new_actions_NIL, log_of_def] >>
  ONCE_REWRITE_TAC[GENLIST] >>
  simp[SNOC_APPEND, FLAT_APPEND, trace_actions_APPEND] >>
  simp[trace_actions_bround_events] >>
  qspecl_then [‘ws’, ‘n’, ‘c’] strip_assume_tac (GEN_ALL brounds_kept_SUC) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac ‘new_actions _ (h ++ [s])’ >>
  ‘log_of c.run h ≼ log_of c.run (h ++ [s])’ by simp[log_of_def, wf_SNOC_actions] >>
  drule new_actions_prefix >> simp[log_of_def]
QED
