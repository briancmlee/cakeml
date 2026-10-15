(*
  The pure HOL side of the event loop with actions (asyncCfActLoopScript.sml):
  a minimal, self-contained FFI model, the snapshot sequence the world
  provides, and the link between the loop's I/O trace and the model's
  action log.

  The world (an assumption made for this spike, see 05-cf-actions.md):
  - actions and responses are bytes;
  - one FFI call `act` performs one action: the action byte goes in a
    one-byte buffer, and the world writes the response byte into it;
  - one FFI call `ready` returns one byte b, the round's ready set {b};
  - the world is an infinite stream of bytes ws, consumed in order by both
    calls (so responses do not depend on the action: an oblivious world);
  - the time `now` is always 0.

  Each loop iteration performs the round's actions in order, then reads the
  ready byte, then polls the computation with the snapshot
  <| ready := {b}; now := 0; results := the responses |>.
*)
Theory asyncCfActWorld
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel
  cfFFIType cfHeapsBase cfDiv ffi llist
Libs
  preamble

(* ------------------------------------------------------------------------
   The FFI model
   ------------------------------------------------------------------------ *)

Definition io_names_def:
  io_names = [«act»; «ready»]
End

(* The FFI state for the byte stream ws (byte i is ws i) *)
Definition io_state_def:
  io_state (ws : num -> word8) = Stream (LGENLIST (λi. w2n (ws i)) NONE)
End

(* Both calls take an empty config and a one-byte buffer, and overwrite the
   buffer with the next byte of the stream. *)
Definition io_update_def:
  io_update n conf bytes st =
    if MEM n io_names ∧ conf = [] ∧ LENGTH bytes = 1 then
      case destStream st of
      | NONE => NONE
      | SOME ll =>
          case LHD ll of
          | NONE => NONE
          | SOME w => SOME (FFIreturn [n2w w] (Stream (THE (LTL ll))))
    else NONE
End

(* The stream without its first k bytes *)
Definition sdrop_def:
  sdrop k (ws : num -> word8) = λi. ws (i + k)
End

(* IOS ws evs: the FFI, with remaining stream ws and past events evs *)
Definition IOS_def:
  IOS ws evs = one (FFI_part (io_state ws) io_update io_names evs)
End

(* The I/O event of performing action a, with response r *)
Definition act_event_def:
  act_event (a : word8) (r : word8) = IO_event (ExtCall «act») [] [(a, r)]
End

(* The I/O event of reading the ready byte b *)
Definition ready_event_def:
  ready_event (b : word8) = IO_event (ExtCall «ready») [] [(0w, b)]
End

Theorem io_update_next:
  MEM n io_names ⇒
  io_update n [] [b] (io_state ws) =
  SOME (FFIreturn [ws 0] (io_state (sdrop 1 ws)))
Proof
  simp[io_update_def, io_state_def, Once LGENLIST_NONE_UNFOLD] >>
  simp[sdrop_def, combinTheory.o_DEF, ADD1]
QED

Theorem sdrop_sdrop:
  sdrop j (sdrop k ws) = sdrop (j + k) ws
Proof
  simp[sdrop_def, FUN_EQ_THM]
QED

Theorem sdrop_0[simp]:
  sdrop 0 ws = ws
Proof
  simp[sdrop_def, FUN_EQ_THM, ETA_AX]
QED

(* ------------------------------------------------------------------------
   One round, and the snapshot sequence the world provides
   ------------------------------------------------------------------------ *)

(* The snapshot built after performing k actions against the stream ws:
   the responses are the first k bytes, the ready byte the next one. *)
Definition world_snap_def:
  world_snap (ws : num -> word8) k =
    <| ready := {ws k}; now := 0; results := GENLIST ws k |>
End

(* The events of one round that performs the actions acts against ws *)
Definition round_events_of_def:
  round_events_of acts ws =
    MAP2 act_event acts (GENLIST ws (LENGTH acts)) ++
    [ready_event (ws (LENGTH acts))]
End

(* rounds m ws n = (h, pos): after n rounds of the loop running m against
   the stream ws, the history of snapshots m has been polled with, and how
   many bytes of the stream have been consumed. *)
Definition rounds_def:
  rounds m ws 0 = ([], 0n) ∧
  rounds m ws (SUC n) =
    let (h, pos) = rounds m ws n;
        k = LENGTH (new_actions (log_of m) h)
    in (h ++ [world_snap (sdrop pos ws) k], pos + k + 1)
End

(* The history of snapshots after n rounds *)
Definition hist_def:
  hist m ws n = FST (rounds m ws n)
End

(* The I/O events of round n: the model's new actions in that round,
   performed against the rest of the stream *)
Definition round_events_def:
  round_events m ws n =
    let (h, pos) = rounds m ws n in
    round_events_of (new_actions (log_of m) h) (sdrop pos ws)
End

Theorem rounds_SUC:
  rounds m ws (SUC n) =
    (FST (rounds m ws n) ++
       [world_snap (sdrop (SND (rounds m ws n)) ws)
                   (LENGTH (new_actions (log_of m) (FST (rounds m ws n))))],
     SND (rounds m ws n) +
       LENGTH (new_actions (log_of m) (FST (rounds m ws n))) + 1)
Proof
  simp[rounds_def] >> Cases_on ‘rounds m ws n’ >> simp[]
QED

Theorem round_events_alt:
  round_events m ws n =
    round_events_of (new_actions (log_of m) (FST (rounds m ws n)))
                    (sdrop (SND (rounds m ws n)) ws)
Proof
  simp[round_events_def] >> Cases_on ‘rounds m ws n’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The actions recorded in a trace
   ------------------------------------------------------------------------ *)

(* The action performed by an event, if it is an `act` event *)
Definition event_action_def:
  event_action (IO_event (ExtCall n) conf bytes) =
    (if n = «act» ∧ conf = [] then MAP FST bytes else []) ∧
  event_action _ = []
End

(* All actions performed in a finite trace, in order *)
Definition trace_actions_def:
  trace_actions evs = FLAT (MAP event_action evs)
End

Theorem trace_actions_APPEND:
  trace_actions (xs ++ ys) = trace_actions xs ++ trace_actions ys
Proof
  simp[trace_actions_def]
QED

Theorem trace_actions_round_events_of:
  ∀acts ws. trace_actions (round_events_of acts ws) = acts
Proof
  Induct >>
  simp[round_events_of_def, trace_actions_def, event_action_def,
       ready_event_def, act_event_def, GENLIST_CONS] >>
  rpt strip_tac >>
  first_x_assum (qspec_then ‘ws o SUC’ mp_tac) >>
  simp[round_events_of_def, trace_actions_def, event_action_def,
       ready_event_def]
QED

(* MAIN: the trace and the model agree.  The actions performed in the
   first n+1 rounds of the loop's trace are exactly the model's action log
   after the n snapshots the world has provided. *)
Theorem trace_actions_rounds:
  wf m ⇒
  trace_actions (FLAT (GENLIST (round_events m ws) (SUC n))) =
  (m (hist m ws n)).actions
Proof
  strip_tac >> Induct_on ‘n’
  >- simp[round_events_alt, rounds_def, hist_def,
          trace_actions_round_events_of, new_actions_NIL, log_of_def] >>
  ONCE_REWRITE_TAC[GENLIST] >>
  simp[SNOC_APPEND, FLAT_APPEND, trace_actions_APPEND] >>
  simp[round_events_alt, trace_actions_round_events_of, hist_def] >>
  simp[rounds_SUC] >>
  gvs[hist_def] >>
  qmatch_goalsub_abbrev_tac ‘new_actions _ (h ++ [s])’ >>
  ‘log_of m h ≼ log_of m (h ++ [s])’ by simp[log_of_def, wf_SNOC_actions] >>
  drule new_actions_prefix >> simp[log_of_def]
QED

(* ------------------------------------------------------------------------
   Lazy-list lemma for the trace
   ------------------------------------------------------------------------ *)

(* The first iteration of cfDiv's loop rule has no events of its own *)
Theorem LFLATTEN_LGENLIST_shift:
  LFLATTEN (LGENLIST (fromList o (λi. if i = 0 then [] else e (i - 1))) NONE) =
  LFLATTEN (LGENLIST (λi. fromList (e i)) NONE)
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED
