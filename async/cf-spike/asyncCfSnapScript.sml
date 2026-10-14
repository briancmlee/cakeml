(*
  The pure HOL side of the toy event loop (asyncCfLoopScript.sml):
  a minimal, self-contained FFI model of a stream of one-byte world
  snapshots, the model computation after a list of snapshots, and a lazy
  list lemma for the loop's trace.
*)
Theory asyncCfSnap
Ancestors
  asyncCfModel cfFFIType cfHeapsBase cfDiv ffi llist
Libs
  preamble

(* ------------------------------------------------------------------------
   A minimal FFI model: get_snapshot reads the next byte of a stream
   ------------------------------------------------------------------------ *)

Definition snap_names_def:
  snap_names = [«get_snapshot»]
End

(* The FFI's state for the snapshot stream s (snapshot i is s i). *)
Definition snap_state_def:
  snap_state (s : num -> word8) = Stream (LGENLIST (λi. w2n (s i)) NONE)
End

(* The FFI function: get_snapshot with an empty config and a one-byte
   buffer writes the next snapshot into the buffer. *)
Definition snap_update_def:
  snap_update n conf bytes st =
    if n = «get_snapshot» ∧ conf = [] ∧ LENGTH bytes = 1 then
      case destStream st of
      | NONE => NONE
      | SOME ll =>
          case LHD ll of
          | NONE => NONE
          | SOME w => SOME (FFIreturn [n2w w] (Stream (THE (LTL ll))))
    else NONE
End

(* The I/O event of one get_snapshot call that returned snapshot w. *)
Definition snap_event_def:
  snap_event (w : word8) = IO_event (ExtCall «get_snapshot») [] [(0w, w)]
End

(* SNAP s evs: the snapshot FFI, with remaining stream s and past events evs. *)
Definition SNAP_def:
  SNAP s evs = one (FFI_part (snap_state s) snap_update snap_names evs)
End

(* The stream after its first snapshot has been consumed. *)
Definition stail_def:
  stail (s : num -> word8) = λi. s (SUC i)
End

(* One get_snapshot call: returns the first snapshot, consumes it. *)
Theorem snap_update_get:
  snap_update «get_snapshot» [] [b] (snap_state s) =
  SOME (FFIreturn [s 0] (snap_state (stail s)))
Proof
  simp[snap_update_def, snap_state_def, Once LGENLIST_NONE_UNFOLD] >>
  simp[stail_def, combinTheory.o_DEF, ADD1]
QED

(* ------------------------------------------------------------------------
   The model after a list of snapshots
   ------------------------------------------------------------------------ *)

(* m after being polled with the snapshots ws, oldest first. *)
Definition after_list_def:
  after_list ws (m : 'w list -> 'a option) = λh. m (ws ++ h)
End

Theorem after_list_NIL:
  after_list [] m = m
Proof
  simp[after_list_def, FUN_EQ_THM]
QED

Theorem after_after_list:
  after w (after_list ws m) = after_list (ws ++ [w]) m
Proof
  simp[after_def, after_list_def, FUN_EQ_THM] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

(* ------------------------------------------------------------------------
   Lazy-list lemma for the trace
   ------------------------------------------------------------------------ *)

Theorem LGENLIST_shift:
  LGENLIST (λi. f (i + k)) NONE = f k ::: LGENLIST (λi. f (i + (k + 1))) NONE
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem LGENLIST_singletons_shift[local]:
  LGENLIST (λi. [|e (i + k)|]) NONE =
  [|e k|] ::: LGENLIST (λi. [|e (i + (k + 1))|]) NONE
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

(* Flattening an infinite list of one-element lists. *)
Theorem LFLATTEN_LGENLIST_singletons:
  LFLATTEN (LGENLIST (λi. [|e i|]) NONE) = LGENLIST e NONE
Proof
  simp[Once LLIST_BISIMULATION0] >>
  qexists_tac ‘λa b. ∃k. a = LFLATTEN (LGENLIST (λi. [|e (k + i)|]) NONE) ∧
                         b = LGENLIST (λi. e (k + i)) NONE’ >>
  rw[] >- (qexists_tac ‘0’ >> simp[ETA_AX]) >>
  ONCE_REWRITE_TAC[LGENLIST_shift] >> simp[] >>
  qexists_tac ‘LFLATTEN (LGENLIST (λi. [|e (i + (k + 1))|]) NONE)’ >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_singletons_shift])) >>
      simp[]) >>
  qexists_tac ‘k + 1’ >> simp[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_shift])) >> simp[]
QED

