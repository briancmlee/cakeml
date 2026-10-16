(*
  Examples: the echo loop, and small programs evaluated on concrete
  histories (sanity checks that the definitions mean what we think).

  A toy world: events are fds becoming readable, and actions are reads and
  writes on fds.
*)
Theory asyncEcho
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop
Libs
  BasicProvers

Datatype:
  event = Readable num | Writable num | Timer num | Always
End

Datatype:
  action = Read num | Write num string
End

(* The response to a Read may be data, "would block" (readiness is only a
   hint) or end of file.  A Write is acknowledged with Written. *)
Datatype:
  response = Data string | WouldBlock | Eof | Written
End

(* Finishes at the first snapshot in which fd is readable *)
Definition readable_def:
  readable fd = wait (λs. if Readable fd ∈ s.ready then SOME () else NONE)
End

(* ------------------------------------------------------------------------
   The echo loop

     echo fd = wait until fd is readable;
               read fd;
               on Data d:     write d to fd, then echo fd
               on WouldBlock: echo fd
               on Eof:        stop
   ------------------------------------------------------------------------ *)

Definition echo_body_def:
  echo_body r fd =
    bind (readable fd) (λu.
    bind (emit (Read fd)) (λres.
      case res of
        Data d => bind (emit (Write fd d)) (λw. r fd)
      | Eof => return ()
      | _ => r fd))
End

Theorem echo_body_contractive:
  contractive echo_body
Proof
  rw[contractive_def, echo_body_def]
  (* the recursive calls come after `readable fd`, which needs a snapshot *)
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call, nonexpansive_const]
  >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const, nonexpansive_call]
QED

Definition echo_def:
  echo = fix echo_body
End

(* MAIN: echo satisfies its recursive equation *)
Theorem echo_unfold:
  echo fd =
    bind (readable fd) (λu.
    bind (emit (Read fd)) (λres.
      case res of
        Data d => bind (emit (Write fd d)) (λw. echo fd)
      | Eof => return ()
      | _ => echo fd))
Proof
  simp[echo_def]
  >> simp[Once (MATCH_MP fix_unfold echo_body_contractive)]
  >> simp[echo_body_def]
QED

Theorem wf_echo_body:
  (∀p. wf (r p)) ⇒ wf (echo_body r fd)
Proof
  rw[echo_body_def]
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases
  >> simp[wf_return] >> irule wf_bind >> simp[wf_emit]
QED

(* MAIN: echo is well-formed *)
Theorem wf_echo:
  wf (echo fd)
Proof
  simp[echo_def] >> irule wf_fix >> simp[echo_body_contractive, wf_echo_body]
QED

Theorem settled_echo_body:
  (∀p. settled (r p)) ⇒ settled (echo_body r fd)
Proof
  rw[echo_body_def]
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases
  >> simp[settled_return] >> irule settled_bind >> simp[wf_emit, settled_emit]
QED

(* MAIN: echo never loses a response *)
Theorem settled_echo:
  settled (echo fd)
Proof
  simp[echo_def] >> irule settled_fix
  >> simp[echo_body_contractive, settled_echo_body]
QED

(* ------------------------------------------------------------------------
   Sanity checks on concrete histories (each proved by evaluation)
   ------------------------------------------------------------------------ *)

(* A snapshot at time 0 with the given ready events and responses *)
Definition snap_def:
  snap rdy res = <| ready := rdy; now := 0; results := res |>
End

(* emit a, then emit b: each response goes to the emit that asked for it *)
Theorem example_bind_emit:
  bind (emit "a") (λx. bind (emit "b") (λy. return (x, y)))
       [snap ({} : num set) [1]; snap {} [2 : num]] =
    <| actions := ["a"; "b"]; result := SOME (1, 2) |>
Proof
  EVAL_TAC
QED

(* Two emits side by side: one snapshot answers both, left first *)
Theorem example_both:
  both (emit "a") (emit "b") [snap ({} : num set) [1; 2 : num]] =
    <| actions := ["a"; "b"]; result := SOME (1, 2) |>
Proof
  EVAL_TAC
QED

(* Routing: in round 1 only the left side emits (c), so the whole of
   snapshot 2's results go to it *)
Theorem example_both_routing:
  both (bind (emit "a") (λx. emit "c")) (emit "b")
       [snap ({} : num set) [1; 2]; snap {} [3 : num]] =
    <| actions := ["a"; "b"; "c"]; result := SOME (3, 2) |>
Proof
  EVAL_TAC
QED

(* Ties go to the left side *)
Theorem example_choose_tie:
  map (λr. case r of INL (x, _) => INL x | INR (_, y) => INR y)
      (choose (wait (λs. if 3 ∈ s.ready then SOME (3 : num) else NONE))
              (emit "b"))
      [snap {3 : num} [7 : num]] =
    <| actions := ["b"]; result := SOME (INL 3) |>
Proof
  EVAL_TAC
QED

(* ... and the loser keeps the response to its request *)
Theorem example_choose_tie_rejoin:
  bind (choose (wait (λs. if 3 ∈ s.ready then SOME (3 : num) else NONE))
               (emit "b"))
       rejoin
       [snap {3 : num} [7 : num]] =
    <| actions := ["b"]; result := SOME (3, 7) |>
Proof
  EVAL_TAC
QED

(* return 5 wins at once, but emit "a" has a request in flight: choose
   waits one round for its response... *)
Theorem example_choose_waits:
  choose (emit "a") (return (5 : num)) ([] : (num, num) snapshot list) =
    <| actions := ["a"]; result := NONE |>
Proof
  EVAL_TAC
QED

(* ... so that the loser, continued, gets it *)
Theorem example_choose_rejoin:
  bind (choose (emit "a") (return (5 : num))) rejoin
       [snap ({} : num set) [42 : num]] =
    <| actions := ["a"]; result := SOME (42, 5) |>
Proof
  EVAL_TAC
QED

(* echo reads "hi", writes it back, and waits for fd 0 to become readable
   again *)
Theorem example_echo:
  echo 0 [snap {Readable 0} []; snap {} [Data "hi"]; snap {} [Written]] =
    <| actions := [Read 0; Write 0 "hi"]; result := NONE |>
Proof
  EVAL_TAC
QED

(* ... and stops at end of file *)
Theorem example_echo_eof:
  echo 0 [snap {Readable 0} []; snap {} [Data "hi"]; snap {} [Written];
          snap {Readable 0} []; snap {} [Eof]] =
    <| actions := [Read 0; Write 0 "hi"; Read 0]; result := SOME () |>
Proof
  EVAL_TAC
QED

(* Readiness is only a hint: a read may still say "would block", and echo
   then simply waits again *)
Theorem example_echo_wouldblock:
  echo 0 [snap {Readable 0} []; snap {} [WouldBlock];
          snap {Readable 0} []; snap {} [Data "x"]] =
    <| actions := [Read 0; Read 0; Write 0 "x"]; result := NONE |>
Proof
  EVAL_TAC
QED
