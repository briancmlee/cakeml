(*
  choose, in the style of OCaml's Async: nothing is lost.

  choose m1 m2 runs m1 and m2 side by side until one of them finishes.  It
  returns the winner's result together with the loser, *still running*, as
  a computation the caller can continue (or drop):

     choose m1 m2 : (('a × 'b computation) + ('a computation × 'b)) computation

  Ties go to m1.  There is no implicit cancellation, and no response is
  lost: the loser is returned *suspended*, i.e. with every response to its
  earlier actions already delivered to it, and its next poll still to come.
  Whoever holds the loser makes that poll, whenever they like.

  The responses to the actions a computation emits in round n arrive in
  snapshot n+1, so a value created in round n cannot contain them.  Hence:
   - if m1 wins in round n, m2 is not polled in round n.  The loser is m2
     with snapshot n delivered but not yet polled;
   - if m2 wins in round n, m1 has already been polled in round n.  If that
     poll emitted nothing, the loser is m1 as it is.  Otherwise choose waits
     one more round for the responses and returns m1 with them delivered.
*)
Theory asyncChoose
Ancestors
  pair list rich_list arithmetic option sum asyncCore asyncLevel1
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The rest of a computation
   ------------------------------------------------------------------------ *)

(* resume m p: the rest of m after it has been polled with p (and with every
   prefix of p).  It shows m the history p ++ h, and reports only the actions
   m emits after p. *)
Definition resume_def:
  resume m p h =
    <| actions := DROP (LENGTH (m p).actions) (m (p ++ h)).actions;
       result := (m (p ++ h)).result |>
End

(* suspended m r: the rest of m after it has been polled with every proper
   prefix of r, when the last snapshot of r has been delivered but m has not
   been polled with it yet.  Its first poll is m's poll with r. *)
Definition suspended_def:
  suspended m r =
    if r = [] then m else (λh. resume m (FRONT r) (LAST r :: h))
End

(* ------------------------------------------------------------------------
   choose
   ------------------------------------------------------------------------ *)

(* One of the two sides has finished, on what it has been shown so far *)
Definition either_done_def:
  either_done m1 m2 p ⇔
    (m1 (left_view m1 m2 p)).result ≠ NONE ∨
    (m2 (right_view m1 m2 p)).result ≠ NONE
End

(* The log of m1 and m2 side by side, before the last round of p *)
Definition log_before_def:
  log_before m1 m2 p = if p = [] then [] else par_log m1 m2 (FRONT p)
End

(* choose m1 m2: see the comment at the top of the file.  n is the first
   round in which a side has finished; p the history up to it; l and r what
   the two sides have been shown. *)
Definition choose_def:
  choose m1 m2 h =
    case first_prefix (either_done m1 m2) h of
      NONE => <| actions := par_log m1 m2 h; result := NONE |>
    | SOME n =>
        let p = TAKE n h;
            l = left_view m1 m2 p;
            r = right_view m1 m2 p
        in
          case (m1 l).result of
            SOME x =>
              (* m1 wins; m2 is not polled in this round *)
              <| actions := log_before m1 m2 p ++ new_actions (log_of m1) l;
                 result := SOME (INL (x, suspended m2 r)) |>
          | NONE =>
              (* m2 wins; m1 has been polled in this round *)
              let y = THE (m2 r).result in
              if new_actions (log_of m1) l = [] then
                <| actions := par_log m1 m2 p;
                   result := SOME (INR (resume m1 l, y)) |>
              else if LENGTH h = n then
                (* m1 has requests in flight: wait for their responses *)
                <| actions := par_log m1 m2 p; result := NONE |>
              else
                <| actions := par_log m1 m2 p;
                   result :=
                     SOME (INR (suspended m1 (left_view m1 m2 (TAKE (n + 1) h)),
                                y)) |>
End
