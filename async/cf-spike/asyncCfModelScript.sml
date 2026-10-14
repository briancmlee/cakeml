(*
  A minimal HOL "history model" of polled asynchronous computations,
  used by the CF feasibility spike (see async/design/02-cf-feasibility.md).

  A computation is observed by polling it with snapshots of the world.
  Its meaning is a function from the history of snapshots it has been
  polled with (oldest first) to its status after that history:
  SOME x if it has finished with result x, NONE if it is still waiting.

  Only results are modelled here: no actions, no responses, no both/choose.
  The world snapshot type 'w is abstract.
*)
Theory asyncCfModel
Ancestors
  list option

(* ------------------------------------------------------------------------
   The model
   ------------------------------------------------------------------------ *)

(* A computation: status after each history of snapshots (oldest first). *)
Type comp = “:'w list -> 'a option”

(* m has finished with result x: it reports x whatever it is polled with. *)
Definition finished_def:
  finished (m : ('w,'a) comp) x ⇔ ∀h. m h = SOME x
End

(* The computation m as seen after one more poll with snapshot w. *)
Definition after_def:
  after w (m : ('w,'a) comp) = λh. m (w :: h)
End

(* return x: finished with x from the start. *)
Definition mret_def:
  mret x : ('w,'a) comp = λh. SOME x
End

(* wait f: finishes with a at the first polled snapshot w with f w = SOME a.
   It is pending before the first poll, even if f would accept the
   current world: a computation only sees snapshots it is polled with. *)
Definition mwait_def:
  (mwait f [] = NONE) ∧
  (mwait f (w :: h) = case f w of SOME a => SOME a | NONE => mwait f h)
End

(* bind m g: run m; once m has finished with x (as soon as a poll makes it
   finish), continue as g x on the rest of the history.  If m is finished
   before any poll, bind m g behaves as g x from the start. *)
Definition mbind_def:
  (mbind m g [] = case m [] of SOME x => g x [] | NONE => NONE) ∧
  (mbind m g (w :: h) =
     case m [] of SOME x => g x (w :: h) | NONE => mbind (after w m) g h)
End

(* ------------------------------------------------------------------------
   Lemmas used by the CF proofs: one per implementation step
   ------------------------------------------------------------------------ *)

Theorem finished_mret:
  finished (mret x) x
Proof
  simp[finished_def, mret_def]
QED

Theorem finished_after:
  finished m x ⇒ finished (after w m) x
Proof
  simp[finished_def, after_def]
QED

Theorem mwait_NIL:
  mwait f [] = NONE
Proof
  simp[mwait_def]
QED

(* Polling wait f with a snapshot it rejects leaves wait f unchanged. *)
Theorem after_mwait_NONE:
  f w = NONE ⇒ after w (mwait f) = mwait f
Proof
  simp[after_def, mwait_def, FUN_EQ_THM]
QED

(* Polling wait f with a snapshot it accepts finishes it. *)
Theorem after_mwait_SOME:
  f w = SOME a ⇒ finished (after w (mwait f)) a
Proof
  simp[finished_def, after_def, mwait_def]
QED

(* Binding a finished computation is just the continuation. *)
Theorem mbind_finished:
  finished m x ⇒ mbind m g = g x
Proof
  rw[finished_def, FUN_EQ_THM] >> Cases_on ‘x'’ >> simp[mbind_def]
QED

Theorem mbind_NIL_pending:
  m [] = NONE ⇒ mbind m g [] = NONE
Proof
  simp[mbind_def]
QED

(* Polling a bind whose first part is pending polls the first part. *)
Theorem after_mbind_pending:
  m [] = NONE ⇒ after w (mbind m g) = mbind (after w m) g
Proof
  simp[after_def, mbind_def, FUN_EQ_THM]
QED
