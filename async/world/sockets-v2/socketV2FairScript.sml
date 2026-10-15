(*
  The fairness assumption on version-2 schedules, as in version 1
  (ffiSpikeSocketFair): every arrival of the schedule makes sense when it
  arrives, so that no arrival is silently dropped.

  One bound is added: fewer than 2^64 clients in all, counting the fds the
  process otherwise uses and the listeners.  It guarantees that an accept
  always finds a free fd (open connections are at most the clients).
  Version 1 has the same bound implicitly (every connection there takes a
  fresh 64-bit fd for good).
*)
Theory socketV2Fair
Ancestors
  llist alist ffiSpikeSocketFFI socketV2FFI
Libs
  preamble

(* An arrival is effective in state s: deliver2 does not drop it. *)
Definition arrival_ok2_def:
  (arrival_ok2 s (Connect2 l) ⇔
     ALOOKUP s.listening l ≠ NONE ∧
     LENGTH s.reserved + LENGTH s.listening + LENGTH s.clients + 1 < dimword (:64)) ∧
  (arrival_ok2 s (Data2 j bs) ⇔
     j < LENGTH s.clients ∧ ¬(EL j s.clients).peer_closed) ∧
  (arrival_ok2 s (Eof2 j) ⇔
     j < LENGTH s.clients ∧ ¬(EL j s.clients).peer_closed)
End

(* Every arrival of a step is effective when it is delivered. *)
Definition step_ok2_def:
  step_ok2 s [] = T ∧
  step_ok2 s (a::as) = (arrival_ok2 s a ∧ step_ok2 (deliver2 s a) as)
End

(* The world left alone for n rounds. *)
Definition ticks2_def:
  ticks2 0 s = s ∧
  ticks2 (SUC n) s = ticks2 n (tick2 s)
End

Definition next_step2_def:
  next_step2 s = case LHD s.future of NONE => [] | SOME as => as
End

(* ASSUMPTION sched_wf2: left alone, the world never drops an arrival. *)
Definition sched_wf2_def:
  sched_wf2 s ⇔ ∀n. step_ok2 (ticks2 n s) (next_step2 (ticks2 n s))
End
