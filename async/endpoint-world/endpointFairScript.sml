(*
  THE ENDPOINT WORLD'S RELY (trusted; for the user's review): what a
  program may assume of its environment, whatever the program does.

   - ep_sched_ok: in every state the program can reach (by any sequence of
     calls), the environment's next arrivals make sense there (version 2's
     sched_wf2, checked on the actual run, not on the world left alone);
     this includes version 2's bound on the number of channels, so a new
     channel can always get a free fd;
   - takes_ok: the acceptance policy accepts at most what is offered, and
     at least one byte when nothing is in flight;
   - alloc_ok: the kernel gives free fds (version 2).

  No conjunct is a progress assumption, and none depends on whether the
  world has backpressure: the simple worlds satisfy it as they are.
  Progress assumptions (a peer keeps reading, endpointSpecForms'
  reads_fair) are per-guarantee antecedents instead.
*)
Theory endpointFair
Ancestors
  llist endpointWorld socketV2FFI
Libs
  preamble

Definition ep_arrival_ok_def:
  (ep_arrival_ok (w:eworld) (Incoming a) ⇔
     EXISTS (λ(l, a', q). a' = a) w.listening ∧
     LENGTH w.reserved + LENGTH w.listening + LENGTH w.chans + 1 < dimword (:64)) ∧
  (ep_arrival_ok w (PData j bs) ⇔
     j < LENGTH w.chans ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).peer_eof) ∧
  (ep_arrival_ok w (PEof j) ⇔
     j < LENGTH w.chans ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).peer_eof) ∧
  (ep_arrival_ok w (Drain j) ⇔ j < LENGTH w.chans) ∧
  (ep_arrival_ok w (Settle j b) ⇔
     j < LENGTH w.chans ∧ (EL j w.chans).status = Connecting)
End

Definition ep_step_ok_def:
  ep_step_ok w [] = T ∧
  ep_step_ok w (a :: as) = (ep_arrival_ok w a ∧ ep_step_ok (ep_deliver w a) as)
End

(* The world after a sequence of calls; NONE if one of them fails *)
Definition ep_after_def:
  ep_after w [] = SOME w ∧
  ep_after w ((n, conf, bytes) :: cs) =
    case ep_ffi_fn n conf bytes w of
    | SOME (_, w') => ep_after w' cs
    | NONE => NONE
End

(* ASSUMPTION: whatever the program does, the next arrivals make sense *)
Definition ep_sched_ok_def:
  ep_sched_ok w ⇔
    ∀cs w'. ep_after w cs = SOME w' ⇒
            ep_step_ok (w' with clock := w'.clock + 1) (w'.env w'.clock w'.hist)
End

(* ASSUMPTION: the acceptance policy is sane *)
Definition takes_ok_def:
  takes_ok (t : num -> num -> num -> num) ⇔
    ∀j b n. t j b n ≤ n ∧ (b = 0 ∧ 0 < n ⇒ 0 < t j 0 n)
End

Definition ep_rely_def:
  ep_rely (w:eworld) ⇔ alloc_ok w.alloc ∧ takes_ok w.takes ∧ ep_sched_ok w
End
