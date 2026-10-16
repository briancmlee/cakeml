(*
  THE L0 WORLD'S RELY (trusted; design/36 §4.3): the facts about the real
  C and kernel that every world is assumed to satisfy.  Each is either a
  property of socket_ffi_l0.c or a guarantee of the standards; none is a
  progress assumption (those are per-guarantee antecedents of the specs).

   - the raw errno is 4 bytes (the C writes 4);
   - the kernel accepts at most what it is offered [P send];
   - recv with data available returns at least one byte and at most what
     is there [P recv: "data shall be returned to the user as soon as it
     becomes available"];
   - [A2] a call fails with EAGAIN only where the standard says so (no data,
     no room, no connection pending).  POSIX 2.3 lets an implementation
     return any error "under circumstances other than those described";
     the model lets every other error happen at any time (transient), and
     assumes this one exception, checked by the conformance tests;
   - sys_listen reports a step 1..5 (the C does);
   - the fd limit is at most 2^31 (fds are C ints).
*)
Theory honestL0Rely
Ancestors
  honestL0World
Libs
  preamble

Definition l0_rely_def:
  l0_rely (w : l0world) ⇔
    (∀h. LENGTH (w.ch.errno_of h) = 4) ∧
    (∀j h b n. w.ch.takes j h b n ≤ n) ∧
    (∀j h a. 0 < a ⇒ 0 < w.ch.short j h a ∧ w.ch.short j h a ≤ a) ∧
    (∀h. w.ch.transient h ≠ SOME E_AGAIN) ∧
    (∀h k e. w.ch.listen_fails h = SOME (k, e) ⇒ 1 ≤ k ∧ k ≤ 5) ∧
    w.fd_limit ≤ 2 ** 31
End

(* The rely is about the choices only: time passing, calls and arrivals
   keep it *)
Theorem l0_rely_ch:
  l0_rely w ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit ⇒ l0_rely w'
Proof
  rw[l0_rely_def]
QED
