(*
  TRUSTED (for review).  The L0 claims' shared outcomes.

  stdio_closed (design/50 (c2), D33): the program's first three calls,
  sys_fdok on fds 0, 1 and 2 (always all three), found one closed, and the
  program stopped.  Every L0 claim
  allows it as an outcome, alongside its listen failure, instead of
  assuming the fds open (the world assumption no longer has
  MEM 0w/1w/2w w.reserved).

  stdio_open and no_close_stdio (D37, user-approved 2026-10-17; text agreed
  by close-v2, KV and m4-server): a claim's main branch has
  stdio_open (beh_io beh) ∧ ∀evs. LPREFIX (fromList evs) (beh_io beh) ⇒ no_close_stdio evs.
*)
Theory honestL0Outcome
Ancestors
  semantics honestL0World
Libs
  preamble

Definition stdio_closed_def:
  stdio_closed b ⇔
    ∃i0 i1 i2 r0 r1 r2.
      b = Terminate Success [IO_event (ExtCall «sys_fdok») [0w] [(i0, r0)];
                             IO_event (ExtCall «sys_fdok») [1w] [(i1, r1)];
                             IO_event (ExtCall «sys_fdok») [2w] [(i2, r2)]] ∧
      MEM 0w [r0; r1; r2]
End

(* After the stdio check (D33): the program's first three events are
   sys_fdok on 0, 1, 2, each answering 1 (open) *)
Definition stdio_open_def:
  stdio_open io ⇔
    ∃i0 i1 i2 rest.
      io = LAPPEND (fromList [IO_event (ExtCall «sys_fdok») [0w] [(i0, 1w)];
                              IO_event (ExtCall «sys_fdok») [1w] [(i1, 1w)];
                              IO_event (ExtCall «sys_fdok») [2w] [(i2, 1w)]]) rest
End

(* It never closes its stdio fds (any close call on 0, 1 or 2) *)
Definition no_close_stdio_def:
  no_close_stdio evs ⇔
    ∀conf bs. MEM (IO_event (ExtCall «sys_close») conf bs) evs ∧ LENGTH conf = 8 ⇒
              bytes_fd conf ≠ 0w ∧ bytes_fd conf ≠ 1w ∧ bytes_fd conf ≠ 2w
End
