(*
  TRUSTED (for review).  The L0 claims' shared outcomes.

  stdio_closed (design/50 (c2), D33): the program's first three calls,
  sys_fdok on fds 0, 1 and 2 (always all three), found one closed, and the
  program stopped.  Every L0 claim
  allows it as an outcome, alongside its listen failure, instead of
  assuming the fds open (the world assumption no longer has
  MEM 0w/1w/2w w.reserved).
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
