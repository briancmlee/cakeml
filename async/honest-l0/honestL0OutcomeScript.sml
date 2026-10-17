(*
  TRUSTED (for review).  The L0 claims' shared outcomes.

  stdio_closed (design/50 (c2)): the program's first call, sys_stdio,
  found fd 0, 1 or 2 closed, and the program stopped.  Every L0 claim
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
    ∃bs. b = Terminate Success [IO_event (ExtCall «sys_stdio») [] bs] ∧ MEM 0w (MAP SND bs)
End
