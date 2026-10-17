(*
  The proxy (moonshotProxy, step 9) is a fold program in the generic E1
  driver's sense (e1Fold): its computation is the fold of its step from its
  initial state, its actions are each state's last round, and it never
  finishes.
*)
Theory proxyFold
Ancestors
  moonshotProxy e1Fold
Libs
  preamble

Theorem pprog_fold:
  pprog lfd b hw = fold_prog (pinit lfd b hw) (pstep lfd b hw) (λst. MAP SND st.last) (K F)
Proof
  simp[FUN_EQ_THM, pprog_def, fold_prog_def, pstate_def]
QED
