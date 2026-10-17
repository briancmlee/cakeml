(*
  The PF echo drains once L1 fetches nothing: honestL1BEofClose's
  pf_drain_read, with async-spike's echo facts (honest-echo-live: S2, S3w
  and echo_read_soon_eof) for m = srelabel (server k), polled through
  interest [n2w k].

  MAIN: echo_drain.
*)
Theory honestEchoL0BDrain
Ancestors
  honestL1PFLive honestL1PFConnRun honestL1BQuietDrain honestL1BEofClose
  honestEchoL0Obl honestEchoL0EofRead
Libs
  preamble

Theorem echo_drain:
  echo_run lfdn pol w0 ∧ linv (n2w lfdn) w0 ∧
  (∀n. n0 ≤ n ⇒ rlog (n2w lfdn) pol EI ES w0 n = []) ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
       (rstate (n2w lfdn) pol EI ES w0 n).acq = [] ∧
       ∀h f. ALOOKUP (rstate (n2w lfdn) pol EI ES w0 n).b.tbl h = SOME f ⇒
             inb_of (rstate (n2w lfdn) pol EI ES w0 n) f = [] ∧
             ¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof
Proof
  strip_tac >> irule pf_drain_read >>
  drule echo_S2 >> drule echo_S3w >> fs[echo_run_def] >> rpt strip_tac >>
  qexists_tac ‘n0’ >> rw[] >>
  ‘echo_run lfdn pol w0’ by fs[echo_run_def] >>
  drule_all echo_read_soon_eof >> strip_tac >>
  qexistsl [‘i’, ‘kk’] >> ‘i + n = n + i’ by simp[] >> fs[]
QED
