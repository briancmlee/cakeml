(*
  D26 at the M4 level: the live interest list (asyncM4LiveInterest) holds
  the listener and every connection handed out, until its read returns
  end-of-file.  The live analogue of asyncM4LiveProg's interest_accepted;
  the connections read_soon_s and accept_soon_s poll are of that kind.

  MAIN: live_accepted.
*)
Theory asyncM4LiveAcc
Ancestors
  asyncM4LiveProg asyncM4LiveInterest asyncM4GTrans asyncM4GRounds asyncM4SockInv
  asyncM4Loop asyncM3World
Libs
  preamble

Theorem live_ghist_SUC:
  live fds0 (log_of m) (ghist ifds m s0 (SUC n)) =
  live_round (live fds0 (log_of m) (ghist ifds m s0 n)) (gacts ifds m s0 n) (gres ifds m s0 n)
Proof
  simp[Once ghist_def, grounds_SUC, live_SNOC, ssnap_def, gres_def, gacts_def] >>
  simp[ghist_def]
QED

(* MAIN: in round n, the loop polls the listener and every connection
   handed out so far whose read has not returned end-of-file *)
Theorem live_accepted:
  ∀n c. grun_ok (live fds0 (log_of m)) m s0 ∧
        (MEM c fds0 ∨ MEM c (wacc (gperf (live fds0 (log_of m)) m s0 n))) ∧
        (∀k. ¬MEM (Read c k, Got (SOME [])) (gperf (live fds0 (log_of m)) m s0 n)) ⇒
        MEM c (live fds0 (log_of m) (ghist (live fds0 (log_of m)) m s0 n))
Proof
  Induct
  >- simp[gperf_def, wacc_def, ghist_def, grounds_def]
  >> rpt gen_tac >> strip_tac >> simp[live_ghist_SUC] >>
  qabbrev_tac ‘L = live fds0 (log_of m)’ >>
  ‘LENGTH (gacts L m s0 n) = LENGTH (gres L m s0 n)’ by simp[LENGTH_gres] >>
  simp[MEM_live_round] >> fs[gperf_SUC] >>
  ‘∀k. ¬MEM (Read c k, Got (SOME [])) (gperf L m s0 n)’ by metis_tac[] >>
  rpt strip_tac >> gvs[]
  >- (irule MEM_add_accepted >> first_x_assum irule >> simp[])
  >- (irule MEM_add_accepted >> first_x_assum irule >> simp[])
  >> irule wacc_add_accepted >> qexists_tac ‘gacts L m s0 n’ >> simp[]
QED
