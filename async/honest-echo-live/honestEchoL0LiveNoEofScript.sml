(*
  D26 for the echo, at M4: a connection on the live interest list (other
  than the initial fds) was handed out and none of its reads has returned
  end-of-file.  The converse of asyncM4LiveAcc's live_accepted; it gives
  read_soon_live and read_soon_eof_live their no-end-of-file premise.

  Why it holds: a read is only of a handle handed out before its round
  (echo_round_actions_ok), and handles are handed out once (echo_sinv's
  ALL_DISTINCT), so a handle whose read returned end-of-file is never
  re-added to the live list.

  MAIN: live_noeof.
*)
Theory honestEchoL0LiveNoEof
Ancestors
  honestL1PFOblLive asyncM4LiveAcc asyncM4LiveInterest asyncM4EchoRunOk asyncM4GTrans
  asyncM4GRounds asyncM4SockInv asyncM4Loop asyncM3World
Libs
  preamble

(* A result Accepted (SOME c) comes from an Accept *)
Theorem sock_acts_accepted:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧ MEM (Accepted (SOME c)) rs ⇒
    MEM c (wacc (ZIP (acts, rs)))
Proof
  Induct >> simp[sock_acts_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[wacc_def]
  >- (Cases_on ‘h’ >> gvs[sock_do_def, AllCaseEqs(), OPTION_MAP_EQ_SOME] >>
      rpt (pairarg_tac >> gvs[]))
  >> res_tac >> simp[]
QED

Theorem gres_accepted:
  grun_ok ifds m s0 ∧ MEM (Accepted (SOME c)) (gres ifds m s0 n) ⇒
  MEM c (wacc (ZIP (gacts ifds m s0 n, gres ifds m s0 n)))
Proof
  rw[grun_ok_def] >> first_x_assum (qspec_then ‘n’ assume_tac) >>
  Cases_on ‘sock_acts (gstate ifds m s0 n) (gacts ifds m s0 n)’ >> fs[] >>
  PairCases_on ‘x’ >> fs[gres_def, sock_acts_tot_def] >>
  drule_all sock_acts_accepted >> simp[]
QED

(* A read the echo performed is of a handle handed out *)
Theorem echo_read_wacc:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n c k r. MEM (Read c k, r) (SP lfdn ifds s0 n) ⇒ MEM c (wacc (SP lfdn ifds s0 n))
Proof
  strip_tac >> Induct >- simp[gperf_def] >>
  rpt gen_tac >> simp[gperf_SUC] >> strip_tac >- metis_tac[] >>
  mp_tac echo_sinv >> impl_tac >- fs[] >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule echo_round_actions_ok >> simp[EVERY_MEM] >> disch_then (qspec_then ‘Read c k’ mp_tac) >>
  impl_tac
  >- (‘grun_ok ifds (srelabel (server lfdn)) s0’ by (irule echo_grun_ok >> simp[]) >>
      drule_then (qspec_then ‘n’ assume_tac) LENGTH_gres >>
      gvs[MEM_ZIP] >> metis_tac[EL_MEM]) >>
  simp[action_ok_def]
QED

(* MAIN: a live connection was handed out and has had no end-of-file read *)
Theorem live_noeof:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n c. MEM c (live fds0 (log_of (srelabel (server lfdn)))
                 (ghist ifds (srelabel (server lfdn)) s0 n)) ∧ ¬MEM c fds0 ⇒
        MEM c (wacc (SP lfdn ifds s0 n)) ∧
        ∀k. ¬MEM (Read c k, Got (SOME [])) (SP lfdn ifds s0 n)
Proof
  strip_tac >> ‘grun_ok ifds (srelabel (server lfdn)) s0’ by (irule echo_grun_ok >> simp[]) >>
  Induct >- simp[ghist_def, grounds_def] >>
  rpt gen_tac >> strip_tac >>
  ‘LENGTH (gacts ifds (srelabel (server lfdn)) s0 n) =
   LENGTH (gres ifds (srelabel (server lfdn)) s0 n)’
    by simp[LENGTH_gres] >>
  qpat_x_assum ‘MEM c (live _ _ _)’ mp_tac >>
  simp[live_ghist_SUC, MEM_live_round, MEM_add_accepted] >> strip_tac
  >- (first_x_assum (qspec_then ‘c’ mp_tac) >> simp[gperf_SUC] >> metis_tac[])
  >> drule_all gres_accepted >> strip_tac >>
  simp[gperf_SUC] >> rpt strip_tac >> TRY (metis_tac[]) >>
  (* an earlier end-of-file read: c was handed out twice *)
  mp_tac echo_sinv >> impl_tac >- fs[] >> disch_then (qspec_then ‘SUC n’ strip_assume_tac) >>
  ‘MEM c (wacc (SP lfdn ifds s0 n))’ by metis_tac[echo_read_wacc] >>
  fs[sinv_def, gperf_SUC, ALL_DISTINCT_APPEND] >> metis_tac[]
QED
