(*
  M4's no-misuse argument and trace bridge, for any server computation
  that uses the socket API correctly in the model (generic form of
  echoRunOk and of the round bridge in echoSafe).

  For a model computation m with  uses_ok lfdn m  (every Accept is on the
  listener lfdn; every Read/Write of a connection comes after its
  Accepted), run by M4's loop as  srelabel m  against a socket world with
  exactly one listener n2w lfdn (nothing pending) and no connections:

   - gen_grun_ok:      no action of the run is a misuse;
   - gen_fresh:        the model transcript hands out distinct connections;
   - gen_rounds_bytes: at round boundary n, the bytes written to c in
                       rounds 0..n and read from c in rounds 0..n-1 are
                       those of the model transcript TSg m ifds s0 n on fd
                       w2n c.

  The proofs are echoRunOk's and echoSafe's, with uses_ok m
  in place of server_uses_accepted.  The echo server is an instance
  (uses_ok_server).
*)
Theory skeletonRunOk
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServerSafety echoServerUses relabel relabelDist
  socketWorld loopPollWorld loopRounds loopSockInv
  echoSockModel loopRoundsTrans echoRunOk echoSafe EchoSpec
Libs
  preamble

(* m uses the socket API correctly, on every history *)
Definition uses_ok_def:
  uses_ok lfd m ⇔
    ∀hh. accepts_on lfd (trans m hh) ∧ ∀fd. acc_first fd (trans m hh)
End

Theorem uses_ok_server:
  uses_ok lfd (server lfd)
Proof
  simp[uses_ok_def, server_uses_accepted]
QED

(* The model transcript of m on the translated history of n rounds, the
   performed pairs, and round n's actions *)
Overload TSg = “λm ifds s0 n. trans m (MAP sfs (ghist ifds (srelabel m) s0 n))”
Overload SPg = “λm ifds s0 n. gperf ifds (srelabel m) s0 n”
Overload SAg = “λm ifds s0 n. gacts ifds (srelabel m) s0 n”

Theorem gen_trans_split:
  gok_upto ifds (srelabel m) s0 n ⇒
  ∃tt1 tt2. TSg m ifds s0 n = tt1 ++ tt2 ∧
          TREL tt1 (MAP (λ(a, r). (a, SOME r)) (SPg m ifds s0 n)) ∧
          TREL tt2 (MAP (λa. (a, NONE)) (SAg m ifds s0 n))
Proof
  strip_tac >>
  qspecl_then [‘sfs’, ‘sfr’, ‘m’, ‘sfa’,
               ‘ghist ifds (srelabel m) s0 n’] mp_tac
    (Q.GENL [‘fs’, ‘fr’, ‘m’, ‘fa’, ‘h’] trans_relabel) >>
  impl_tac >- simp[snap_map_def] >>
  drule trans_ghist_upto >> strip_tac >> simp[] >>
  simp[MAP_EQ_APPEND] >> strip_tac >>
  rename1 ‘_ = l1 ++ l2’ >> qexistsl [‘l1’, ‘l2’] >> simp[]
QED

Theorem acc_first_NONE[local]:
  ∀tt. EVERY (λp. SND p = NONE) tt ∧ EXISTS (on_fd fd) tt ⇒ ¬acc_first fd tt
Proof
  Induct >> simp[acc_first_def] >> rpt strip_tac >>
  gvs[accepts_def] >> metis_tac[]
QED

Theorem gen_round_actions_ok:
  uses_ok lfdn m ∧ gok_upto ifds (srelabel m) s0 n ⇒
  EVERY (action_ok (n2w lfdn) (wacc (SPg m ifds s0 n))) (SAg m ifds s0 n)
Proof
  strip_tac >> drule_all gen_trans_split >> strip_tac >>
  drule TREL_NONE >> strip_tac >>
  gvs[uses_ok_def] >>
  first_x_assum (qspec_then ‘MAP sfs (ghist ifds (srelabel m) s0 n)’
                   strip_assume_tac) >>
  gvs[accepts_on_def] >>
  drule TREL_accepted >> strip_tac >>
  qpat_x_assum ‘_ = SAg _ _ _ _’ (SUBST1_TAC o SYM) >>
  simp[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  rename1 ‘MEM (a0, r0) tt2’ >>
  ‘r0 = NONE’ by (gvs[EVERY_MEM] >> res_tac >> gvs[]) >> gvs[] >>
  Cases_on ‘a0’ >> simp[sfa_def, action_ok_def]
  >~ [‘MEM (Read fd, NONE) tt2’]
  >- (qpat_x_assum ‘∀fd. acc_first fd _’ (qspec_then ‘fd’ mp_tac) >>
      simp[acc_first_APPEND] >> strip_tac >>
      ‘¬acc_first fd tt2’ by (irule acc_first_NONE >> simp[EXISTS_MEM] >>
                             qexists_tac ‘(Read fd, NONE)’ >> simp[]) >>
      gvs[] >> imp_res_tac MEM_accepted >> gvs[MEM_MAP] >>
      simp[bufsz_def])
  >~ [‘MEM (Write fd d, NONE) tt2’]
  >- (qpat_x_assum ‘∀fd. acc_first fd _’ (qspec_then ‘fd’ mp_tac) >>
      simp[acc_first_APPEND] >> strip_tac >>
      ‘¬acc_first fd tt2’ by (irule acc_first_NONE >> simp[EXISTS_MEM] >>
                             qexists_tac ‘(Write fd d, NONE)’ >> simp[]) >>
      gvs[] >> imp_res_tac MEM_accepted >> gvs[MEM_MAP])
  >~ [‘MEM (Accept l, NONE) tt2’]
  >> gvs[EVERY_MEM, is_accept_def] >>
  first_x_assum (qspec_then ‘(Accept l, NONE)’ mp_tac) >> simp[]
QED

(* MAIN (helper): round after round the socket-world invariant holds and
   no round has a misuse *)
Theorem gen_sinv:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n. sinv (n2w lfdn) (wacc (SPg m ifds s0 n)) (gstate ifds (srelabel m) s0 n) ∧
      gok_upto ifds (srelabel m) s0 n
Proof
  strip_tac >> Induct
  >- simp[gperf_def, wacc_def, gstate_def, grounds_def, sinv_init,
          gok_upto_def] >>
  pop_assum strip_assume_tac >>
  drule_all_then strip_assume_tac gen_round_actions_ok >>
  drule_all sock_acts_ok >> strip_tac >>
  ‘gres ifds (srelabel m) s0 n = rs’
    by simp[gres_def, sock_acts_tot_def] >>
  conj_tac
  >- (simp[gperf_SUC, Once gstate_def, grounds_SUC] >>
      simp[GSYM gstate_def, sock_acts_tot_def] >>
      irule sinv_sock_poll >> gvs[])
  >> gvs[gok_upto_def] >> rw[] >>
  Cases_on ‘i = n’ >> gvs[]
QED

(* MAIN: a computation that uses the socket API correctly never misuses it
   when run by the loop: M3's no-misuse hypothesis, for any interest
   function *)
Theorem gen_grun_ok:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grun_ok ifds (srelabel m) s0
Proof
  rw[grun_ok_def] >>
  drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘SUC n’] strip_assume_tac) >>
  gvs[gok_upto_def]
QED

(* MAIN: the world hands the computation distinct connections *)
Theorem gen_fresh:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  fresh (TSg m ifds s0 n)
Proof
  strip_tac >> drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
  simp[fresh_def, accepted_NONE] >>
  irule ALL_DISTINCT_MAP_INJ >> simp[] >>
  gvs[sinv_def, ALL_DISTINCT_APPEND]
QED

Theorem acc_first_accepted[local]:
  ∀tt. acc_first fd tt ∧ EXISTS (on_fd fd) tt ⇒ MEM fd (accepted tt)
Proof
  Induct >> simp[acc_first_def] >> rpt gen_tac >>
  Cases_on ‘accepts fd h’ >> simp[]
  >- (strip_tac >> gvs[accepts_def, accepted_def]) >>
  strip_tac >> gvs[] >> PairCases_on ‘h’ >>
  Cases_on ‘h0’ >> Cases_on ‘h1’ >> simp[] >> TRY CASE_TAC >> simp[]
QED

(* Every fd the model touches was handed out by the world *)
Theorem gen_fds_bounded:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀fd. EXISTS (on_fd fd) (TSg m ifds s0 n) ⇒ fd < dimword(:64)
Proof
  rpt strip_tac >>
  drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  ‘MEM fd (accepted (TSg m ifds s0 n))’
    by (irule acc_first_accepted >> gvs[uses_ok_def]) >>
  drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
  gvs[accepted_NONE, MEM_MAP] >>
  qspec_then ‘y’ mp_tac w2n_lt >> simp[]
QED

(* The socket transcript at round n, in terms of the performed pairs *)
Theorem owritten_rounds[local]:
  grun_ok ifds m s0 ⇒
  FLAT (MAP (owritten c)
         (MAP (λ(a, r). (a, SOME r)) (gperf ifds m s0 n) ++
          MAP (λa. (a, NONE)) (gacts ifds m s0 n))) =
  FLAT (MAP (pwritten c) (gperf ifds m s0 (SUC n)))
Proof
  strip_tac >> simp[gperf_SUC, MAP_MAP_o, combinTheory.o_DEF] >>
  ‘∀ps. MAP (λx. owritten c ((λ(a, r). (a, SOME r)) x)) ps = MAP (pwritten c) ps’
    by (Induct >> simp[FORALL_PROD] >> Cases >> simp[owritten_def, pwritten_def]) >>
  simp[] >>
  ‘∀as rs. LENGTH rs = LENGTH as ⇒
           MAP (λa. owritten c (a, NONE)) as = MAP (pwritten c) (ZIP (as, rs))’
    by (Induct >> simp[] >> Cases_on ‘rs’ >> simp[] >>
        Cases >> simp[owritten_def, pwritten_def]) >>
  AP_TERM_TAC >> first_x_assum irule >> metis_tac[LENGTH_gres]
QED

Theorem oread_rounds[local]:
  FLAT (MAP (oread c)
         (MAP (λ(a, r). (a, SOME r)) ps ++ MAP (λa. (a, NONE)) as)) =
  FLAT (MAP (pread c) ps)
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  ‘∀as. FLAT (MAP (λa. oread c (a, NONE)) as) = []’
    by (Induct >> simp[] >> Cases >> simp[oread_def]) >>
  simp[] >> AP_TERM_TAC >> simp[MAP_EQ_f, FORALL_PROD] >>
  Cases >> simp[oread_def, pread_def] >> Cases >> simp[oread_def, pread_def] >>
  rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[oread_def, pread_def]
QED

(* MAIN: the trace bridge.  At round boundary n, on every connection c,
   the bytes written in rounds 0..n and the bytes read in rounds 0..n-1
   are the bytes of what the model transcript wrote to / read from fd
   w2n c. *)
Theorem gen_rounds_bytes:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  bytes_written_to c
    (FLAT (GENLIST (grounds_events ifds (srelabel m) s0) (SUC n))) =
  bytes (FLAT (written (w2n c) (TSg m ifds s0 n))) ∧
  bytes_read_from c
    (FLAT (GENLIST (grounds_events ifds (srelabel m) s0) n)) =
  bytes (FLAT (read (w2n c) (TSg m ifds s0 n)))
Proof
  strip_tac >> drule_all gen_grun_ok >> disch_then (qspec_then ‘ifds’ assume_tac) >>
  simp[bytes_written_to_rounds, bytes_read_from_rounds] >>
  drule_all gen_sinv >>
  disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  ‘TREL (tt1 ++ tt2)
     (MAP (λ(a, r). (a, SOME r)) (SPg m ifds s0 n) ++
      MAP (λa. (a, NONE)) (SAg m ifds s0 n))’
    by (simp[MAP_APPEND] >> metis_tac[]) >>
  drule_then (qspec_then ‘c’ mp_tac) TREL_written_read >>
  impl_tac >- (qpat_x_assum ‘_ = tt1 ++ tt2’ (SUBST1_TAC o SYM) >>
               metis_tac[gen_fds_bounded]) >>
  simp[owritten_rounds, oread_rounds]
QED
