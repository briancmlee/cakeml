(*
  The echo server, run against the socket world, never misuses the
  socket API, and the world hands it distinct connections (shared by
  echo_safe and echo_live).

  The computation run by the loop is  srelabel (server lfdn)  (the
  model's server, in the socket vocabulary; asyncM4SockModel).  For any
  interest function ifds and any initial world with exactly one listener
  n2w lfdn (nothing pending) and no connections:

   - echo_grun_ok: no action of the run is a misuse (M3's no-misuse
     hypothesis, discharged);
   - echo_fresh: the model server's transcript on the (translated) history
     hands out distinct connections, so echo_server_safety applies;
   - echo_trans_split: the model transcript, split into the rounds whose
     responses have arrived and the current round, matching the
     performed pairs (gperf) and round n's actions.

  The proof is an induction on rounds with the socket-world invariant
  sinv (asyncM4SockInv): the model's server_uses_accepted
  (asyncM4ServerUses) says every action is allowed by the fds handed out
  so far, and sock_acts_ok says allowed actions succeed.
*)
Theory asyncM4EchoRunOk
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncM4Relabel asyncM4RelabelDist
  ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4SockInv
  asyncM4SockModel asyncM4GTrans
Libs
  preamble

(* ------------------------------------------------------------------------
   Transcripts related by the relabelling, pair by pair
   ------------------------------------------------------------------------ *)

(* The pairs of the model transcript tt and of the socket transcript U
   correspond: same position, action translated by sfa, response read back
   with sfr. *)
Overload TREL = “λtt U. MAP (λ(a, r). (sfa a, r)) tt =
                       MAP (λ(a, r). (a, OPTION_MAP sfr r)) U”

Theorem TREL_APPEND:
  TREL tt (U1 ++ U2) ⇔ ∃tt1 tt2. tt = tt1 ++ tt2 ∧ TREL tt1 U1 ∧ TREL tt2 U2
Proof
  simp[MAP_EQ_APPEND] >> metis_tac[]
QED

Theorem TREL_CONS[local]:
  TREL ((a0, r0) :: tt) ((a, ro) :: U) ⇔
    sfa a0 = a ∧ r0 = OPTION_MAP sfr ro ∧ TREL tt U
Proof
  simp[] >> metis_tac[]
QED

Theorem TREL_LENGTH[local]:
  TREL tt U ⇒ LENGTH tt = LENGTH U
Proof
  metis_tac[LENGTH_MAP]
QED

(* The connections handed out, in both vocabularies *)
Theorem TREL_accepted:
  ∀tt ps. TREL tt (MAP (λ(a, r). (a, SOME r)) ps) ⇒
         accepted tt = MAP w2n (wacc ps)
Proof
  Induct
  >- (gen_tac >> Cases_on ‘ps’ >> simp[wacc_def]) >>
  rpt gen_tac >> Cases_on ‘ps’ >> simp[] >>
  PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on ‘h0’ >> gvs[sfa_def, wacc_def] >>
  Cases_on ‘h'1’ >> gvs[sfr_def, wacc_def] >>
  TRY (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> gvs[sfr_def, wacc_def]) >>
  TRY (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> gvs[sfr_def, wacc_def] >>
       rw[]) >>
  simp[accepted_def]
QED

Theorem TREL_NONE:
  ∀tt acts. TREL tt (MAP (λa. (a, NONE)) acts) ⇒
           EVERY (λp. SND p = NONE) tt ∧ MAP (sfa o FST) tt = acts
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘acts’ >> simp[] >>
  PairCases_on ‘h’ >> simp[] >> metis_tac[]
QED

Theorem accepted_NONE:
  ∀tt. EVERY (λp. SND p = NONE) tt ⇒ accepted tt = []
Proof
  Induct >> simp[] >> Cases >> Cases_on ‘q’ >> simp[]
QED

Theorem acc_first_NONE[local]:
  ∀tt. EVERY (λp. SND p = NONE) tt ∧ EXISTS (on_fd fd) tt ⇒ ¬acc_first fd tt
Proof
  Induct >> simp[acc_first_def] >> rpt strip_tac >>
  gvs[accepts_def] >> metis_tac[]
QED

Theorem MEM_accepted:
  ∀tt. EXISTS (accepts fd) tt ⇒ MEM fd (accepted tt)
Proof
  Induct >> simp[] >> rw[accepts_def] >> gvs[accepted_def]
QED

(* ------------------------------------------------------------------------
   The model transcript of the server, split at round n
   ------------------------------------------------------------------------ *)

Overload TS = “λlfdn ifds s0 n.
  trans (server lfdn)
    (MAP sfs (ghist ifds (srelabel (server lfdn)) s0 n))”

Overload SP = “λlfdn ifds s0 n.
  gperf ifds (srelabel (server lfdn)) s0 n”

Overload SA = “λlfdn ifds s0 n.
  gacts ifds (srelabel (server lfdn)) s0 n”

(* MAIN: if the first n rounds had no misuse, the model server's
   transcript is a part that matches the performed pairs of the first n
   rounds, then a part that matches round n's actions (no responses
   yet). *)
Theorem echo_trans_split:
  gok_upto ifds (srelabel (server lfdn)) s0 n ⇒
  ∃tt1 tt2. TS lfdn ifds s0 n = tt1 ++ tt2 ∧
          TREL tt1 (MAP (λ(a, r). (a, SOME r)) (SP lfdn ifds s0 n)) ∧
          TREL tt2 (MAP (λa. (a, NONE)) (SA lfdn ifds s0 n))
Proof
  strip_tac >>
  qspecl_then [‘sfs’, ‘sfr’, ‘server lfdn’, ‘sfa’,
               ‘ghist ifds (srelabel (server lfdn)) s0 n’] mp_tac
    (Q.GENL [‘fs’, ‘fr’, ‘m’, ‘fa’, ‘h’] trans_relabel) >>
  impl_tac >- simp[snap_map_def] >>
  drule trans_ghist_upto >> strip_tac >> simp[] >>
  simp[MAP_EQ_APPEND] >> strip_tac >>
  rename1 ‘_ = l1 ++ l2’ >> qexistsl [‘l1’, ‘l2’] >> simp[]
QED

(* The actions of round n are allowed by the fds handed out before it *)
Theorem echo_round_actions_ok:
  gok_upto ifds (srelabel (server lfdn)) s0 n ⇒
  EVERY (action_ok (n2w lfdn) (wacc (SP lfdn ifds s0 n))) (SA lfdn ifds s0 n)
Proof
  strip_tac >> drule echo_trans_split >> strip_tac >>
  drule TREL_NONE >> strip_tac >>
  qspec_then ‘MAP sfs (ghist ifds (srelabel (server lfdn)) s0 n)’
    strip_assume_tac (Q.INST [‘lfd’ |-> ‘lfdn’] server_uses_accepted) >>
  gvs[accepts_on_def] >>
  drule TREL_accepted >> strip_tac >>
  qpat_x_assum ‘_ = SA _ _ _ _’ (SUBST1_TAC o SYM) >>
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

(* ------------------------------------------------------------------------
   No misuse, by induction on rounds
   ------------------------------------------------------------------------ *)

(* MAIN: in a world with one listener n2w lfdn (nothing pending) and no
   connections, round after round the socket-world invariant holds (with
   the connections handed out so far) and no round has a misuse *)
Theorem echo_sinv:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n. sinv (n2w lfdn) (wacc (SP lfdn ifds s0 n))
           (gstate ifds (srelabel (server lfdn)) s0 n) ∧
      gok_upto ifds (srelabel (server lfdn)) s0 n
Proof
  strip_tac >> Induct
  >- simp[gperf_def, wacc_def, gstate_def, grounds_def, sinv_init,
          gok_upto_def] >>
  pop_assum strip_assume_tac >>
  drule_then strip_assume_tac echo_round_actions_ok >>
  drule_all sock_acts_ok >> strip_tac >>
  ‘gres ifds (srelabel (server lfdn)) s0 n = rs’
    by simp[gres_def, sock_acts_tot_def] >>
  conj_tac
  >- (simp[gperf_SUC, Once gstate_def, grounds_SUC] >>
      simp[GSYM gstate_def, sock_acts_tot_def] >>
      irule sinv_sock_poll >> gvs[])
  >> gvs[gok_upto_def] >> rw[] >>
  Cases_on ‘i = n’ >> gvs[]
QED

(* MAIN: the echo server, run by the loop against the socket world, never
   misuses the socket API: M3's no-misuse hypothesis, discharged for any
   interest function *)
Theorem echo_grun_ok:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  grun_ok ifds (srelabel (server lfdn)) s0
Proof
  rw[grun_ok_def] >>
  mp_tac echo_sinv >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘SUC n’ strip_assume_tac) >>
  gvs[gok_upto_def]
QED

(* MAIN: the world hands the server distinct connections *)
Theorem echo_fresh:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  fresh (TS lfdn ifds s0 n)
Proof
  strip_tac >> mp_tac echo_sinv >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule echo_trans_split >> strip_tac >>
  drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
  simp[fresh_def, accepted_NONE] >>
  irule ALL_DISTINCT_MAP_INJ >> simp[] >>
  gvs[sinv_def, ALL_DISTINCT_APPEND]
QED
