(*
  The echo server's run becomes stable after the last arrival (option C,
  design/33 §2.5 (e); Q1).

  Once the measure (echoMeasure) is 0, nothing can make the server
  act (server_cause, echoServerCause):
  - the listener is not ready: no connection is pending, and no
    connection has the listener's fd (conns_no_listener);
  - a ready connection is one whose EOF the server has read, and for such
    a connection the server's transcript has as many EOFs as accepts
    (eofr_eofs, accs_le_one), so its handler has finished;
  - no read returns data: every connection the server still serves has
    nothing unread.
  And nothing the server declares interest in (server2, Level 2) is ready
  (server_live, echoBlockingWaits).

  MAIN: echo_stable.
*)
Theory echoStable
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServerSafety echoServer2 socketWorld socketFair
  loopPollWorld loopRounds loopRoundsTrans loopSockInv relabel
  relabelDist echoSockModel loopPollDyn echoRunOk
  echoServerUses echoLiveSched echoLiveQueue echoLiveProg echoLiveWorld
  echoLiveReadSoon echoBlockingWaits echoServerCause quietRounds
  echoMeasure QuietSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   The world
   ------------------------------------------------------------------------ *)

Theorem deliver1_no_listener[local]:
  is_listener s l ∧ ALOOKUP s.conns l = NONE ⇒
  is_listener (deliver1 s a) l ∧ ALOOKUP (deliver1 s a).conns l = NONE
Proof
  Cases_on ‘a’ >>
  rw[deliver1_def, is_listener_def, is_conn_def, AFUPDKEY_ALOOKUP] >>
  gvs[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on ‘ALOOKUP s.listeners l’ >> gvs[] >> rw[]
QED

Theorem FOLDL_deliver1_no_listener[local]:
  ∀as s. is_listener s l ∧ ALOOKUP s.conns l = NONE ⇒
         is_listener (FOLDL deliver1 s as) l ∧
         ALOOKUP (FOLDL deliver1 s as).conns l = NONE
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> metis_tac[deliver1_no_listener]
QED

Theorem tick_no_listener[local]:
  is_listener s l ∧ ALOOKUP s.conns l = NONE ⇒
  ALOOKUP (tick s).conns l = NONE
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def] >>
  qmatch_goalsub_abbrev_tac ‘FOLDL deliver1 s1 as’ >>
  qspecl_then [‘as’, ‘s1’] mp_tac FOLDL_deliver1_no_listener >>
  simp[Abbr ‘s1’] >> gvs[is_listener_def]
QED

(* No connection ever has the listener's fd *)
Theorem conns_no_listener:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns (n2w lfdn) = NONE
Proof
  strip_tac >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  Induct >- simp[gstate_def, grounds_def] >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gmid (EI lfdn) (EM lfdn) s0 n = s'’ by simp[gmid_def, sock_acts_tot_def] >>
  simp[gstate_SUC] >> irule tick_no_listener >>
  drule sock_acts_counts >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  simp[] >>
  qspecl_then [‘s0’, ‘n2w lfdn’, ‘EI lfdn’, ‘EM lfdn’] mp_tac
    (Q.GENL [‘s0’, ‘lfd’, ‘ifds’, ‘m’] grounds_known) >>
  simp[] >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule sock_acts_keys >> strip_tac >>
  gvs[is_listener_def, ALOOKUP_NONE]
QED

(* A static round's end has no connection its start did not have *)
Theorem conns_back:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ static_from lfdn s0 N ⇒
  ∀d. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 N).conns c = NONE ⇒
      ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 (N + d)).conns c = NONE
Proof
  strip_tac >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  Induct >> simp[] >> strip_tac >> gvs[] >>
  ‘N + SUC d = SUC (N + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘next_step (gstate (EI lfdn) (EM lfdn) s0 (N + d)) = []’ by simp[] >>
  drule_all static_round >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  res_tac
QED

(* ------------------------------------------------------------------------
   The transcript
   ------------------------------------------------------------------------ *)

Theorem acc_first_on_fd[local]:
  ∀tt. acc_first fd tt ∧ EXISTS (on_fd fd) tt ⇒ EXISTS (accepts fd) tt
Proof
  Induct >> simp[acc_first_def] >> rw[] >> gvs[]
QED

(* The server reads only fds it accepted, which are fds of the world *)
Theorem TS_read_fd:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM (Read fd, r) (TS lfdn (EI lfdn) s0 n) ⇒
  ∃c. fd = w2n c ∧ MEM c (wacc (SP lfdn (EI lfdn) s0 n))
Proof
  strip_tac >>
  ‘MEM fd (accepted (TS lfdn (EI lfdn) s0 n))’
    by (irule MEM_accepted >> irule acc_first_on_fd >>
        simp[server_uses_accepted, EXISTS_MEM] >>
        qexists_tac ‘(Read fd, r)’ >> simp[on_fd_def]) >>
  drule_all accepted_TS >> disch_then (qspec_then ‘n’ mp_tac) >> strip_tac >>
  gvs[MEM_MAP] >> metis_tac[]
QED

(* An EOF the server read in the world is one in its transcript *)
Theorem eofr_eofs:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ eofr lfdn s0 c n ⇒
  1 ≤ eofs (w2n c) (TS lfdn (EI lfdn) s0 n)
Proof
  rw[eofr_def] >> mp_tac (Q.INST [‘ifds’ |-> ‘EI lfdn’] echo_sinv) >> impl_tac >- simp[] >>
  disch_then (qspecl_then [‘n’] strip_assume_tac) >>
  drule echo_trans_split >> strip_tac >>
  ‘MEM (Read c k, SOME Eof) (MAP (λ(a, r). (sfa a, r)) tt1)’
    by (ASM_REWRITE_TAC[] >> simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘SOME (Got (SOME []))’ >>
        simp[sfr_def]) >>
  qpat_x_assum ‘MEM _ (MAP _ tt1)’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_MAP, EXISTS_PROD]) >>
  rename1 ‘MEM (a, SOME Eof) tt1’ >> Cases_on ‘a’ >> fs[sfa_def] >>
  rename1 ‘MEM (Read fd, SOME Eof) tt1’ >>
  ‘MEM (Read fd, SOME Eof) (TS lfdn (EI lfdn) s0 n)’ by ASM_REWRITE_TAC[MEM_APPEND] >>
  drule_all TS_read_fd >> strip_tac >> gvs[] >>
  ‘w2n c MOD dimword (:64) = w2n c’ by simp[w2n_lt] >> fs[] >>
  ‘MEM (Read (w2n c), SOME Eof) (FILTER (is_eof (w2n c)) tt1)’
    by simp[MEM_FILTER, is_eof_def] >>
  ‘1 ≤ eofs (w2n c) tt1’ suffices_by simp[] >>
  simp[eofs_def] >> Cases_on ‘FILTER (is_eof (w2n c)) tt1’ >> gvs[]
QED

Theorem accs_accepted[local]:
  ∀tt. accs fd tt = LENGTH (FILTER ($= fd) (accepted tt))
Proof
  Induct >- simp[accs_def] >> rpt gen_tac >> PairCases_on ‘h’ >>
  Cases_on ‘h1’ >> TRY (rename1 ‘SOME x’ >> Cases_on ‘x’) >>
  Cases_on ‘h0’ >> simp[is_acc_def, FILTER_APPEND] >> IF_CASES_TAC >> gvs[]
QED

(* The server accepts each fd at most once (no reuse in this world) *)
Theorem accs_le_one:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  accs fd (TS lfdn (EI lfdn) s0 n) ≤ 1
Proof
  strip_tac >> drule_all echo_fresh >>
  disch_then (qspecl_then [‘n’, ‘EI lfdn’] mp_tac) >> rw[fresh_def] >>
  simp[accs_accepted] >>
  Cases_on ‘MEM fd (accepted (TS lfdn (EI lfdn) s0 n))’
  >- (gvs[ALL_DISTINCT_FILTER] >> res_tac >> simp[])
  >> ‘FILTER ($= fd) (accepted (TS lfdn (EI lfdn) s0 n)) = []’
       by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   One round's snapshot and actions
   ------------------------------------------------------------------------ *)

Theorem ghist_SUC_snap:
  ghist ifds m s0 (SUC n) =
  ghist ifds m s0 n ++
    [ssnap (FILTER (is_ready (gstate ifds m s0 (SUC n))) (ifds (ghist ifds m s0 n)))
           (gres ifds m s0 n)]
Proof
  simp[Once ghist_def, grounds_SUC, gstate_SUC, gmid_def, gres_def, sock_poll_def]
QED

(* A response Got comes from a read *)
Theorem sock_acts_got[local]:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧ MEM (a, Got x) (ZIP (acts, rs)) ⇒
    ∃c k. a = Read c k
Proof
  Induct >> simp[sock_acts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()]
  >- (Cases_on ‘a’ >> gvs[sock_do_def, AllCaseEqs()] >> TRY (Cases_on ‘z’) >> gvs[]) >>
  metis_tac[]
QED

Theorem rdbytes_MEM[local]:
  ∀ps. MEM (Read c k, Got (SOME bs)) ps ⇒ LENGTH bs ≤ rdbytes c ps
Proof
  Induct >> simp[] >> rpt strip_tac >> ONCE_REWRITE_TAC[counts_CONS] >> gvs[]
  >- simp[rdbytes_def]
  >> res_tac >> simp[]
QED

Theorem MEM_ZIP_SND[local]:
  ∀xs ys. LENGTH xs = LENGTH ys ∧ MEM y ys ⇒ ∃x. MEM (x, y) (ZIP (xs, ys))
Proof
  Induct >> simp[] >> Cases_on ‘ys’ >> simp[] >> rw[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   When the measure is 0
   ------------------------------------------------------------------------ *)

Overload ksN = “λlfdn s0 N. MAP FST (gstate (EI lfdn) (EM lfdn) s0 N).conns”

(* A connection whose EOF the server has not read has nothing left *)
Theorem zero_conn:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ static_from lfdn s0 N ∧
  N ≤ n ∧ meas lfdn s0 (ksN lfdn s0 N) n = 0 ∧
  ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c = SOME cn ∧
  ¬eofr lfdn s0 c n ⇒
  cn.incoming = [] ∧ ¬cn.peer_closed
Proof
  strip_tac >>
  ‘MEM c (ksN lfdn s0 N)’
    by (CCONTR_TAC >>
        ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 N).conns c = NONE’
          by simp[ALOOKUP_NONE] >>
        drule_all conns_back >> disch_then (qspec_then ‘n − N’ mp_tac) >> simp[]) >>
  gvs[meas_def, SUM_eq_0, MEM_MAP, PULL_EXISTS] >>
  first_x_assum drule >> simp[cterm_def, cm_def] >> rw[] >> gvs[]
QED

(* A ready fd is a connection whose EOF the server has read *)
Theorem zero_ready:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ static_from lfdn s0 N ∧
  N ≤ n ∧ meas lfdn s0 (ksN lfdn s0 N) n = 0 ∧
  is_ready (gstate (EI lfdn) (EM lfdn) s0 n) c ⇒
  c ≠ n2w lfdn ∧ eofr lfdn s0 c n
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  ‘MEM c (MAP FST (gstate (EI lfdn) (EM lfdn) s0 n).listeners) ⇒ c = n2w lfdn’
    by (qspecl_then [‘s0’, ‘n2w lfdn’, ‘EI lfdn’, ‘EM lfdn’] mp_tac
          (Q.GENL [‘s0’, ‘lfd’, ‘ifds’, ‘m’] grounds_known) >>
        impl_tac >- simp[] >>
        disch_then (qspec_then ‘n’ (fn th => REWRITE_TAC[CONJUNCT1 th])) >>
        simp[]) >>
  ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns (n2w lfdn) = NONE’
    by metis_tac[conns_no_listener] >>
  qpat_x_assum ‘is_ready _ _’ mp_tac >> simp[is_ready_def] >>
  Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).listeners c’ >> simp[]
  (* a connection *)
  >- (Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c’ >> simp[] >>
      strip_tac >> conj_tac >- (strip_tac >> gvs[]) >>
      CCONTR_TAC >> drule_all zero_conn >> gvs[]) >>
  (* a listener: it is lfdn, and the queue is empty *)
  rename1 ‘SOME q’ >> strip_tac >>
  ‘c = n2w lfdn’
    by (first_x_assum irule >> drule ALOOKUP_MEM >> strip_tac >>
        simp[MEM_MAP] >> qexists_tac ‘(c, q)’ >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum ‘meas _ _ _ _ = 0’ mp_tac >> simp[meas_def, qlen_def, lq_def] >>
  Cases_on ‘q’ >> gvs[]
QED

(* For such a connection, the server's handler has finished *)
Theorem eofr_not_live:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ eofr lfdn s0 c n ⇒
  ¬(eofs (w2n c) (TS lfdn (EI lfdn) s0 n) < accs (w2n c) (TS lfdn (EI lfdn) s0 n))
Proof
  strip_tac >> drule_all eofr_eofs >>
  qspecl_then [‘w2n c’, ‘s0’, ‘lfdn’, ‘n’] mp_tac
    (Q.GENL [‘fd’, ‘s0’, ‘lfdn’, ‘n’] accs_le_one) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Stability
   ------------------------------------------------------------------------ *)

(* MAIN: with the measure 0 at m and m + 1, round m + 1 has no actions *)
Theorem zero_no_actions:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  static_from lfdn s0 N ∧ N ≤ m ∧
  meas lfdn s0 (ksN lfdn s0 N) m = 0 ∧ meas lfdn s0 (ksN lfdn s0 N) (SUC m) = 0 ⇒
  SA lfdn (EI lfdn) s0 (SUC m) = []
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  simp[gacts_def, new_actions_relabel, ghist_SUC_snap, new_actions_SNOC, log_of_def] >>
  qmatch_goalsub_abbrev_tac ‘server lfdn (q ++ [s])’ >>
  ‘(server lfdn (q ++ [s])).actions = (server lfdn q).actions’
    suffices_by simp[DROP_LENGTH_NIL] >>
  CCONTR_TAC >> drule server_cause >> qunabbrev_tac ‘s’ >> strip_tac
  (* the listener is not ready *)
  >- (qpat_x_assum ‘Readable lfdn ∈ _’
        (strip_assume_tac o
         SIMP_RULE (srw_ss()) [snap_map_def, ssnap_def, sfe_def, MEM_FILTER]) >>
      ‘x = n2w lfdn’ by (qpat_x_assum ‘lfdn = w2n x’ SUBST1_TAC >> simp[]) >>
      qpat_x_assum ‘is_ready _ x’ mp_tac >> qpat_x_assum ‘x = _’ SUBST1_TAC >>
      strip_tac >> ‘N ≤ SUC m’ by simp[] >> drule_all zero_ready >> simp[])
  (* a ready connection has a finished handler *)
  >- (qpat_x_assum ‘Readable fd ∈ _’
        (strip_assume_tac o
         SIMP_RULE (srw_ss()) [snap_map_def, ssnap_def, sfe_def, MEM_FILTER]) >>
      rename1 ‘is_ready _ c’ >>
      ‘N ≤ SUC m’ by simp[] >> drule_all zero_ready >> strip_tac >>
      ‘eofr lfdn s0 c m’
        by (gvs[eofr_SUC] >> CCONTR_TAC >>
            drule grun_ok_sock_acts >> disch_then (qspec_then ‘m’ strip_assume_tac) >>
            ‘∃cn. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 m).conns c = SOME cn’
              by (Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 m).conns c’ >> simp[] >>
                  drule_all sock_acts_eof >> strip_tac >>
                  drule sock_acts_counts >> strip_tac >> res_tac >> gvs[]) >>
            drule_all sock_acts_conn >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
            drule_all zero_conn >> gvs[]) >>
      drule_all eofr_not_live >> gvs[Abbr ‘q’])
  (* no read returns data *)
  >> qpat_x_assum ‘MEM _ (snap_map _ _ _).results’
       (strip_assume_tac o
        SIMP_RULE (srw_ss()) [snap_map_def, ssnap_def, MEM_MAP]) >>
  rename1 ‘MEM r (gres _ _ _ m)’ >>
  ‘∃bs. r = Got (SOME bs) ∧ bs ≠ []’
    by (Cases_on ‘r’ >> gvs[sfr_def] >> Cases_on ‘o'’ >> gvs[sfr_def] >>
        qpat_x_assum ‘_ = if _ then _ else _’ mp_tac >> rw[]) >>
  gvs[] >>
  ‘∃a. MEM (a, Got (SOME bs)) (ZIP (SA lfdn (EI lfdn) s0 m, gres (EI lfdn) (EM lfdn) s0 m))’
    by (irule MEM_ZIP_SND >> simp[LENGTH_gres]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘m’ strip_assume_tac) >>
  drule_all sock_acts_got >> strip_tac >> gvs[] >>
  drule rdbytes_MEM >> strip_tac >>
  ‘next_step (gstate (EI lfdn) (EM lfdn) s0 m) = []’ by simp[] >>
  drule_all static_round >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 m).conns c’
  >- (res_tac >> Cases_on ‘bs’ >> gvs[]) >>
  rename1 ‘SOME cn’ >> first_x_assum drule >> strip_tac >>
  Cases_on ‘eofr lfdn s0 c m’
  >- (gvs[eofr_def] >>
      drule grounds_eof >> disch_then drule >> strip_tac >> gvs[] >>
      Cases_on ‘bs’ >> gvs[])
  >> drule_all zero_conn >> strip_tac >> Cases_on ‘bs’ >> gvs[]
QED

(* MAIN: nothing the server declares interest in is ready *)
Theorem zero_interest:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  static_from lfdn s0 N ∧ N ≤ n ∧ meas lfdn s0 (ksN lfdn s0 N) n = 0 ∧
  Readable x ∈ (server2 lfdn).interest (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 n)) ⇒
  ¬is_ready (gstate (EI lfdn) (EM lfdn) s0 n) (n2w x)
Proof
  rpt strip_tac >> drule_all zero_ready >> strip_tac >>
  qspecl_then [‘lfdn’, ‘MAP sfs (ghist (EI lfdn) (EM lfdn) s0 n)’] mp_tac
    (Q.GEN ‘lfd’ server_live) >>
  disch_then (drule o CONJUNCT2) >> strip_tac >> gvs[] >>
  ‘MEM x (accepted (TS lfdn (EI lfdn) s0 n))’
    by (CCONTR_TAC >>
        ‘FILTER ($= x) (accepted (TS lfdn (EI lfdn) s0 n)) = []’
          by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
        gvs[accs_accepted]) >>
  drule_all accepted_TS >> disch_then (qspec_then ‘n’ mp_tac) >> strip_tac >>
  gvs[MEM_MAP] >> drule_all eofr_not_live >> simp[]
QED

(* MAIN (Q1): in a world where only finitely many things arrive, the
   polling run of the echo program reaches a round after which it performs
   no actions, and nothing the server declares interest in is ready *)
Theorem echo_stable:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
       SA lfdn (EI lfdn) s0 n = [] ∧
       ∀x. Readable x ∈ (server2 lfdn).interest (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 n)) ⇒
           ¬is_ready (gstate (EI lfdn) (EM lfdn) s0 n) (n2w x)
Proof
  strip_tac >>
  qspecl_then [‘s0’, ‘EI lfdn’, ‘EM lfdn’] mp_tac
    (Q.GENL [‘s0’, ‘ifds’, ‘m’] static_after) >>
  simp[] >> strip_tac >>
  ‘static_from lfdn s0 N’ by simp[] >>
  qspecl_then [‘s0’, ‘lfdn’, ‘ksN lfdn s0 N’, ‘N’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘ks’, ‘N’] meas_zero) >>
  simp[] >> disch_then (qspec_then ‘N’ mp_tac) >> simp[] >> strip_tac >>
  ‘∀n. n0 ≤ n ⇒ meas lfdn s0 (ksN lfdn s0 N) n = 0’
    by (rpt strip_tac >>
        qspecl_then [‘s0’, ‘lfdn’, ‘N’, ‘n0’, ‘n’, ‘ksN lfdn s0 N’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘N’, ‘n’, ‘j’, ‘ks’] meas_le) >>
        simp[]) >>
  qexists_tac ‘SUC n0’ >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (Cases_on ‘n’ >> gvs[] >> irule zero_no_actions >> simp[] >>
      qexists_tac ‘N’ >> simp[])
  >> rpt strip_tac >> drule_at Any zero_interest >> simp[] >>
  qexists_tac ‘N’ >> simp[]
QED
