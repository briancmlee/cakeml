(*
  The shared E1 trace layer, events (close-v2): what an E1 run's raw L0
  events can be, generic in the program.
   - No round listens, and every connect is to a port the program asked
     for (erounds_evs_ok): the T3/T4 shape of the L0 claims.
   - l0sysEpisodes' episodes are monotone under trace prefixes
     (l0_ep_role_mono, l0_ep_sent_mono), and a start whose events make no
     episode and send nothing (the stdio check, the listen) changes no
     episode's role kind or sent bytes (l0_ep_role_quiet, l0_ep_sent_quiet).
*)
Theory e1TraceEvents
Ancestors
  moonshotSentGlue honestL1EPModel honestL1PFConnRun honestL1PFRound honestL1Model
  l0sysEpisodes
Libs
  preamble

(* ------------------------------------------------------------------------
   No listen; connects only to the program's ports
   ------------------------------------------------------------------------ *)

Definition e1ev_ok_def:
  e1ev_ok P (IO_event n conf bs) ⇔
    n ≠ ExtCall «sys_listen» ∧ (n = ExtCall «sys_connect» ⇒ ∃p. P p ∧ conf = port_bytes p)
End

Theorem names_ok:
  ev_name ev ≠ ExtCall «sys_listen» ∧ ev_name ev ≠ ExtCall «sys_connect» ⇒ e1ev_ok P ev
Proof
  Cases_on ‘ev’ >> simp[ev_name_def, e1ev_ok_def]
QED

Theorem names_ok_every:
  EVERY (λev. ev_name ev ≠ ExtCall «sys_listen» ∧ ev_name ev ≠ ExtCall «sys_connect») evs ⇒
  EVERY (e1ev_ok P) evs
Proof
  rw[EVERY_MEM] >> res_tac >> irule names_ok >> simp[]
QED

Theorem edo_ok:
  edo lfd pol (w, es) x = SOME (r, ws', evs) ∧ (∀p. x = EConnect p ⇒ P p) ⇒
  EVERY (e1ev_ok P) evs
Proof
  Cases_on ‘∃p. x = EConnect p’
  >- (gvs[] >> simp[edo_def, AllCaseEqs(), sys_connect_def] >> rw[] >>
      drule l0_do_cases >> rw[] >> simp[e1ev_ok_def] >> metis_tac[]) >>
  strip_tac >> irule names_ok_every >>
  PairCases_on ‘ws'’ >> gvs[] >> drule edo_names >>
  simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[]
QED

Theorem eacts_ok:
  ∀acts ws rs evs ws'.
    eacts lfd pol ws acts = SOME (rs, evs, ws') ∧ (∀p. MEM (EConnect p) acts ⇒ P p) ⇒
    EVERY (e1ev_ok P) evs
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws’ >> drule edo_ok >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem etail_ok:
  etail lfd pol hs (w, es) = SOME (rdy, ws', log, tevs) ⇒ EVERY (e1ev_ok P) tevs
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘_ = tevs’ (SUBST1_TAC o SYM) >> simp[] >>
  rpt conj_tac >> irule names_ok_every
  >- (drule l1_polls_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[])
  >- (drule l1_flush_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[])
  >- (qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
      drule pf_fetch_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[])
  >- (qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >>
      drule l1_reap_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[]) >>
  drule settle_fds_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[]
QED

(* Every event of an E1 run: no listen, and a connect to a port P allows,
   if every connect the program asks for is to such a port *)
Theorem erounds_evs_ok:
  (∀h p. MEM (EConnect p) (new_actions (log_of m) h) ⇒ P p) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ⇒ EVERY (e1ev_ok P) evs
Proof
  strip_tac >> Induct >> simp[erounds_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 ‘etail _ _ _ ws1 = _’ >> PairCases_on ‘ws1’ >>
  drule etail_ok >> simp[] >> disch_then kall_tac >>
  drule eacts_ok >> disch_then irule >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Episodes under prefixes
   ------------------------------------------------------------------------ *)

Theorem ep_io_prefix:
  ep_io sel j opn n xs ≼ ep_io sel j opn n (xs ++ ys)
Proof
  simp[ep_io_append]
QED

Theorem l0_ep_sent_mono:
  xs ≼ ys ⇒ l0_ep_sent j xs ≼ l0_ep_sent j ys
Proof
  rw[IS_PREFIX_APPEND] >> simp[l0_ep_sent_def, ep_io_append]
QED

Theorem ep_roles_prefix:
  ∀xs lst. ep_roles lst xs ≼ ep_roles lst (xs ++ ys)
Proof
  Induct >> simp[ep_roles_def]
QED

Theorem l0_ep_role_mono:
  xs ≼ ys ∧ l0_ep_role j xs = SOME r ⇒ l0_ep_role j ys = SOME r
Proof
  rw[IS_PREFIX_APPEND] >> gvs[l0_ep_role_def, AllCaseEqs()] >>
  qspecl_then [‘xs’, ‘[]’] mp_tac (Q.GEN ‘ys’ ep_roles_prefix |> Q.SPEC ‘l’) >>
  rw[IS_PREFIX_APPEND] >> simp[EL_APPEND1]
QED

(* The number of episodes is what ep_next counts *)
Theorem ep_roles_LENGTH:
  ∀xs lst opn k. LENGTH (ep_roles lst xs) + k = SND (FOLDL ep_next (opn, k) xs)
Proof
  Induct >> simp[ep_roles_def] >> rpt gen_tac >> simp[ep_next_def] >>
  Cases_on ‘ev_new h’ >> simp[]
  >- (qmatch_goalsub_abbrev_tac ‘ep_roles L xs’ >>
      first_x_assum (qspecl_then [‘L’, ‘opn’, ‘k’] mp_tac) >> simp[]) >>
  PairCases_on ‘x’ >> Cases_on ‘x1’ >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘ep_roles L xs’ >>
  qmatch_goalsub_abbrev_tac ‘FOLDL ep_next (OP, _) xs’ >>
  first_x_assum (qspecl_then [‘L’, ‘OP’, ‘k + 1’] mp_tac) >> simp[]
QED

(* A start that makes no episode and sends nothing *)
Theorem l0_ep_sent_quiet:
  EVERY (λev. ev_new ev = NONE ∧ l0sysEpisodes$ev_sent ev = NONE) pre ⇒
  l0_ep_sent j (pre ++ xs) = l0_ep_sent j xs
Proof
  simp[l0_ep_sent_def] >> qid_spec_tac ‘pre’ >> Induct >> simp[ep_io_def]
QED

Definition rkind_def:
  rkind r r' ⇔ (∀p. r = Connected p ⇔ r' = Connected p) ∧ ((∃p. r = Accepted p) ⇔ ∃p. r' = Accepted p)
End

Theorem ep_roles_kinds:
  ∀xs lst lst'. LIST_REL rkind (ep_roles lst xs) (ep_roles lst' xs)
Proof
  Induct >> simp[ep_roles_def] >> rpt gen_tac >>
  Cases_on ‘ev_new h’ >> simp[] >> PairCases_on ‘x’ >> Cases_on ‘x1’ >> simp[rkind_def]
QED

Theorem ep_roles_quiet:
  ∀pre lst xs. EVERY (λev. ev_new ev = NONE) pre ⇒ ∃lst'. ep_roles lst (pre ++ xs) = ep_roles lst' xs
Proof
  Induct >> simp[ep_roles_def] >> metis_tac[]
QED

Theorem l0_ep_role_quiet:
  EVERY (λev. ev_new ev = NONE) pre ⇒
  (l0_ep_role j (pre ++ xs) = SOME (Connected p) ⇔ l0_ep_role j xs = SOME (Connected p)) ∧
  ((∃p. l0_ep_role j (pre ++ xs) = SOME (Accepted p)) ⇔ ∃p. l0_ep_role j xs = SOME (Accepted p))
Proof
  strip_tac >> drule ep_roles_quiet >> disch_then (qspecl_then [‘[]’, ‘xs’] strip_assume_tac) >>
  qspecl_then [‘xs’, ‘lst'’, ‘[]’] mp_tac ep_roles_kinds >> strip_tac >>
  imp_res_tac LIST_REL_LENGTH >>
  simp[l0_ep_role_def] >>
  qpat_x_assum ‘ep_roles [] _ = _’ (fn th => REWRITE_TAC[th]) >> Cases_on ‘j < LENGTH (ep_roles [] xs)’ >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[rkind_def]
QED
