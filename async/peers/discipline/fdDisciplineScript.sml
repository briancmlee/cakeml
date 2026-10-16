(*
  Our servers are fd-disciplined (peerInstances' fd_disciplined): every
  socket event of their traces names only the listener or a connection
  they have accepted.  Generic: any server whose model accepts only on lfd
  and touches an fd only after accepting it (uses_ok), run by the polling
  loop (grounds_events), has an fd-disciplined trace (rounds_disciplined).
  The echo server is an instance (echo_prog_disciplined).
*)
Theory fdDiscipline
Ancestors
  llist ffi socketWorld EchoEpisodesSpec loopPollWorld loopRounds loopRoundsTrans
  loopPollDyn loopSockInv skeletonRunOk lifetimeSimRun peerSpecForms
  peerInstances
Libs
  preamble

(* ------------------------------------------------------------------------
   The events of performed actions
   ------------------------------------------------------------------------ *)

(* An action and its response are of the same kind *)
Definition resp_ok_def:
  resp_ok (Accept l, Accepted x) = T ∧
  resp_ok (Read c n, Got x) = T ∧
  resp_ok (Write c bs, Wrote) = T ∧
  resp_ok _ = F
End

Theorem sock_acts_events:
  ∀acts s rs evs s'. sock_acts s acts = SOME (rs, evs, s') ⇒
    evs = MAP (UNCURRY act_event) (ZIP (acts, rs)) ∧ LENGTH rs = LENGTH acts ∧
    EVERY resp_ok (ZIP (acts, rs))
Proof
  Induct >> simp[sock_acts_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >>
  strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on ‘h’ >> gvs[sock_do_def, resp_ok_def] >>
  TRY (Cases_on ‘z’) >> gvs[resp_ok_def]
QED

Theorem act_event_props:
  resp_ok (a, r) ⇒
  event_closed (act_event a r) = NONE ∧
  event_opened (act_event a r) =
    (case (a, r) of (Accept l, Accepted (SOME c)) => SOME c | _ => NONE) ∧
  event_fds (act_event a r) =
    (case a of Accept l => [l] | Read c n => [c] | Write c bs => [c])
Proof
  Cases_on ‘a’ >> Cases_on ‘r’ >>
  simp[resp_ok_def, act_event_def, event_closed_def, event_opened_def,
       event_accepted_def, event_fds_def] >>
  TRY (Cases_on ‘o'’) >> simp[] >>
  TRY (‘TAKE 8 (fd_bytes c ++ l) = fd_bytes c’
         by (‘8 = LENGTH (fd_bytes c)’ by simp[] >> metis_tac[TAKE_LENGTH_APPEND]) >>
       simp[] >> NO_TAC) >>
  simp[MAP_ZIP]
QED

Theorem opened_fds_APPEND[simp]:
  opened_fds (a ++ b) = opened_fds a ++ opened_fds b ∧ opened_fds [] = []
Proof
  simp[opened_fds_def]
QED

Theorem opened_fds_acts:
  ∀ps. EVERY resp_ok ps ⇒ opened_fds (MAP (UNCURRY act_event) ps) = wacc ps
Proof
  Induct >> simp[opened_fds_def, wacc_def, FORALL_PROD] >> rpt strip_tac >>
  drule act_event_props >> strip_tac >> fs[opened_fds_def] >>
  every_case_tac >> gvs[]
QED

Theorem spoll_event_props:
  event_closed (spoll_event fds s) = NONE ∧ event_opened (spoll_event fds s) = NONE ∧
  event_fds (spoll_event fds s) = fds
Proof
  simp[spoll_event_def, event_closed_def, event_opened_def, event_accepted_def,
       event_fds_def]
QED

(* Without closes, the open fds are the opened ones *)
Theorem open_now_no_close:
  ∀pre. EVERY (λev. event_closed ev = NONE) pre ⇒
        (MEM f (open_now (REVERSE pre)) ⇔ MEM f (opened_fds pre))
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[open_now_def, opened_fds_def] >>
  rw[REVERSE_SNOC, open_now_def, EVERY_SNOC] >> every_case_tac >> fs[opened_fds_def] >>
  simp[SNOC_APPEND, FLAT_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The rounds of a uses_ok server
   ------------------------------------------------------------------------ *)

Overload RE = “λlfdn m s0. grounds_events (interest [n2w lfdn : word64]) (srelabel m) s0”

Theorem round_events:
  grun_ok (interest [n2w lfdn]) (srelabel m) s0 ⇒
  RE lfdn m s0 n =
    MAP (UNCURRY act_event)
        (ZIP (gacts (interest [n2w lfdn]) (srelabel m) s0 n,
              gres (interest [n2w lfdn]) (srelabel m) s0 n)) ++
    [spoll_event (interest [n2w lfdn] (ghist (interest [n2w lfdn]) (srelabel m) s0 n))
                 (SND (SND (sock_acts_tot (gstate (interest [n2w lfdn]) (srelabel m) s0 n)
                                          (gacts (interest [n2w lfdn]) (srelabel m) s0 n))))] ∧
  EVERY resp_ok (ZIP (gacts (interest [n2w lfdn]) (srelabel m) s0 n,
                      gres (interest [n2w lfdn]) (srelabel m) s0 n)) ∧
  LENGTH (gres (interest [n2w lfdn]) (srelabel m) s0 n) =
  LENGTH (gacts (interest [n2w lfdn]) (srelabel m) s0 n)
Proof
  strip_tac >> simp[grounds_events_alt] >>
  fs[grun_ok_def] >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘sock_acts (gstate (interest [n2w lfdn]) (srelabel m) s0 n)
                      (gacts (interest [n2w lfdn]) (srelabel m) s0 n)’ >> simp[] >>
  rename1 ‘SOME p’ >> PairCases_on ‘p’ >> strip_tac >>
  drule sock_acts_events >> simp[sock_acts_tot_def, gres_def]
QED

Theorem rounds_props:
  grun_ok (interest [n2w lfdn]) (srelabel m) s0 ⇒
  ∀N. opened_fds (FLAT (GENLIST (RE lfdn m s0) N)) =
        wacc (gperf (interest [n2w lfdn]) (srelabel m) s0 N) ∧
      EVERY (λev. event_closed ev = NONE) (FLAT (GENLIST (RE lfdn m s0) N))
Proof
  strip_tac >> Induct >- simp[gperf_def, wacc_def] >>
  simp[GENLIST, SNOC_APPEND, gperf_SUC] >>
  drule round_events >> disch_then (qspec_then ‘N’ strip_assume_tac) >>
  simp[opened_fds_acts, EVERY_MAP] >>
  simp[opened_fds_def, spoll_event_props] >>
  fs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >>
  metis_tac[act_event_props]
QED

(* Every event names only lfd or what is open before it *)
Definition disc_def:
  disc lfd evs ⇔
    ∀pre ev post. evs = pre ++ [ev] ++ post ⇒
                  EVERY (λf. f = lfd ∨ MEM f (open_now (REVERSE pre))) (event_fds ev)
End

Theorem split_APPEND:
  pre ++ ev :: post = X ++ Y ⇒
  (∃p. X = pre ++ ev :: p) ∨ (∃q. pre = X ++ q ∧ Y = q ++ ev :: post)
Proof
  strip_tac >>
  qpat_x_assum ‘_ = _’ (strip_assume_tac o ONCE_REWRITE_RULE [APPEND_EQ_APPEND]) >>
  rveq >> TRY (Cases_on ‘l’) >> fs[] >> rveq >>
  metis_tac[APPEND_NIL, APPEND, APPEND_ASSOC]
QED

Theorem rounds_disc:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀N. disc (n2w lfdn) (FLAT (GENLIST (RE lfdn m s0) N))
Proof
  strip_tac >>
  ‘grun_ok (interest [n2w lfdn]) (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  drule rounds_props >> strip_tac >>
  Induct >- simp[disc_def] >>
  rw[disc_def] >> fs[GENLIST, SNOC_APPEND] >>
  qpat_x_assum ‘FLAT _ ++ _ = _’
    (assume_tac o SYM o REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule split_APPEND >> strip_tac
  >- (fs[disc_def] >> first_x_assum irule >> metis_tac[]) >>
  gvs[] >>
  ‘EVERY (λev. event_closed ev = NONE) (FLAT (GENLIST (RE lfdn m s0) N) ++ q)’
    by (first_x_assum (qspec_then ‘SUC N’ mp_tac) >>
        simp[GENLIST, SNOC_APPEND] >> rw[EVERY_APPEND] >> fs[EVERY_APPEND]) >>
  simp[open_now_no_close] >>
  ‘∀f. MEM f (wacc (gperf (interest [n2w lfdn]) (srelabel m) s0 N)) ⇒
       MEM f (opened_fds (FLAT (GENLIST (RE lfdn m s0) N) ++ q))’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘N’ mp_tac) >> simp[]) >>
  ‘MEM ev (RE lfdn m s0 N)’ by (qpat_x_assum ‘RE _ _ _ _ = _’ SUBST1_TAC >> simp[]) >>
  drule round_events >> disch_then (qspec_then ‘N’ strip_assume_tac) >>
  qpat_x_assum ‘MEM ev _’ mp_tac >>
  qpat_x_assum ‘RE _ _ _ N = MAP _ _ ++ _’ SUBST1_TAC >>
  rw[MEM_MAP]
  >- (rename1 ‘MEM p (ZIP _)’ >> PairCases_on ‘p’ >>
      ‘resp_ok (p0, p1)’ by (drule round_events >> rw[EVERY_MEM] >> res_tac) >>
      drule act_event_props >> strip_tac >> simp[] >>
      ‘action_ok (n2w lfdn) (wacc (gperf (interest [n2w lfdn]) (srelabel m) s0 N)) p0’
        by (‘gok_upto (interest [n2w lfdn]) (srelabel m) s0 N’
              by metis_tac[grun_ok_gok_upto] >>
            drule_all gen_round_actions_ok >> rw[EVERY_MEM] >> first_x_assum irule >>
            drule round_events >> disch_then (qspec_then ‘N’ strip_assume_tac) >>
            imp_res_tac MEM_ZIP_MEM_MAP >> rfs[]) >>
      Cases_on ‘p0’ >> fs[action_ok_def])
  >- (simp[spoll_event_props, EVERY_MEM] >> rpt strip_tac >>
      drule interest_ghist_sub >> disch_then drule >> simp[] >> metis_tac[])
QED

(* MAIN: the trace of a uses_ok server, run by the polling loop, is
   fd-disciplined *)
Theorem rounds_disciplined:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  fd_disciplined (n2w lfdn) (LFLATTEN (LGENLIST (λi. fromList (RE lfdn m s0 i)) NONE))
Proof
  rw[fd_disciplined_def, always_def] >>
  ‘∀i. RE lfdn m s0 i ≠ []’ by simp[grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘disc (n2w lfdn) (FLAT (GENLIST (RE lfdn m s0) (SUC n)))’ by metis_tac[rounds_disc] >>
  fs[disc_def, IS_PREFIX_APPEND] >> first_x_assum irule >>
  qexists_tac ‘l'’ >> simp[]
QED
