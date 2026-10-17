(*
  The verified version-2 echo server (EchoSpec2's echo2_prog, with close and
  fd reuse) is fd-disciplined in every version-2 server world: every socket
  event names the listener or an fd that is open (accepted and not closed
  since).  Its handle layer only reaches fds through its handle table, and
  the table holds exactly the world's open fds (close-v2's hsim0).
*)
Theory fdDiscipline2
Ancestors
  llist ffi ffiSpikeSocketFFI socketV2FFI socketV2Fair EchoSpec2 socketV2Proof
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4Loop asyncM4SockInv asyncM4EchoRunOk
  asyncHLModel asyncHLSimWorld asyncHLSimOps asyncHLEpisodes asyncHLEof asyncHLSimEvents
  asyncHLSimRun asyncHLSimTrace asyncHLMain endpointSpecForms endpointInstances
  endpointTrace endpointEcho2 fdDiscipline socketV2Events
Libs
  preamble

(* A program is fd-disciplined in version 2's worlds *)
Definition v2_disciplined_def:
  v2_disciplined lfd prog ⇔
    ∀sk. server_world2 lfd sk ⇒
         ∃io. semantics_prog (init_state (socket2_ffi sk)) init_env prog (Diverge io) ∧
              fd_disciplined lfd io
End

(* Every event names lfd or an fd open before it (opn: the open fds and
   their episodes, as ep_st tracks them) *)
Definition disc_from_def:
  disc_from lfd k opn [] = T ∧
  disc_from lfd k opn (e :: es) =
    (EVERY (λf. f = lfd ∨ MEM f (MAP FST opn)) (event_fds e) ∧
     disc_from lfd (FST (ep_st k opn [e])) (SND (ep_st k opn [e])) es)
End

Theorem ep_st_CONS:
  ep_st k opn (e :: es) = ep_st (FST (ep_st k opn [e])) (SND (ep_st k opn [e])) es
Proof
  ‘e :: es = [e] ++ es’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[ep_st_APPEND] >> Cases_on ‘ep_st k opn [e]’ >> simp[]
QED

Theorem disc_from_APPEND:
  ∀e1 k opn. disc_from lfd k opn (e1 ++ e2) ⇔
             disc_from lfd k opn e1 ∧
             disc_from lfd (FST (ep_st k opn e1)) (SND (ep_st k opn e1)) e2
Proof
  Induct >- simp[disc_from_def, ep_st_def] >> rpt gen_tac >>
  ‘ep_st k opn (h::e1) = ep_st (FST (ep_st k opn [h])) (SND (ep_st k opn [h])) e1’
    by simp[Once ep_st_CONS] >>
  pop_assum SUBST1_TAC >> fs[disc_from_def, CONJ_ASSOC]
QED

Theorem MEM_FST_ADELKEY:
  MEM x (MAP FST (ADELKEY f l)) ⇔ MEM x (MAP FST l) ∧ x ≠ f
Proof
  simp[ADELKEY_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

(* The open fds of the trace are ep_st's *)
Theorem open_now_ep_st:
  ∀evs L k opn.
    (∀f. MEM f (open_now L) ⇔ MEM f (MAP FST opn)) ∧
    EVERY (λe. event_opened e = event_accepted e) evs ⇒
    ∀f. MEM f (open_now (REVERSE evs ++ L)) ⇔ MEM f (MAP FST (SND (ep_st k opn evs)))
Proof
  Induct >- simp[ep_st_def] >> rpt gen_tac >> strip_tac >> fs[] >>
  ‘REVERSE evs ++ [h] ++ L = REVERSE evs ++ h :: L’ by simp[] >>
  simp[Once ep_st_CONS] >>
  first_x_assum irule >> simp[] >>
  simp[open_now_def, ep_st_def] >> every_case_tac >> fs[MEM_FST_ADELKEY, MEM_FILTER] >>
  metis_tac[]
QED

Theorem disc_from_prefix:
  ∀evs k opn L. disc_from lfd k opn evs ∧
    (∀f. MEM f (open_now L) ⇔ MEM f (MAP FST opn)) ∧
    EVERY (λe. event_opened e = event_accepted e) evs ⇒
    ∀pre ev post. evs = pre ++ ev :: post ⇒
      EVERY (λf. f = lfd ∨ MEM f (open_now (REVERSE pre ++ L))) (event_fds ev)
Proof
  rpt strip_tac >> gvs[disc_from_APPEND, disc_from_def] >>
  ‘∀f. MEM f (open_now (REVERSE pre ++ L)) ⇔ MEM f (MAP FST (SND (ep_st k opn pre)))’
    by (irule open_now_ep_st >> simp[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   One action, one round
   ------------------------------------------------------------------------ *)

Theorem fd_of_fd_bytes:
  bytes_fd (TAKE 8 (fd_bytes c ++ l)) = c
Proof
  ‘8 = LENGTH (fd_bytes c)’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[TAKE_LENGTH_APPEND]
QED

Theorem open_of_tbl:
  hsim0 lfd s1 (s2, hs) ∧ ALOOKUP hs.tbl h = SOME f ⇒ MEM f (MAP FST s2.open_fds)
Proof
  rw[hsim0_def] >> res_tac >> imp_res_tac ALOOKUP_MEM >>
  simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem hdo_disc:
  hsim0 lfd s1 (s2, hs) ∧ hdo lfd (s2, hs) a = SOME (r, (s2', hs'), evs) ∧
  act_ok lfd hs.nxt a ⇒
  disc_from lfd hs.nxt s2.open_fds evs
Proof
  strip_tac >> Cases_on ‘a’ >> fs[act_ok_def] >>
  qpat_x_assum ‘hdo _ _ _ = _’ mp_tac >> simp[hdo_def, AllCaseEqs()] >> rw[] >>
  simp[disc_from_def, act_event_def, event_fds_def, close_event_def, ep_st_def,
       event_accepted_def, event_closed_def, fd_of_fd_bytes] >>
  TRY (Cases_on ‘r'’) >> simp[act_event_def, event_fds_def, event_accepted_def] >>
  metis_tac[open_of_tbl]
QED

(* As hacts_events, with discipline *)
Theorem hacts_disc:
  ∀acts s1 s2 hs rs evs1 s1' P.
    hsim lfd s1 (s2, hs) ∧ sched_wf2 s2 ∧ EVERY (action_ok lfd acc) acts ∧
    set acc ⊆ set (GENLIST (hdl lfd) hs.nxt) ∧
    sock_acts s1 acts = SOME (rs, evs1, s1') ∧
    closed_eof lfd P hs ∧ no_after_eof P (ZIP (acts, rs)) ⇒
    ∃evs2 s2' hs'.
      hacts lfd (s2, hs) acts = SOME (rs, evs2, (s2', hs')) ∧
      disc_from lfd hs.nxt s2.open_fds evs2
Proof
  Induct
  >- simp[sock_acts_def, hacts_def, disc_from_def]
  >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘sock_acts _ _ = _’ mp_tac >> simp[sock_acts_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 ‘sock_do s1 a = SOME (r, s1a)’ >>
  ‘act_ok lfd hs.nxt a’
    by (Cases_on ‘a’ >> fs[action_ok_def, act_ok_def, SUBSET_DEF] >>
        res_tac >> fs[MEM_GENLIST] >> metis_tac[]) >>
  ‘∃s2a hsa evsa. hdo lfd (s2, hs) a = SOME (r, (s2a, hsa), evsa) ∧
                  hsim lfd s1a (s2a, hsa) ∧ LENGTH s2a.clients = LENGTH s2.clients ∧
                  s2a.future = s2.future’
    by (Cases_on ‘a’ >> fs[act_ok_def]
        >- (rveq >> drule_all hdo_sim_accept >> simp[])
        >- (rveq >> drule_all hdo_sim_read >> simp[])
        >> rveq >> drule_all hdo_sim_write >> simp[]) >>
  ‘sched_wf2 s2a’ by metis_tac[hdo_sched_wf2] >>
  drule hdo_nxt >> strip_tac >>
  qpat_x_assum ‘no_after_eof _ _’ (strip_assume_tac o MATCH_MP no_after_eof_CONS) >>
  ‘∀c bs. a = Write c bs ⇒ ALOOKUP hs.tbl c ≠ NONE’
    by (rpt strip_tac >> gvs[act_ok_def] >>
        gvs[closed_eof_def] >> first_x_assum drule_all >> strip_tac >>
        first_x_assum drule >> simp[sock_on_def]) >>
  ‘hsim0 lfd s1 (s2, hs)’ by fs[hsim_def] >>
  drule_all hdo_events >> strip_tac >>
  drule_all hdo_disc >> strip_tac >>
  first_x_assum (qspecl_then [‘s1a’, ‘s2a’, ‘hsa’, ‘rs'’, ‘evs’, ‘s1'’,
                              ‘P ++ [(a, r)]’] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (fs[SUBSET_DEF] >> rw[] >> res_tac >> fs[])
      >> rw[closed_eof_def] >> drule_all hdo_closed >> strip_tac
      >- (fs[closed_eof_def] >> metis_tac[])
      >> gvs[] >> metis_tac[]) >>
  strip_tac >>
  simp[hacts_def, disc_from_APPEND]
QED

(* ------------------------------------------------------------------------
   The rounds
   ------------------------------------------------------------------------ *)

Theorem hpoll_fds_open:
  MEM f (hpoll_fds lfd hs hfds) ⇒ f = lfd ∨ ∃h. ALOOKUP hs.tbl h = SOME f
Proof
  rw[hpoll_fds_def, MEM_FLAT, MEM_MAP] >> every_case_tac >> fs[] >> metis_tac[]
QED

Theorem spoll2_event_fds:
  event_fds (spoll2_event fds s) = fds ∧ event_accepted (spoll2_event fds s) = NONE ∧
  event_closed (spoll2_event fds s) = NONE
Proof
  simp[spoll2_event_def, event_fds_def, event_accepted_def, event_closed_def]
QED

Theorem rounds2_disc:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. disc_from (n2w lfdn) 0 []
        (FLAT (GENLIST (hround_events (n2w lfdn) (interest [n2w lfdn])
                          (srelabel (server lfdn)) s2) n))
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘grun_ok (interest [n2w lfdn]) (srelabel (server lfdn)) s1’
    by (irule echo_grun_ok >> simp[]) >>
  drule_all hrun_sim >> strip_tac >>
  drule_all hrun_events >> strip_tac >>
  Induct >- simp[disc_from_def] >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >> gvs[] >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto EI ES s1 n’ by simp[grun_ok_gok_upto] >>
  drule echo_round_actions_ok >> strip_tac >>
  drule_then (qspecl_then [‘n’, ‘EI’] assume_tac) round_no_after_eof >>
  qspecl_then [‘gacts EI ES s1 n’, ‘gstate EI ES s1 n’, ‘s2k’, ‘hsk’,
               ‘gres EI ES s1 n’, ‘evs’, ‘s'’, ‘gperf EI ES s1 n’] mp_tac
    (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf EI ES s1 n)’] hacts_events) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  qspecl_then [‘gacts EI ES s1 n’, ‘gstate EI ES s1 n’, ‘s2k’, ‘hsk’,
               ‘gres EI ES s1 n’, ‘evs’, ‘s'’, ‘gperf EI ES s1 n’] mp_tac
    (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf EI ES s1 n)’] hacts_disc) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >> gvs[] >>
  ‘hacts_of (n2w lfdn) EI ES s2 n = gacts EI ES s1 n’
    by simp[hacts_of_def, gacts_def] >>
  ‘hround_events (n2w lfdn) EI ES s2 n =
     evs2 ++ [spoll2_event (hpoll_fds (n2w lfdn) hs' (EI (hhist (n2w lfdn) EI ES s2 n))) s2']’
    by simp[hround_events_alt, hacts_tot_def] >>
  simp[GENLIST, SNOC_APPEND, disc_from_APPEND, ep_st_APPEND] >>
  simp[disc_from_def, spoll2_event_fds, EVERY_MEM] >>
  rpt strip_tac >> drule hpoll_fds_open >> strip_tac >> simp[] >>
  ‘hsim0 (n2w lfdn) s' (s2', hs')’ by fs[hsim_def] >>
  metis_tac[open_of_tbl]
QED

Theorem opened_accepted_ok:
  event_ok no_conn_send ev ⇒ event_opened ev = event_accepted ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  rw[event_ok_def, no_conn_send_def, event_opened_def, event_accepted_def] >>
  every_case_tac >> fs[]
QED

(* MAIN: the verified version-2 echo server is fd-disciplined *)
Theorem echo2_prog_disciplined:
  v2_disciplined 3w echo2_prog
Proof
  rw[v2_disciplined_def, server_world2_def] >>
  ‘echo2_run_ok sk’
    by (qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s2’, ‘lfdn’] hrun_ok_echo) >> simp[]) >>
  drule echo2_semantics_prog >> strip_tac >>
  qexists_tac ‘echo2_trace sk’ >> simp[] >>
  rw[fd_disciplined_def, always_def] >>
  qmatch_asmsub_abbrev_tac ‘LFLATTEN (LGENLIST (λi. fromList (R i)) NONE)’ >>
  ‘∀i. R i ≠ []’
    by (simp[Abbr ‘R’, hround_events_alt] >> gen_tac >>
        qmatch_goalsub_abbrev_tac ‘_ X ≠ []’ >> PairCases_on ‘X’ >> simp[]) >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘disc_from 3w 0 [] (FLAT (GENLIST R (SUC n)))’
    by (qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s2’, ‘lfdn’] rounds2_disc) >>
        simp[Abbr ‘R’]) >>
  ‘EVERY (event_ok no_conn_send) (FLAT (GENLIST R (SUC n)))’
    by (qpat_assum ‘semantics_prog _ _ _ _’
          (fn th => mp_tac (Q.GEN ‘evs’ (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (Q.INST [‘P’ |-> ‘no_conn_send’] run_events_ok)) th))) >>
        disch_then (qspec_then ‘FLAT (GENLIST R (SUC n))’ mp_tac) >>
        simp[socket2_ffi_def, socket2_oracle_ok, rounds_LPREFIX]) >>
  ‘∃post. FLAT (GENLIST R (SUC n)) = pre ++ ev :: post’
    by (qpat_x_assum ‘pre ++ [ev] ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >>
        qexists_tac ‘l’ >> simp[]) >>
  qspecl_then [‘FLAT (GENLIST R (SUC n))’, ‘0’, ‘[]’, ‘[]’] mp_tac
    (Q.INST [‘lfd’ |-> ‘3w’] disc_from_prefix) >>
  impl_tac
  >- (simp[open_now_def] >> fs[EVERY_MEM] >> metis_tac[opened_accepted_ok]) >>
  disch_then (qspecl_then [‘pre’, ‘ev’, ‘post’] mp_tac) >> simp[]
QED
