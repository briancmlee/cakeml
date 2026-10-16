(*
  ChatSpecTimely for the loop's trace of the chat server: bounded latency,
  counted in polls (one per round).

   - chat_deliver_rounds: what d is owed at round R is written by the end
     of round R + 2 (chat_cover_at: the hub has told d's writer by round
     R + 2; server_v_live_at with B = 0: told is written in that round).
     So the bound is 3 rounds, whatever the number of clients.
   - chat_prompt_trace: on the trace, whatever d is owed at any point is
     written before 4 more polls (chat_prompt 4).
   - chat_accept_rounds: a connection that arrived within the first n
     steps of the schedule is accepted by round n + 3 * (the number of
     connections that arrived within those steps): m_queue_progress_at,
     and the listener's queue is no longer than that number (the world
     only creates connections on Connect arrivals).
   - chat_accept_trace: chat_accept_prompt 3, on the trace.
*)
Theory asyncChatTimely
Ancestors
  pair list rich_list arithmetic option string words llist alist pred_set
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncM4ServerUses asyncRunOkGen asyncM4GRounds asyncM4SockModel
  asyncM4SockInv asyncM4GTrans asyncM4Sched asyncM4Queue asyncM4LiveWorld
  asyncM3World ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec HttpSpec ChatSpec
  asyncSWSock asyncWithStore asyncChatSW
  ChatSpecTimely ChatSpecTimelyBite asyncServerV asyncServerVLive
  asyncServerVLiveA asyncServerVPushLive asyncServerVAcceptAt asyncWithTap
  asyncChatModel asyncChatSafe asyncChatTrace asyncChatLiveV
  asyncChatLiveDeliver asyncChatLiveCoverRun asyncChatLiveAccept
  asyncChatLiveDeliverRun
Libs
  preamble

Overload CWr = “with_tap chat_tap chat_delta empty_store”
Overload CIn = “tap_hist chat_tap chat_delta empty_store”
(* the same, at the chat server's types *)
Overload CWrT = “with_tap chat_tap chat_delta empty_store :
  ((event, (canswer, asyncServer$response) kres) snapshot list ->
   ((action, num # cquery) kact, unit option) outcome) ->
  (event, asyncServer$response) snapshot list -> (action, unit option) outcome”
Overload CInT = “tap_hist chat_tap chat_delta empty_store :
  ((event, (canswer, asyncServer$response) kres) snapshot list ->
   ((action, num # cquery) kact, unit option) outcome) ->
  (event, asyncServer$response) snapshot list ->
  (event, (canswer, asyncServer$response) kres) snapshot list”

(* ------------------------------------------------------------------------
   Rounds and polls
   ------------------------------------------------------------------------ *)

Theorem act_event_not_poll[local]:
  ¬is_poll (act_event a r)
Proof
  Cases_on ‘a’ >> Cases_on ‘r’ >> simp[act_event_def, is_poll_def]
QED

(* Each round's events end with its one poll *)
Theorem polls_round:
  grun_ok ifds m s0 ⇒ polls (grounds_events ifds m s0 i) = 1
Proof
  strip_tac >> drule grun_ok_sock_acts >>
  disch_then (qspec_then ‘i’ strip_assume_tac) >>
  drule sock_acts_events >> strip_tac >>
  simp[grounds_events_alt, sock_acts_tot_def, polls_def, FILTER_APPEND] >>
  simp[spoll_event_def, is_poll_def] >>
  ‘FILTER is_poll evs = []’
    by (simp[FILTER_EQ_NIL, EVERY_EL] >> gvs[EL_MAP2, act_event_not_poll]) >>
  gvs[]
QED

Theorem polls_rounds:
  grun_ok ifds m s0 ⇒
  ∀n. polls (FLAT (GENLIST (grounds_events ifds m s0) n)) = n
Proof
  strip_tac >> drule polls_round >> strip_tac >>
  Induct >> simp[GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  fs[polls_def, FILTER_APPEND]
QED

Theorem polls_mono:
  evs ≼ evs' ⇒ polls evs ≤ polls evs'
Proof
  rw[IS_PREFIX_APPEND] >> simp[polls_def, FILTER_APPEND]
QED

Theorem FLAT_GENLIST_prefix[local]:
  a ≤ b ⇒ FLAT (GENLIST f a) ≼ FLAT (GENLIST f b)
Proof
  strip_tac >> ‘∃k. b = a + k’ by (qexists_tac ‘b − a’ >> simp[]) >>
  pop_assum SUBST1_TAC >> Induct_on ‘k’ >>
  simp[ADD_CLAUSES, GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem written_prefix[local]:
  evs ≼ L ⇒ bytes_written_to c evs ≼ bytes_written_to c L
Proof
  rw[IS_PREFIX_APPEND] >> simp[bytes_written_to_def] >> metis_tac[]
QED

Theorem bytes_mono[local]:
  ∀s t. s ≼ t ⇒ bytes s ≼ bytes t
Proof
  Induct >> simp[bytes_def] >> Cases_on ‘t’ >> fs[bytes_def]
QED

(* ------------------------------------------------------------------------
   Delivery within 3 rounds
   ------------------------------------------------------------------------ *)

(* The library's push liveness with the round, for the chat server *)
Theorem chat_live_at:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (chat_server lfdn) ifds s0 n)) ∧ n ≤ N0 ⇒
  ∃N. N ≤ N0 ∧
      bytes (FLAT (cout (DROP 1
         (conn_answers chatV CWrT CInT chat_handler lfdn ifds s0 N0 c)))) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0) (SUC N)))
Proof
  rw[chat_server_v] >>
  qspecl_then [‘chatV’, ‘CWrT’, ‘CInT’, ‘chat_handler’, ‘λans. cout (DROP 1 ans)’, ‘0’,
               ‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’, ‘N0’]
    mp_tac (Q.GENL [‘V’, ‘Wr’, ‘inner’, ‘hf’, ‘out’, ‘B’, ‘lfdn’, ‘s0’, ‘c’, ‘ifds’,
                    ‘n’, ‘N0’] server_v_live_at) >>
  impl_tac >- simp[wrap_ok_with_tap, vocab_ok_chatV, hokv_chat_handler,
                   handler_push_live_chat] >>
  strip_tac >> qexists_tac ‘N’ >> fs[bytes_def]
QED

(* MAIN: for a connection d accepted by round R, what d is owed at round R
   is written to d by the end of round R + 2 *)
Theorem chat_deliver_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM d (wacc (SPg (chat_server lfdn) ifds s0 R)) ⇒
  bytes (owed_m (w2n d) (TSg (chat_server lfdn) ifds s0 R)) ≼
  bytes_written_to d
    (FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0) (R + 3)))
Proof
  strip_tac >>
  drule_all chat_cover_at >> strip_tac >>
  qspecl_then [‘s0’, ‘lfdn’, ‘d’, ‘ifds’, ‘R’, ‘R + 2’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘ifds’, ‘n’, ‘N0’] chat_live_at) >>
  simp[] >> strip_tac >>
  ‘bytes_written_to d
     (FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0) (SUC N))) ≼
   bytes_written_to d
     (FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0) (R + 3)))’
    by (irule written_prefix >> irule FLAT_GENLIST_prefix >> simp[]) >>
  ‘bytes (owed_m (w2n d) (TSg (chat_server lfdn) ifds s0 R)) ≼
   bytes (CONCAT (cout (DROP 1
     (conn_answers chatV CWr CIn chat_handler lfdn ifds s0 (R + 2) d))))’
    by (irule bytes_mono >> first_assum ACCEPT_TAC) >>
  metis_tac[IS_PREFIX_TRANS]
QED

(* MAIN: chat_prompt 4, for the loop's trace: whatever d is owed at any
   point of the trace is written to d before 4 more polls *)
Theorem chat_prompt_trace:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  LPREFIX (fromList evs)
    (LFLATTEN (LGENLIST
       (λi. fromList (grounds_events ifds (srelabel (chat_server lfdn)) s0 i)) NONE)) ⇒
  ∃evs'. LPREFIX (fromList evs')
           (LFLATTEN (LGENLIST
              (λi. fromList (grounds_events ifds (srelabel (chat_server lfdn)) s0 i))
              NONE)) ∧
         polls evs' ≤ polls evs + 4 ∧
         owed d evs ≼ bytes_written_to d evs'
Proof
  strip_tac >>
  ‘grun_ok ifds (srelabel (chat_server lfdn)) s0’
    by metis_tac[gen_grun_ok, chat_uses_ok_v] >>
  ‘∀i. grounds_events ifds (srelabel (chat_server lfdn)) s0 i ≠ []’
    by simp[grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘n ≤ polls evs’
    by (drule polls_rounds >> disch_then (qspec_then ‘n’ (SUBST1_TAC o SYM)) >>
        irule polls_mono >> first_assum ACCEPT_TAC) >>
  drule_all chat_owed_rounds >> disch_then (qspec_then ‘d’ strip_assume_tac) >>
  qpat_x_assum ‘owed _ _ = _’ SUBST1_TAC >>
  Cases_on ‘MEM d (wacc (SPg (chat_server lfdn) ifds s0 (SUC n)))’
  >- (drule_all chat_deliver_rounds >> strip_tac >>
      qexists_tac ‘FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0)
                                 (SUC n + 3))’ >>
      simp[rounds_LPREFIX] >> conj_tac
      >- (drule polls_rounds >> simp[]) >>
      irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
      irule bytes_mono >> irule owed_m_mono >> first_assum ACCEPT_TAC)
  >> qexists_tac ‘evs’ >> simp[] >>
  ‘owed_m (w2n d) U = ""’ suffices_by simp[bytes_def] >>
  irule owed_m_not_accepted >> strip_tac >>
  ‘MEM (w2n d) (accepted (TSg (chat_server lfdn) ifds s0 (SUC n)))’
    by (qpat_x_assum ‘U ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >> simp[]) >>
  ‘accepted (TSg (chat_server lfdn) ifds s0 (SUC n)) =
   MAP w2n (wacc (SPg (chat_server lfdn) ifds s0 (SUC n)))’
    by (qspecl_then [‘lfdn’, ‘chat_server lfdn’, ‘s0’, ‘ifds’, ‘SUC n’] mp_tac
          (Q.GENL [‘lfdn’, ‘m’, ‘s0’, ‘ifds’, ‘n’] TSg_accepted) >>
        simp[chat_uses_ok_v]) >>
  gvs[MEM_MAP]
QED

(* ------------------------------------------------------------------------
   The world: connections come from Connect arrivals
   ------------------------------------------------------------------------ *)

Theorem sock_do_conns[local]:
  sock_do s a = SOME (r, s') ⇒ MAP FST s'.conns = MAP FST s.conns
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, sock_accept_def, sock_read_def, sock_write_def] >>
  gvs[AllCaseEqs(), MAP_FST_AFUPDKEY]
QED

Theorem sock_acts_conns[local]:
  ∀acts s rs evs s'. sock_acts s acts = SOME (rs, evs, s') ⇒
                     MAP FST s'.conns = MAP FST s.conns
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()] >>
  imp_res_tac sock_do_conns >> metis_tac[]
QED

Theorem deliver1_conn[local]:
  is_conn (deliver1 s a) d ⇒ is_conn s d ∨ ∃l. a = Connect l d
Proof
  Cases_on ‘a’ >> rw[deliver1_def, is_conn_def, AFUPDKEY_ALOOKUP] >>
  every_case_tac >> gvs[]
QED

Theorem deliver_conn[local]:
  ∀as s. is_conn (FOLDL deliver1 s as) d ⇒ is_conn s d ∨ ∃l. MEM (Connect l d) as
Proof
  Induct >> rw[] >> first_x_assum drule >> strip_tac
  >- (drule deliver1_conn >> metis_tac[])
  >> metis_tac[]
QED

Theorem tick_conn_back[local]:
  is_conn (tick s) d ⇒ is_conn s d ∨ ∃l. MEM (Connect l d) (next_step s)
Proof
  rw[tick_def, next_step_def] >> Cases_on ‘LHD s.sched’ >> gvs[deliver_def] >>
  drule deliver_conn >> simp[is_conn_def]
QED

(* A connection of the world arrived in the schedule *)
Theorem conn_arrived:
  grun_ok ifds m s0 ∧ s0.conns = [] ⇒
  ∀n. is_conn (gstate ifds m s0 n) d ⇒
      ∃l. MEM (Connect l d) (arrivals_upto n s0.sched)
Proof
  strip_tac >> Induct
  >- simp[gstate_def, grounds_def, is_conn_def] >>
  simp[gstate_SUC] >> strip_tac >>
  qspecl_then [‘n’, ‘1’] mp_tac grounds_arrivals >>
  ‘n + 1 = SUC n’ by simp[] >> simp[] >> strip_tac >>
  ‘arrivals_upto 1 (gstate ifds m s0 n).sched = next_step (gmid ifds m s0 n)’
    by (REWRITE_TAC[ONE, arrivals_upto_def] >>
        simp[next_step_def, gmid_sched] >> CASE_TAC >> simp[arrivals_upto_def]) >>
  drule tick_conn_back >> strip_tac >> gvs[]
  >- (‘is_conn (gstate ifds m s0 n) d’
        suffices_by (strip_tac >> first_x_assum drule >> metis_tac[]) >>
      drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
      ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def] >>
      drule sock_acts_conns >> strip_tac >>
      qpat_x_assum ‘is_conn (gmid _ _ _ _) _’ mp_tac >>
      simp[is_conn_def, ALOOKUP_NONE])
  >> metis_tac[]
QED

Theorem CARD_le_LENGTH[local]:
  ALL_DISTINCT q ∧ set q ⊆ set L ⇒ LENGTH q ≤ LENGTH L
Proof
  strip_tac >>
  ‘LENGTH q = CARD (set q)’ by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  ‘CARD (set q) ≤ CARD (set L)’ by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (set L) ≤ LENGTH L’ by simp[CARD_LIST_TO_SET] >>
  simp[]
QED

(* The listener's queue is no longer than the number of connections that
   have arrived *)
Theorem lq_nconnects:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  LENGTH (lq (n2w lfdn) (gstate ifds (srelabel m) s0 n)) ≤ nconnects n s0
Proof
  strip_tac >>
  ‘grun_ok ifds (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  drule_all gen_sinv >> disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  gvs[sinv_def, lq_def, ALL_DISTINCT_APPEND, nconnects_def] >>
  qmatch_goalsub_abbrev_tac ‘LENGTH (FILTER P A)’ >>
  ‘LENGTH (FILTER P A) =
   LENGTH (MAP (λa. case a of Connect l c => c | _ => 0w) (FILTER P A))’ by simp[] >>
  pop_assum SUBST1_TAC >> irule CARD_le_LENGTH >>
  simp[SUBSET_DEF, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
  ‘is_conn (gstate ifds (srelabel m) s0 n) x’ by metis_tac[] >>
  drule_all conn_arrived >> strip_tac >>
  qexists_tac ‘Connect l x’ >> simp[Abbr ‘P’, Abbr ‘A’]
QED

(* ------------------------------------------------------------------------
   Prompt accepts
   ------------------------------------------------------------------------ *)

Theorem MEM_wacc[local]:
  ∀ps. MEM d (wacc ps) ⇒ ∃l. MEM (Accept l, Accepted (SOME d)) ps
Proof
  Induct >> simp[wacc_def] >> PairCases >> simp[wacc_def] >>
  every_case_tac >> rw[] >> metis_tac[]
QED

Theorem event_accepts_accept[local]:
  event_accepts d (act_event (Accept l) (Accepted (SOME d)))
Proof
  simp[act_event_def, event_accepts_def] >>
  ‘LENGTH (1w :: fd_bytes d) = LENGTH (REPLICATE 9 (0w : word8))’ by simp[] >>
  simp[MAP_ZIP]
QED

(* MAIN: a connection that arrived within the first n steps is handed out
   by round n + 3 * nconnects n s0 *)
Theorem chat_accept_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ connects_upto d n s0 ⇒
  ∃N. N ≤ n + 3 * nconnects n s0 ∧
      MEM d (wacc (SPg (chat_server lfdn) (EI lfdn) s0 N))
Proof
  rw[connects_upto_def] >>
  ‘grun_ok (EI lfdn) (srelabel (chat_server lfdn)) s0’
    by metis_tac[gen_grun_ok, chat_uses_ok_v] >>
  ‘is_conn (gstate (EI lfdn) (srelabel (chat_server lfdn)) s0 n) d’
    by metis_tac[connects_is_conn] >>
  qspecl_then [‘EI lfdn’, ‘srelabel (chat_server lfdn)’, ‘s0’, ‘n2w lfdn’] mp_tac
    (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfd’] grounds_known) >>
  simp[] >> disch_then (qspec_then ‘n’ (strip_assume_tac o CONJUNCT2)) >>
  fs[known_def] >> first_x_assum drule >> strip_tac
  >- (qexists_tac ‘n’ >> simp[]) >>
  ‘LENGTH (lq (n2w lfdn) (gstate (EI lfdn) (srelabel (chat_server lfdn)) s0 n)) ≤
   nconnects n s0’ by (irule lq_nconnects >> simp[chat_uses_ok_v]) >>
  qpat_x_assum ‘MEM d (lq _ _)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  qspecl_then [‘s0’, ‘lfdn’, ‘d’, ‘chat_server lfdn’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘M’] m_queue_progress_at) >>
  impl_tac >- simp[wf_chat_server, chat_accepts_progress, chat_uses_ok_v] >>
  disch_then (qspecl_then [‘LENGTH l1’, ‘n’] mp_tac) >>
  impl_tac >- (rw[queued_def] >> qexistsl_tac [‘l1’, ‘l2’] >> simp[]) >>
  strip_tac >>
  qexists_tac ‘N’ >> gvs[]
QED

(* MAIN: chat_accept_prompt 3, for the loop's trace *)
Theorem chat_accept_trace:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ connects_upto d n s0 ⇒
  ∃evs. LPREFIX (fromList evs)
          (LFLATTEN (LGENLIST
             (λi. fromList (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0 i))
             NONE)) ∧
        polls evs ≤ n + 3 * nconnects n s0 ∧
        EXISTS (event_accepts d) evs
Proof
  strip_tac >> drule_all chat_accept_rounds >> strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel (chat_server lfdn)) s0’
    by metis_tac[gen_grun_ok, chat_uses_ok_v] >>
  qexists_tac ‘FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0) N)’ >>
  simp[rounds_LPREFIX] >>
  conj_tac >- (drule polls_rounds >> simp[]) >>
  drule MEM_wacc >> strip_tac >> rename1 ‘MEM (Accept l0, _) _’ >>
  drule_then (qspec_then ‘N’ assume_tac) FILTER_rounds >>
  ‘MEM (act_event (Accept l0) (Accepted (SOME d)))
     (FILTER np (FLAT (GENLIST (grounds_events (EI lfdn)
                                  (srelabel (chat_server lfdn)) s0) N)))’
    by (pop_assum SUBST1_TAC >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  gvs[MEM_FILTER, EXISTS_MEM] >> first_assum (irule_at Any) >>
  simp[event_accepts_accept]
QED
