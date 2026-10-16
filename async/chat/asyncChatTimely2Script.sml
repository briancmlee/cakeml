(*
  The revised ChatSpecTimely clauses (review T1, T2) for the loop's trace
  of the chat server:

   - chat_read_trace (T1): the complete lines c sent within n steps are
     read by poll n + 4 (1 + nconnects n + |sent|): c is accepted by round
     n + 3 nconnects n (chat_accept_rounds), and then its reader reads at
     least one byte every 4 rounds (chat_reads);
   - chat_accept_backlog (T2): at the n-th poll, a connection that arrived
     within n steps is accepted within 3 polls per connection still
     waiting.  The prefix ending with the n-th poll is the first n rounds
     (rounds_at_poll); its accept events are the connections handed out
     (naccepts_rounds); and those, with the listener's queue, are no more
     than the connections that arrived (acc_lq_nconnects).
*)
Theory asyncChatTimely2
Ancestors
  pair list rich_list arithmetic option string words llist alist pred_set
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncM4ServerUses asyncRunOkGen asyncM4GRounds asyncM4SockModel
  asyncM4SockInv asyncM4GTrans asyncM4Sched asyncM4Queue asyncM4LiveWorld
  asyncM4Account asyncM4ReadSoon asyncM3World ffiSpikeSocketFFI
  ffiSpikeSocketFair EchoSpec HttpSpec ChatSpec ChatSpecTimely
  ChatSpecTimelyBite asyncServerV asyncServerVLive asyncServerVLiveA
  asyncServerVAcceptAt asyncWithTap asyncChatSW asyncChatModel asyncChatSafe
  asyncChatTrace asyncChatLiveV asyncChatLiveCoverRun asyncChatLiveAccept
  asyncChatLiveRead asyncChatLiveReads asyncChatLiveReadRun asyncChatTimely
  asyncProgress asyncM4AcceptSoon asyncM4Drain asyncServerWithLive asyncWithStore
Libs
  preamble

Overload TRc = “λlfdn s0. LFLATTEN (LGENLIST
   (λi. fromList (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0 i)) NONE)”

(* ------------------------------------------------------------------------
   The prefix that ends with the n-th poll is the first n rounds
   ------------------------------------------------------------------------ *)

Theorem prefix_snoc[local]:
  evs ≼ P ++ [x] ⇒ evs = P ++ [x] ∨ evs ≼ P
Proof
  rw[IS_PREFIX_APPEND] >> Cases_on ‘l’ using SNOC_CASES >> gvs[] >>
  disj2_tac >> qexists_tac ‘l'’ >>
  metis_tac[SNOC_APPEND, SNOC_11, APPEND_ASSOC]
QED

Theorem act_event_not_poll[local]:
  ¬is_poll (act_event a r)
Proof
  Cases_on ‘a’ >> Cases_on ‘r’ >> simp[act_event_def, is_poll_def]
QED

Theorem round_events_shape[local]:
  grun_ok ifds m s0 ⇒
  ∃A p. grounds_events ifds m s0 i = A ++ [p] ∧ EVERY (λe. ¬is_poll e) A
Proof
  strip_tac >> drule grun_ok_sock_acts >>
  disch_then (qspec_then ‘i’ strip_assume_tac) >>
  drule sock_acts_events >> strip_tac >>
  simp[grounds_events_alt, sock_acts_tot_def] >>
  simp[EVERY_EL] >> gvs[EL_MAP2, act_event_not_poll]
QED

Theorem rounds_at_poll:
  grun_ok ifds m s0 ∧
  LPREFIX (fromList evs0)
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events ifds m s0 i)) NONE)) ∧
  (evs0 ≠ [] ⇒ is_poll (LAST evs0)) ⇒
  evs0 = FLAT (GENLIST (grounds_events ifds m s0) (polls evs0))
Proof
  strip_tac >>
  ‘∀i. grounds_events ifds m s0 i ≠ []’ by simp[grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘∃A p. grounds_events ifds m s0 n = A ++ [p] ∧ EVERY (λe. ¬is_poll e) A’
    by metis_tac[round_events_shape] >>
  qpat_x_assum ‘FLAT _ ≼ evs0’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
  rename1 ‘evs0 = FLAT (GENLIST _ n) ++ x’ >>
  ‘x ≼ A ++ [p]’
    by (qpat_x_assum ‘evs0 ≼ _’ mp_tac >>
        asm_rewrite_tac[GENLIST, SNOC_APPEND, FLAT_APPEND, GSYM APPEND_ASSOC] >>
        rw[IS_PREFIX_APPEND] >> metis_tac[APPEND_11, APPEND_ASSOC]) >>
  ‘evs0 = FLAT (GENLIST (grounds_events ifds m s0) n) ∨
   evs0 = FLAT (GENLIST (grounds_events ifds m s0) (SUC n))’
    by (drule prefix_snoc >> strip_tac
        >- (disj2_tac >> simp[GENLIST, SNOC_APPEND, FLAT_APPEND])
        >> Cases_on ‘x = []’ >- simp[] >>
        ‘is_poll (LAST x)’
          by (qpat_x_assum ‘_ ≠ [] ⇒ _’ mp_tac >> simp[LAST_APPEND_NOT_NIL]) >>
        ‘MEM (LAST x) A’
          by (fs[IS_PREFIX_APPEND] >> ‘MEM (LAST x) x’ by simp[LAST_MEM] >> simp[]) >>
        fs[EVERY_MEM] >> metis_tac[]) >>
  drule polls_rounds >> strip_tac >> gvs[] >>
  qpat_x_assum ‘FLAT (GENLIST _ (SUC n)) = _’ (SUBST_ALL_TAC o SYM) >> simp[]
QED

(* ------------------------------------------------------------------------
   Its accept events are the connections handed out
   ------------------------------------------------------------------------ *)

Theorem is_accept_act[local]:
  is_accept_ev (act_event a r) ⇔ ∃l c. a = Accept l ∧ r = Accepted (SOME c)
Proof
  Cases_on ‘a’ >> Cases_on ‘r’ >> TRY (rename1 ‘Accepted oc’ >> Cases_on ‘oc’) >>
  simp[asyncM3WorldTheory.act_event_def, is_accept_ev_def] >> EVAL_TAC
QED

Theorem accepts_wacc[local]:
  ∀ps. LENGTH (FILTER is_accept_ev (MAP aev ps)) = LENGTH (wacc ps)
Proof
  Induct >> simp[wacc_def] >> PairCases >> simp[wacc_def, is_accept_act] >>
  Cases_on ‘h0’ >> Cases_on ‘h1’ >> simp[] >>
  TRY (rename1 ‘Accepted oc’ >> Cases_on ‘oc’) >> simp[]
QED

Theorem accept_np[local]:
  is_accept_ev e ⇒ np e
Proof
  Cases_on ‘e’ >> rename1 ‘IO_event f _ _’ >> Cases_on ‘f’ >>
  simp[is_accept_ev_def, np_def] >> rw[] >> simp[]
QED

Theorem naccepts_rounds:
  grun_ok ifds m s0 ⇒
  naccepts (FLAT (GENLIST (grounds_events ifds m s0) n)) = LENGTH (wacc (gperf ifds m s0 n))
Proof
  strip_tac >>
  ‘FILTER is_accept_ev (FLAT (GENLIST (grounds_events ifds m s0) n)) =
   FILTER is_accept_ev (FILTER np (FLAT (GENLIST (grounds_events ifds m s0) n)))’
    by (simp[FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
        simp[FUN_EQ_THM] >> metis_tac[accept_np]) >>
  drule FILTER_rounds >> disch_then (qspec_then ‘n’ assume_tac) >>
  simp[ChatSpecTimelyTheory.naccepts_def] >>
  qpat_x_assum ‘FILTER is_accept_ev _ = _’ SUBST1_TAC >>
  qpat_x_assum ‘FILTER np _ = _’ SUBST1_TAC >> simp[accepts_wacc]
QED

(* ------------------------------------------------------------------------
   Handed out and waiting: no more than arrived
   ------------------------------------------------------------------------ *)

Theorem CARD_le_LENGTH[local]:
  ALL_DISTINCT q ∧ set q ⊆ set L ⇒ LENGTH q ≤ LENGTH L
Proof
  strip_tac >>
  ‘LENGTH q = CARD (set q)’ by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  ‘CARD (set q) ≤ CARD (set L)’ by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (set L) ≤ LENGTH L’ by simp[CARD_LIST_TO_SET] >>
  simp[]
QED

Theorem acc_lq_nconnects:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  LENGTH (wacc (SPg m ifds s0 n)) + LENGTH (lq (n2w lfdn) (gstate ifds (srelabel m) s0 n)) ≤
  nconnects n s0
Proof
  strip_tac >>
  ‘grun_ok ifds (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  drule_all gen_sinv >> disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  gvs[sinv_def, lq_def, nconnects_def] >>
  qmatch_goalsub_abbrev_tac ‘LENGTH (FILTER P A)’ >>
  ‘LENGTH (FILTER P A) =
   LENGTH (MAP (λa. case a of Connect l c => c | _ => 0w) (FILTER P A))’ by simp[] >>
  pop_assum SUBST1_TAC >>
  irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (wacc (SPg m ifds s0 n) ++ q)’ >>
  conj_tac >- simp[] >>
  irule CARD_le_LENGTH >>
  simp[SUBSET_DEF, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
  ‘is_conn (gstate ifds (srelabel m) s0 n) x’ by metis_tac[] >>
  drule_all conn_arrived >> strip_tac >>
  qexists_tac ‘Connect l x’ >> simp[Abbr ‘P’, Abbr ‘A’]
QED

(* ------------------------------------------------------------------------
   T2: prompt accepts, against the backlog
   ------------------------------------------------------------------------ *)

Theorem chat_accept_backlog_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ connects_upto d n s0 ⇒
  ∃N. N ≤ n + 3 * (nconnects n s0 − LENGTH (wacc (SPg (chat_server lfdn) (EI lfdn) s0 n))) ∧
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
  ‘LENGTH (wacc (SPg (chat_server lfdn) (EI lfdn) s0 n)) +
   LENGTH (lq (n2w lfdn) (gstate (EI lfdn) (srelabel (chat_server lfdn)) s0 n)) ≤
   nconnects n s0’ by (irule acc_lq_nconnects >> simp[chat_uses_ok_v]) >>
  qpat_x_assum ‘MEM d (lq _ _)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  qspecl_then [‘s0’, ‘lfdn’, ‘d’, ‘chat_server lfdn’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘M’] m_queue_progress_at) >>
  impl_tac >- simp[wf_chat_server, chat_accepts_progress, chat_uses_ok_v] >>
  disch_then (qspecl_then [‘LENGTH l1’, ‘n’] mp_tac) >>
  impl_tac >- (rw[queued_def] >> qexistsl_tac [‘l1’, ‘l2’] >> simp[]) >>
  strip_tac >> qexists_tac ‘N’ >> gvs[]
QED

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

(* An accepted connection, as an event of the first N rounds *)
Theorem accept_in_rounds[local]:
  grun_ok (EI lfdn) (srelabel (chat_server lfdn)) s0 ∧
  MEM d (wacc (SPg (chat_server lfdn) (EI lfdn) s0 N)) ⇒
  EXISTS (event_accepts d)
    (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0) N))
Proof
  strip_tac >> drule MEM_wacc >> strip_tac >> rename1 ‘MEM (Accept l0, _) _’ >>
  drule_then (qspec_then ‘N’ assume_tac) FILTER_rounds >>
  ‘MEM (act_event (Accept l0) (Accepted (SOME d)))
     (FILTER np (FLAT (GENLIST (grounds_events (EI lfdn)
                                  (srelabel (chat_server lfdn)) s0) N)))’
    by (pop_assum SUBST1_TAC >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  gvs[MEM_FILTER, EXISTS_MEM] >> first_assum (irule_at Any) >>
  simp[event_accepts_accept]
QED

(* MAIN (T2): chat_accept_prompt 3, for the loop's trace *)
Theorem chat_accept_backlog:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ connects_upto d n s0 ∧
  LPREFIX (fromList evs0) (TRc lfdn s0) ∧ polls evs0 = n ∧
  (evs0 ≠ [] ⇒ is_poll (LAST evs0)) ⇒
  ∃evs. LPREFIX (fromList evs) (TRc lfdn s0) ∧
        polls evs ≤ n + 3 * (nconnects n s0 − naccepts evs0) ∧
        EXISTS (event_accepts d) evs
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel (chat_server lfdn)) s0’
    by metis_tac[gen_grun_ok, chat_uses_ok_v] >>
  ‘evs0 = FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0) n)’
    by (drule_all rounds_at_poll >> simp[]) >>
  ‘naccepts evs0 = LENGTH (wacc (SPg (chat_server lfdn) (EI lfdn) s0 n))’
    by (qpat_x_assum ‘evs0 = _’ SUBST1_TAC >> irule naccepts_rounds >> simp[]) >>
  drule_all chat_accept_backlog_rounds >> strip_tac >>
  qexists_tac ‘FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0) N)’ >>
  simp[rounds_LPREFIX] >>
  conj_tac >- (drule polls_rounds >> simp[]) >>
  irule accept_in_rounds >> simp[]
QED

(* ------------------------------------------------------------------------
   T1: prompt reads
   ------------------------------------------------------------------------ *)

Theorem MAP_prefix_l[local]:
  ∀s t. s ≼ t ⇒ MAP f s ≼ MAP f t
Proof
  Induct >> simp[] >> Cases_on ‘t’ >> simp[]
QED

Theorem bytes_of_bytes[local]:
  ∀l : word8 list. bytes (MAP (CHR o w2n) l) = l
Proof
  simp[bytes_def, bytes_round_trip]
QED

(* MAIN (T1): chat_read_prompt 4, for the loop's trace *)
Theorem chat_read_trace:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  ∃evs. LPREFIX (fromList evs) (TRc lfdn s0) ∧
        polls evs ≤ n + 4 * (1 + nconnects n s0 + LENGTH (sent_upto c n s0)) ∧
        whole_lines (sent_upto c n s0) ≼ bytes_read_from c evs
Proof
  strip_tac >>
  Cases_on ‘sent_upto c n s0 = []’
  >- (qexists_tac ‘[]’ >> simp[whole_lines_def, bytes_read_from_def, polls_def]) >>
  qabbrev_tac ‘M = chat_server lfdn’ >>
  ‘uses_ok lfdn M’ by simp[Abbr ‘M’, chat_uses_ok_v] >>
  ‘grun_ok (EI lfdn) (srelabel M) s0’ by metis_tac[gen_grun_ok] >>
  ‘is_conn (gstate (EI lfdn) (srelabel M) s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  ‘connects_upto c n s0’
    by (simp[connects_upto_def] >>
        qpat_x_assum ‘grun_ok _ _ _’ assume_tac >>
        drule conn_arrived >> simp[] >> disch_then drule >> simp[]) >>
  ‘∃N0. N0 ≤ n + 3 * nconnects n s0 ∧ MEM c (wacc (SPg M (EI lfdn) s0 N0))’
    by (simp[Abbr ‘M’] >> irule chat_accept_rounds >> simp[]) >>
  qabbrev_tac ‘n1 = n + 3 * nconnects n s0’ >>
  ‘MEM c (wacc (SPg M (EI lfdn) s0 n1))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[Abbr ‘n1’]) >>
  qabbrev_tac ‘D = MAP (CHR o w2n) (sent_upto c n s0)’ >>
  ‘bytes D = sent_upto c n s0’ by simp[Abbr ‘D’, bytes_of_bytes] >>
  ‘bytes D ≼ sent_upto c n1 s0’
    by (qpat_x_assum ‘bytes D = _’ SUBST1_TAC >> simp[Abbr ‘n1’, sent_upto_prefix]) >>
  qabbrev_tac ‘N = n1 + 4 * (LENGTH D + 1)’ >>
  qspecl_then [‘lfdn’, ‘s0’, ‘c’, ‘EI lfdn’, ‘n1’, ‘N’] mp_tac
    (Q.GENL [‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’, ‘N’] chat_view_s) >>
  impl_tac >- fs[Abbr ‘M’, Abbr ‘N’] >> strip_tac >>
  (* the socket world gives the handler its environment *)
  ‘interest_covers (EI lfdn) (srelabel M) s0’ by simp[interest_covers_EI] >>
  qspecl_then [‘lfdn’, ‘M’, ‘s0’, ‘EI lfdn’, ‘c’, ‘n1’, ‘D’, ‘a’, ‘g’, ‘N’,
               ‘chtr (w2n c)’] mp_tac
    (Q.GENL [‘lfdn’, ‘M’, ‘s0’, ‘ifds’, ‘c’, ‘n’, ‘D’, ‘a’, ‘g’, ‘N’, ‘t’] m_view_henv) >>
  impl_tac >- fs[Abbr ‘M’] >> strip_tac >>
  (* so it reads all of D *)
  qspecl_then [‘LENGTH D’, ‘n1 − a’] mp_tac
    (chat_reads |> Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘j0’ |-> ‘n1 − a’]) >>
  impl_tac >- fs[Abbr ‘N’] >> strip_tac >>
  qexists_tac ‘FLAT (GENLIST (grounds_events (EI lfdn) (srelabel M) s0) (a + j'))’ >>
  simp[rounds_LPREFIX] >>
  conj_tac
  >- (drule polls_rounds >> disch_then (qspec_then ‘a + j'’ SUBST1_TAC) >>
      ‘LENGTH D = LENGTH (sent_upto c n s0)’ by simp[Abbr ‘D’] >>
      fs[Abbr ‘N’, Abbr ‘n1’]) >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
  simp[whole_lines_prefix] >>
  qpat_x_assum ‘bytes D = _’ (SUBST1_TAC o SYM) >>
  qspecl_then [‘lfdn’, ‘M’, ‘s0’, ‘c’, ‘a + j'’, ‘EI lfdn’] mp_tac
    (Q.GENL [‘lfdn’, ‘m’, ‘s0’, ‘c’, ‘n’, ‘ifds’] gen_rounds_bytes) >>
  impl_tac >- fs[] >> strip_tac >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd _) _ = _’ (qspec_then ‘j'’ mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  ‘read (w2n c) (TSg M (EI lfdn) s0 (a + j')) = read (w2n c) (chtr (w2n c) (TAKE j' g))’
    by (qpat_x_assum ‘FILTER _ _ = chtr _ _’ (SUBST1_TAC o SYM) >>
        simp[read_FILTER, Abbr ‘M’]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum ‘D ≼ hread_t _ _ _ _’ mp_tac >>
  simp[hread_t_def, bytes_def] >> strip_tac >>
  irule MAP_prefix_l >> first_assum ACCEPT_TAC
QED
