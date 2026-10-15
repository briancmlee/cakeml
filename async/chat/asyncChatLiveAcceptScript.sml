(*
  ChatSpec's first liveness clause for the loop's trace of the chat server:
  every connection that arrives in the schedule is eventually accepted, as
  an event of the trace.

   - connects_is_conn (the world): a Connect in the first n steps of the
     schedule makes the connection known to the world by round n;
   - chat_conn_accepted (asyncChatLiveV, from the library): a known
     connection is eventually handed out by the server's accept;
   - chat_live_accepts: the accept is an event of a prefix of the trace.
*)
Theory asyncChatLiveAccept
Ancestors
  pair list rich_list arithmetic option words llist
  asyncCore asyncLevel1 asyncServer asyncServerSafety ffiSpikeSocketFFI
  ffiSpikeSocketFair EchoSpec ChatSpec asyncM3World asyncM4GRounds
  asyncM4SockInv asyncM4SockModel asyncM4GTrans asyncM4Sched asyncM4Account
  asyncM4LiveWorld asyncM4ReadSoon asyncRunOkGen asyncServerVLive
  asyncChatModel asyncChatTrace asyncChatLiveV
Libs
  preamble

(* ------------------------------------------------------------------------
   The world: arrivals become connections, and connections stay
   ------------------------------------------------------------------------ *)

Theorem step_conn[local]:
  ∀as s. step_ok s as ∧ MEM (Connect l d) as ⇒ is_conn (FOLDL deliver1 s as) d
Proof
  Induct >> simp[step_ok_def] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (‘∃cn. ALOOKUP (deliver1 s (Connect l d)).conns d = SOME cn’
        by gvs[arrival_ok_def, deliver1_def] >>
      drule deliver_conn_s >> disch_then (qspec_then ‘as’ strip_assume_tac) >>
      simp[is_conn_def]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem tick_conn[local]:
  step_ok s (next_step s) ∧ MEM (Connect l d) (next_step s) ⇒ is_conn (tick s) d
Proof
  rw[tick_def, next_step_def] >> Cases_on ‘LHD s.sched’ >> gvs[deliver_def] >>
  irule step_conn >> simp[step_ok_sched] >> metis_tac[]
QED

Theorem gstate_conn_SUC[local]:
  grun_ok ifds m s0 ∧ is_conn (gstate ifds m s0 n) d ⇒
  is_conn (gstate ifds m s0 (SUC n)) d
Proof
  rw[is_conn_def] >> Cases_on ‘ALOOKUP (gstate ifds m s0 n).conns d’ >> gvs[] >>
  drule_all round_conn_s >> strip_tac >> simp[]
QED

(* MAIN: a connection that arrives in the first n steps is known to the
   world by round n *)
Theorem connects_is_conn:
  grun_ok ifds m s0 ∧ sched_wf s0 ⇒
  ∀n. (∃l. MEM (Connect l d) (arrivals_upto n s0.sched)) ⇒
      is_conn (gstate ifds m s0 n) d
Proof
  strip_tac >> Induct >- simp[arrivals_upto_def] >>
  rpt strip_tac >>
  qspecl_then [‘n’, ‘1’] mp_tac grounds_arrivals >>
  ‘n + 1 = SUC n’ by simp[] >> simp[] >> strip_tac >>
  ‘arrivals_upto 1 (gstate ifds m s0 n).sched = next_step (gmid ifds m s0 n)’
    by (REWRITE_TAC[ONE, arrivals_upto_def] >>
        simp[next_step_def, gmid_sched] >> CASE_TAC >> simp[arrivals_upto_def]) >>
  gvs[]
  >- (irule gstate_conn_SUC >> simp[] >> first_x_assum irule >>
      qexists_tac ‘l’ >> simp[])
  >> simp[gstate_SUC] >> irule tick_conn >>
  conj_tac >- (qexists_tac ‘l’ >> simp[]) >>
  irule grounds_step_ok >> simp[]
QED

(* ------------------------------------------------------------------------
   The trace
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

(* MAIN: ChatSpec's first liveness clause, for the loop's trace: every
   connection the schedule brings is accepted, in some prefix of the trace *)
Theorem chat_live_accepts:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ connects_upto d n s0 ⇒
  ∃evs. LPREFIX (fromList evs)
          (LFLATTEN (LGENLIST
             (λi. fromList (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0 i))
             NONE)) ∧
        EXISTS (event_accepts d) evs
Proof
  rw[connects_upto_def] >>
  ‘grun_ok (EI lfdn) (srelabel (chat_server lfdn)) s0’
    by metis_tac[gen_grun_ok, chat_uses_ok_v] >>
  ‘is_conn (gstate (EI lfdn) (srelabel (chat_server lfdn)) s0 n) d’
    by metis_tac[connects_is_conn] >>
  ‘∃N. MEM d (wacc (SPg (chat_server lfdn) (EI lfdn) s0 N))’
    by (irule chat_conn_accepted >> simp[] >> metis_tac[]) >>
  qexists_tac ‘FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0) N)’ >>
  simp[rounds_LPREFIX] >>
  drule MEM_wacc >> strip_tac >> rename1 ‘MEM (Accept l0, _) _’ >>
  drule_then (qspec_then ‘N’ assume_tac) FILTER_rounds >>
  ‘MEM (act_event (Accept l0) (Accepted (SOME d)))
     (FILTER np (FLAT (GENLIST (grounds_events (EI lfdn)
                                  (srelabel (chat_server lfdn)) s0) N)))’
    by (pop_assum SUBST1_TAC >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  gvs[MEM_FILTER, EXISTS_MEM] >> first_assum (irule_at Any) >>
  simp[event_accepts_accept]
QED
