(*
  ChatSpec's third liveness clause (delivery) for the loop's trace of the
  chat server: whatever a connection is owed at some point of the trace is
  eventually written to it.

   - chat_owed_rounds (asyncChatTrace): what a prefix of the trace owes d
     is what a prefix of the model transcript owes it, at the next round
     boundary R;
   - chat_cover (asyncChatLiveCoverRun): by some round, the hub has told
     d's writer all of that;
   - chat_live_every (the library's server_v_live_every, with the chat
     handler's push obligation): what the writer was told is eventually
     written.
*)
Theory asyncChatLiveDeliverRun
Ancestors
  pair list rich_list arithmetic option string words llist
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncM4ServerUses asyncRunOkGen asyncM4GRounds asyncM4SockModel
  asyncM4GTrans EchoSpec HttpSpec ChatSpec ffiSpikeSocketFFI
  asyncServerV asyncServerVLive asyncServerVLiveA asyncServerVPushLive
  asyncSWSock asyncWithStore asyncWithTap asyncChatSW asyncChatModel
  asyncChatSafe asyncChatTrace asyncChatLiveV asyncChatLiveDeliver
  asyncChatLiveCover asyncChatLiveCoverRun
Libs
  preamble

Theorem SPLITP_NIL_SND[local]:
  ∀l. SND (rich_list$SPLITP P l) = [] ⇔ ¬EXISTS P l
Proof
  Induct >> simp[SPLITP] >> rw[]
QED

(* What is owed only grows *)
Theorem owed_m_mono:
  U ≼ V ⇒ owed_m d U ≼ owed_m d V
Proof
  rw[IS_PREFIX_APPEND] >> simp[owed_m_def, SPLITP_APPEND] >>
  Cases_on ‘EXISTS (acc_of d) U’ >> simp[]
  >- (‘SND (SPLITP (acc_of d) U) ≠ []’ by metis_tac[SPLITP_NIL_SND] >>
      Cases_on ‘SPLITP (acc_of d) U’ >> fs[] >> rename1 ‘(U1, U2)’ >>
      Cases_on ‘U2’ >> fs[] >>
      REWRITE_TAC[GSYM IS_PREFIX_APPEND] >>
      irule DROP_prefix >> simp[lines_done_APPEND_prefix])
  >> ‘SND (SPLITP (acc_of d) U) = []’ by metis_tac[SPLITP_NIL_SND] >>
  Cases_on ‘SPLITP (acc_of d) U’ >> fs[]
QED

Theorem owed_m_not_accepted:
  ¬MEM d (accepted U) ⇒ owed_m d U = ""
Proof
  strip_tac >> ‘¬EXISTS (acc_of d) U’ by metis_tac[acc_of_accepted] >>
  ‘SND (SPLITP (acc_of d) U) = []’ by metis_tac[SPLITP_NIL_SND] >>
  simp[owed_m_def] >> Cases_on ‘SPLITP (acc_of d) U’ >> fs[]
QED

(* The library's push liveness, for the chat server *)
Theorem chat_live_every:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (chat_server lfdn) ifds s0 n)) ⇒
  ∀N0. ∃N. bytes (FLAT (cout (DROP 1
                  (conn_answers chatV CWr CIn chat_handler lfdn ifds s0 N0 c)))) ≼
           bytes_written_to c
             (FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0)
                            (SUC N)))
Proof
  rw[chat_server_v] >>
  qspecl_then [‘chatV’, ‘CWr’, ‘CIn’, ‘chat_handler’, ‘λans. cout (DROP 1 ans)’, ‘0’,
               ‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’]
    mp_tac (Q.GENL [‘V’, ‘Wr’, ‘inner’, ‘hf’, ‘out’, ‘B’, ‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’]
              server_v_live_every) >>
  simp[wrap_ok_with_tap, vocab_ok_chatV, hokv_chat_handler, handler_push_live_chat]
QED

Theorem bytes_mono[local]:
  ∀s t. s ≼ t ⇒ bytes s ≼ bytes t
Proof
  Induct >> simp[bytes_def] >> Cases_on ‘t’ >> fs[bytes_def]
QED

(* MAIN: ChatSpec's delivery clause, for the loop's trace *)
Theorem chat_live_deliver:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  LPREFIX (fromList evs)
    (LFLATTEN (LGENLIST
       (λi. fromList (grounds_events ifds (srelabel (chat_server lfdn)) s0 i)) NONE)) ⇒
  ∃evs'. LPREFIX (fromList evs')
           (LFLATTEN (LGENLIST
              (λi. fromList (grounds_events ifds (srelabel (chat_server lfdn)) s0 i))
              NONE)) ∧
         owed d evs ≼ bytes_written_to d evs'
Proof
  strip_tac >>
  ‘∀i. grounds_events ifds (srelabel (chat_server lfdn)) s0 i ≠ []’
    by simp[grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  drule_all chat_owed_rounds >> disch_then (qspec_then ‘d’ strip_assume_tac) >>
  qpat_x_assum ‘owed _ _ = _’ SUBST1_TAC >>
  Cases_on ‘MEM d (wacc (SPg (chat_server lfdn) ifds s0 (SUC n)))’
  >- (drule_all chat_cover >> disch_then (qx_choose_then ‘N0’ assume_tac) >>
      drule_all chat_live_every >> disch_then (qspec_then ‘N0’ strip_assume_tac) >>
      qexists_tac ‘FLAT (GENLIST (grounds_events ifds (srelabel (chat_server lfdn)) s0)
                                 (SUC N))’ >>
      simp[rounds_LPREFIX] >> fs[bytes_def] >>
      irule IS_PREFIX_TRANS >>
      qexists_tac ‘MAP ((n2w : num -> word8) o ORD)
                     (CONCAT (cout (DROP 1 (conn_answers chatV CWr CIn chat_handler
                                              lfdn ifds s0 N0 d))))’ >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule (REWRITE_RULE [bytes_def] bytes_mono) >>
      irule IS_PREFIX_TRANS >>
      qexists_tac ‘owed_m (w2n d) (TSg (chat_server lfdn) ifds s0 (SUC n))’ >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule owed_m_mono >> first_assum ACCEPT_TAC)
  >> qexists_tac ‘evs’ >> conj_tac >- first_assum ACCEPT_TAC >>
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
