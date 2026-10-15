(*
  The chat server as an instance of the library's skeleton (library-liveness):

   - chatV: the vocabulary Sock sact | Kv (fd, query), responses SockR | KvR;
   - cserver_with = server_v chatV (cserver_with_eq_v), so
       chat_server lfd = with_tap chat_tap chat_delta empty_store
                           (server_v chatV chat_handler lfd);
   - with_tap is a wrapper in the library's sense (wrap_ok_with_tap), for
     any tap and query step: it shows the socket part of m, runs m on the
     inner history tap_hist, and keeps prompt answering;
   - chat_handler fits the library's handler conditions (hokv).

  From these the library gives, for free: the chat server keeps accepting
  (chat_accepts_progress), uses the socket API correctly, every connection
  in the world is eventually accepted (chat_conn_accepted), and the view of
  each connection's handler (chat_view).
*)
Theory asyncChatLiveV
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncM4ServerUses asyncRunOkGen asyncM4GRounds
  asyncM4SockModel ffiSpikeSocketFFI
  asyncServerV asyncServerVProgress asyncServerVLive
  asyncWithStore asyncWithTap asyncChatSW asyncChatModel asyncChatSafe
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The vocabulary
   ------------------------------------------------------------------------ *)

Definition chatV_def:
  chatV : ((asyncServer$action, num # cquery) kact, canswer, num # cquery,
           (canswer, asyncServer$response) kres) vocab =
    <| acc := (λl. Sock (Accept l)); rd := (λfd. Sock (Read fd));
       wr := (λfd d. Sock (Write fd d)); qry := Kv;
       sact := (λa. case a of Sock x => SOME x | Kv q => NONE);
       rinj := SockR;
       sres := (λr. case r of SockR y => SOME y | KvR b => NONE);
       kans := (λr. case r of KvR b => SOME b | SockR y => NONE);
       owner := (λa. case a of
                       Sock (Read fd) => SOME fd
                     | Sock (Write fd d) => SOME fd
                     | Sock (Accept l) => NONE
                     | Kv q => SOME (FST q)) |>
End

Theorem vocab_ok_chatV:
  vocab_ok chatV
Proof
  rw[vocab_ok_def, chatV_def] >> every_case_tac >> gvs[]
QED

Theorem vocab_qok_chatV:
  vocab_qok chatV
Proof
  rw[vocab_qok_def, chatV_def]
QED

(* MAIN: the chat skeleton is the library's skeleton *)
Theorem cserver_with_eq_v:
  cserver_with h = server_v chatV h
Proof
  simp[cserver_with_def, server_v_def] >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, cserver_with_body_def, server_v_body_def, chatV_def] >>
  rpt gen_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> rpt gen_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> Cases >>
  simp[vaccd_def] >> every_case_tac >> simp[]
QED

Theorem chat_server_v:
  chat_server lfd =
  with_tap chat_tap chat_delta empty_store (server_v chatV chat_handler lfd)
Proof
  simp[chat_server_def, chat_inner_def, cserver_with_eq_v]
QED

(* ------------------------------------------------------------------------
   with_tap is a wrapper
   ------------------------------------------------------------------------ *)

Theorem untag_sproj:
  ∀tr. untag tr = sproj chatV tr
Proof
  simp[untag_def, sproj_def, chatV_def] >> gen_tac >> AP_TERM_TAC >>
  simp[MAP_EQ_f, FORALL_PROD] >> Cases >> simp[] >>
  Cases >> simp[] >> rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[]
QED

Theorem socks_sacts:
  ∀acts. socks acts = sacts chatV acts
Proof
  simp[socks_def, sacts_def, chatV_def] >> gen_tac >> AP_TERM_TAC >>
  simp[MAP_EQ_f] >> Cases >> simp[]
QED

Theorem LENGTH_merge[local]:
  ∀acts rs ans.
    LENGTH (socks acts) ≤ LENGTH rs ∧ LENGTH (queries acts) ≤ LENGTH ans ⇒
    LENGTH acts ≤ LENGTH (merge acts rs ans)
Proof
  Induct >> simp[merge_def] >> Cases >> rpt gen_tac >>
  simp[merge_def, socks_def, queries_def] >>
  every_case_tac >> simp[] >> gvs[GSYM socks_def, GSYM queries_def]
QED

(* If the world answers with_tap's actions promptly, m's actions are
   answered promptly too (its queries by the tap) *)
Theorem prompt_with_tap:
  wf m ∧ prompt (with_tap σ δ s0 m) h ⇒ prompt m (tap_hist σ δ s0 m h)
Proof
  rw[prompt_def] >> first_x_assum drule >>
  simp[new_actions_with_tap, tap_hist_TAKE, responses_at_def] >>
  simp[EL_tap_hist] >> strip_tac >>
  irule LENGTH_merge >> simp[]
QED

Theorem ready_tap_hist:
  ∀h i. i < LENGTH h ⇒ (EL i (tap_hist σ δ s0 m h)).ready = (EL i h).ready
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rw[SNOC_APPEND, tap_hist_SNOC] >>
  Cases_on ‘i < LENGTH h’ >> gvs[EL_APPEND1, EL_APPEND2] >>
  ‘i = LENGTH h’ by simp[] >> gvs[]
QED

(* MAIN: with_tap is a wrapper in the library's sense, for chatV *)
Theorem wrap_ok_with_tap:
  wrap_ok chatV (with_tap σ δ s0) (tap_hist σ δ s0)
Proof
  rw[wrap_ok_def, wf_with_tap, trans_with_tap, untag_sproj, prompt_with_tap,
     ready_tap_hist, tap_hist_TAKE]
  >> simp[with_tap_def, socks_sacts]
QED

(* ------------------------------------------------------------------------
   The handler
   ------------------------------------------------------------------------ *)

Theorem hokv_chat_handler:
  hokv chatV chat_handler
Proof
  rw[hokv_def, wf_chat_handler, settled_chat_handler] >>
  irule EVERY_MONOTONIC >> qexists ‘on_fdc fd’ >> simp[chat_handler_on_fdc] >>
  PairCases >> Cases_on ‘x0’ >>
  simp[on_fdc_def, on_fd_v_def, chatV_def, on_fd_def] >> rw[] >> simp[] >>
  rename1 ‘Sock a’ >> Cases_on ‘a’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   What the library gives
   ------------------------------------------------------------------------ *)

Theorem chat_accepts_progress:
  accepts_progress lfd (chat_server lfd)
Proof
  simp[chat_server_v] >> irule accepts_progress_wrap >>
  simp[vocab_ok_chatV, hokv_chat_handler] >>
  metis_tac[wrap_ok_with_tap]
QED

Theorem chat_uses_ok_v:
  uses_ok lfd (chat_server lfd)
Proof
  simp[chat_server_v] >> irule uses_ok_wrap >>
  simp[vocab_ok_chatV, hokv_chat_handler] >>
  metis_tac[wrap_ok_with_tap]
QED

(* MAIN: every connection in the world is eventually accepted *)
Theorem chat_conn_accepted:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  is_conn (gstate (EI lfdn) (srelabel (chat_server lfdn)) s0 n) c ⇒
  ∃N. MEM c (wacc (SPg (chat_server lfdn) (EI lfdn) s0 N))
Proof
  strip_tac >> irule m_conn_accepted >>
  simp[wf_chat_server, chat_accepts_progress, chat_uses_ok_v] >>
  metis_tac[]
QED
