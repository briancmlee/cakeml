(*
  ChatSpec's second liveness clause (reads) for the loop's trace of the
  chat server: every complete line a client sends is eventually read.

  If c sent data by step n, c is a connection of the world (grounds_acct),
  the server hands it out (chat_conn_accepted), the library gives its
  handler the view and the socket environment (view_wrap_ans, m_view_henv),
  and the handler reads all of it (chat_reads).
*)
Theory asyncChatLiveReadRun
Ancestors
  pair list rich_list arithmetic option string words llist
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncM4ServerUses asyncRunOkGen asyncM4GRounds
  asyncM4SockModel asyncM4GTrans asyncM4Sched asyncM4Account asyncM4Drain
  asyncM4AcceptSoon asyncM4ReadSoon EchoSpec HttpSpec ChatSpec
  ffiSpikeSocketFFI ffiSpikeSocketFair asyncServerV asyncServerVLive
  asyncServerVLiveA asyncServerWithLive asyncWithStore asyncWithTap
  asyncChatSW asyncChatModel asyncChatSafe asyncChatTrace asyncChatLiveV
  asyncChatLiveRead asyncChatLiveReads
Libs
  preamble

Overload CWr = “with_tap chat_tap chat_delta empty_store”
Overload CIn = “tap_hist chat_tap chat_delta empty_store”

Theorem dropWhile_suffix[local]:
  ∀l. ∃t. l = t ++ dropWhile P l
Proof
  Induct >> simp[] >> rw[] >> fs[] >> metis_tac[APPEND]
QED

Theorem whole_lines_prefix:
  whole_lines bs ≼ bs
Proof
  simp[whole_lines_def] >>
  strip_assume_tac (Q.GEN ‘P’ dropWhile_suffix |> Q.ISPEC ‘λb : word8. b ≠ 10w’
                    |> Q.SPEC ‘REVERSE bs’) >>
  ‘bs = REVERSE (REVERSE bs)’ by simp[] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[REVERSE_APPEND]
QED

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

(* The library's view of a handler, with the socket world's side *)
Theorem chat_view_s:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (chat_server lfdn) ifds s0 n)) ∧ n ≤ N ⇒
  ∃a (g : (event, (canswer, asyncServer$response) kres) snapshot list).
    a ≤ n ∧ LENGTH g + a = N ∧ prompt (chat_handler (w2n c)) g ∧
    (∀i. i < LENGTH g ⇒
         (EL i g).ready =
         (EL (a + i) (MAP sfs (ghist ifds (srelabel (chat_server lfdn)) s0 N))).ready) ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd (w2n c)) (TSg (chat_server lfdn) ifds s0 (a + j)) =
      chtr (w2n c) (TAKE j g)
Proof
  rw[chat_server_v] >>
  qspecl_then [‘chatV’,
               ‘CWr’,
               ‘CIn’, ‘chat_handler’, ‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’, ‘N’]
    mp_tac (Q.GENL [‘V’, ‘Wr’, ‘inner’, ‘hf’, ‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’, ‘N’]
              view_wrap_ans) >>
  simp[wrap_ok_with_tap, vocab_ok_chatV, hokv_chat_handler] >>
  strip_tac >> qexistsl [‘a’, ‘g’] >> simp[]
QED

(* MAIN: ChatSpec's reads clause, for the loop's trace *)
Theorem chat_live_reads:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  ∃evs. LPREFIX (fromList evs)
          (LFLATTEN (LGENLIST
             (λi. fromList (grounds_events (EI lfdn) (srelabel (chat_server lfdn)) s0 i))
             NONE)) ∧
        whole_lines (sent_upto c n s0) ≼ bytes_read_from c evs
Proof
  strip_tac >>
  Cases_on ‘sent_upto c n s0 = []’
  >- (qexists_tac ‘[]’ >> simp[whole_lines_def, bytes_read_from_def]) >>
  qabbrev_tac ‘M = chat_server lfdn’ >>
  ‘uses_ok lfdn M’ by simp[Abbr ‘M’, chat_uses_ok_v] >>
  ‘grun_ok (EI lfdn) (srelabel M) s0’ by metis_tac[gen_grun_ok] >>
  ‘is_conn (gstate (EI lfdn) (srelabel M) s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  ‘∃N0. MEM c (wacc (SPg M (EI lfdn) s0 N0))’
    by (simp[Abbr ‘M’] >> irule chat_conn_accepted >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘n1 = n + N0’ >>
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
