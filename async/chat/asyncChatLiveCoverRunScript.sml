(*
  Delivery for the chat server, part 4: in the run, the hub's answers to a
  connection's writer eventually cover what the connection is owed.

  MAIN: chat_cover.  For a connection d accepted by round R, there is a
  round N by which the lines the hub has told d's writer (conn_answers,
  the library's name for its actual answers) contain owed_m d of the
  transcript at round R.  The proof (design/40 §M4):
   - the library's view of d's handler (view_wrap_ans), and the writer's
     view inside it (chat_handler_writer_views);
   - d's accept is answered before its handler starts, so the hub knows
     d's join position when the writer asks (Start is answered Pos j);
   - counting: by round N the writer has more answered Fetches than it
     can have had by round R, so one of them is later than round R;
   - telescoping (writer_told): what the writer was told up to that Fetch
     is the log there from j, which contains what d was owed at round R.
*)
Theory asyncChatLiveCoverRun
Ancestors
  pair list rich_list arithmetic option string words alist sorting
  relation asyncCore asyncLevel1 asyncTranscript asyncServer
  asyncServerSafety asyncProgress asyncM4ServerUses asyncRunOkGen
  asyncM4GRounds asyncM4SockModel asyncM4SockInv asyncM4GTrans
  asyncM4EchoRunOk asyncM4EchoSafe ffiSpikeSocketFFI
  asyncServerV asyncServerVLive asyncServerVLiveA asyncServerVPushLive
  asyncWithStore asyncWithTap asyncChatSW asyncChatModel asyncChatSafe
  asyncChatTrace asyncChatLiveV asyncChatLiveDeliver asyncChatLiveCover
  asyncChatLiveGlue
Libs
  preamble

(* ------------------------------------------------------------------------
   The run's transcript
   ------------------------------------------------------------------------ *)

Theorem MEM_accepted_tt[local]:
  MEM (Accept l, SOME (Accepted fd)) tt ⇒ MEM fd (accepted tt)
Proof
  simp[accepted_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> strip_tac >>
  first_assum (irule_at Any) >> simp[]
QED

(* The fds of the run's transcript fit in 64 bits *)
Theorem fds_ok_TSg_chat:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  fds_ok (TSg (chat_server lfdn) ifds s0 N)
Proof
  strip_tac >> assume_tac (Q.INST [‘lfd’ |-> ‘lfdn’] chat_uses_ok_v) >>
  ‘∀fd. EXISTS (on_fd fd) (TSg (chat_server lfdn) ifds s0 N) ⇒ fd < dimword(:64)’
    by metis_tac[gen_fds_bounded] >>
  drule_all gen_sinv >> disch_then (qspecl_then [‘ifds’, ‘N’] strip_assume_tac) >>
  drule gen_trans_split >> strip_tac >>
  rewrite_tac[fds_ok_def] >> gen_tac >> strip_tac >> conj_tac >>
  rpt gen_tac >> strip_tac
  >- (‘on_fd fd p’
        by (rewrite_tac[on_fd_def] >> disj1_tac >> first_assum ACCEPT_TAC) >>
      first_x_assum irule >> rewrite_tac[EXISTS_MEM] >> qexists_tac ‘p’ >>
      simp[]) >>
  ‘MEM fd (accepted (tt1 ++ tt2))’
    by (irule MEM_accepted_tt >> qexists_tac ‘l’ >> gvs[]) >>
  drule TREL_NONE >> strip_tac >> drule accepted_NONE >> strip_tac >>
  ‘accepted tt1 = MAP w2n (wacc (SPg (chat_server lfdn) ifds s0 N))’
    by (irule TREL_accepted >> simp[]) >>
  gvs[MEM_MAP] >> ‘w2n y < dimword(:64)’ by simp[w2n_lt] >> gvs[]
QED

Theorem zipr_NIL_NONE[local]:
  ∀acts. EVERY (λp. SND p = NONE) (zipr acts [])
Proof
  Induct >> simp[zipr_def]
QED

(* The transcript after k rounds: its first k rounds, then unanswered
   actions; the full transcript extends its first k rounds *)
Theorem trans_rounds_split:
  k ≤ LENGTH h ⇒
  ∃Z X. trans m (TAKE k h) = FLAT (GENLIST (round_trans m h) k) ++ Z ∧
        EVERY (λp. SND p = NONE) Z ∧
        trans m h = FLAT (GENLIST (round_trans m h) k) ++ X
Proof
  strip_tac >> simp[trans_TAKE_split, zipr_NIL_NONE] >>
  simp[trans_def] >>
  ‘SUC (LENGTH h) = (SUC (LENGTH h) - k) + k’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >>
  metis_tac[]
QED

Theorem MEM_acceptedc[local]:
  MEM fd (acceptedc tr) ⇒ ∃l. MEM (Sock (Accept l), SOME (SockR (Accepted fd))) tr
Proof
  Induct_on ‘tr’ >> simp[acceptedc_def] >> PairCases >> simp[] >>
  every_case_tac >> rw[] >> fs[acceptedc_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The theorem
   ------------------------------------------------------------------------ *)

Overload CWr = “with_tap chat_tap chat_delta empty_store”
Overload CIn = “tap_hist chat_tap chat_delta empty_store”

Theorem MEM_FILTER_pos[local]:
  MEM e (FILTER P l) ⇒ ∃p. p < LENGTH l ∧ EL p l = e ∧ P e
Proof
  simp[MEM_FILTER, MEM_EL] >> metis_tac[]
QED

Theorem nfa_APPEND2[local]:
  nfa fd (a ++ b) = nfa fd a + nfa fd b
Proof
  simp[FILTER_APPEND]
QED

(* The k-th entry of a filtered with_state, located *)
Theorem with_state_FILTER_EL_pos:
  k < LENGTH (FILTER (P ∘ FST) (with_state TR)) ⇒
  ∃p. p < LENGTH TR ∧ P (EL p TR) ∧
      EL k (FILTER (P ∘ FST) (with_state TR)) =
        (EL p TR, tap_fold chat_tap chat_delta empty_store (TAKE p TR))
Proof
  strip_tac >>
  ‘MEM (EL k (FILTER (P ∘ FST) (with_state TR))) (FILTER (P ∘ FST) (with_state TR))’
    by simp[EL_MEM] >>
  qabbrev_tac ‘e = EL k (FILTER (P ∘ FST) (with_state TR))’ >>
  fs[MEM_FILTER] >> Cases_on ‘e’ >> gvs[MEM_with_state] >> metis_tac[]
QED

(* A connection with entries in the server's transcript was accepted *)
Theorem chat_isolates_acc:
  freshc (trans (server_v chatV chat_handler lfd) hh) ∧
  EXISTS (on_fdc fd) (trans (server_v chatV chat_handler lfd) hh) ⇒
  MEM fd (acceptedc (trans (server_v chatV chat_handler lfd) hh))
Proof
  rw[GSYM cserver_with_eq_v] >>
  qspecl_then [‘chat_handler’, ‘lfd’] mp_tac
    (Q.GENL [‘h’, ‘lfd’] cserver_with_isolates) >>
  simp[chat_handler_on_fdc] >> disch_then (qspec_then ‘hh’ mp_tac) >> simp[]
QED

(* The library's view of a connection's handler, for the chat server *)
Theorem chat_view:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (chat_server lfdn) ifds s0 n)) ∧ n ≤ N ⇒
  ∃a (g : (event, (canswer, asyncServer$response) kres) snapshot list).
    a ≤ n ∧ LENGTH g + a = N ∧ prompt (chat_handler (w2n c)) g ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd_v chatV (w2n c))
        (trans (server_v chatV chat_handler lfdn)
           (CIn (server_v chatV chat_handler lfdn)
              (MAP sfs (ghist ifds (srelabel (chat_server lfdn)) s0 (a + j))))) =
      trans (chat_handler (w2n c)) (TAKE j g)
Proof
  rw[chat_server_v] >>
  qspecl_then [‘chatV’, ‘CWr’, ‘CIn’, ‘chat_handler’, ‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’, ‘N’]
    mp_tac (Q.GENL [‘V’, ‘Wr’, ‘inner’, ‘hf’, ‘lfdn’, ‘s0’, ‘c’, ‘ifds’, ‘n’, ‘N’]
              view_wrap_ans) >>
  simp[wrap_ok_with_tap, vocab_ok_chatV, hokv_chat_handler] >>
  strip_tac >> qexistsl [‘a’, ‘g’] >> simp[]
QED

(* MAIN: two rounds after round R, the hub's answers to d's writer cover
   what d was owed at round R *)
Theorem chat_cover_at:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM d (wacc (SPg (chat_server lfdn) ifds s0 R)) ⇒
  owed_m (w2n d) (TSg (chat_server lfdn) ifds s0 R) ≼
  CONCAT (cout (DROP 1 (conn_answers chatV CWr CIn chat_handler lfdn ifds s0 (R + 2) d)))
Proof
  rpt strip_tac >>
  ‘fds_ok (TSg (chat_server lfdn) ifds s0 (R + 2))’ by simp[fds_ok_TSg_chat] >>
  ‘fresh (TSg (chat_server lfdn) ifds s0 (R + 2)) ∧
   ∀k. fresh (TSg (chat_server lfdn) ifds s0 k)’
    by metis_tac[gen_fresh, chat_uses_ok_v] >>
  qabbrev_tac ‘N = R + 2’ >>
  ‘R ≤ N’ by simp[Abbr ‘N’] >>
  (* d's handler's view *)
  drule_all chat_view >> strip_tac >>
  fs[chat_server_v] >>
  qabbrev_tac ‘CM = server_v chatV chat_handler lfdn’ >>
  ‘asyncLevel1$wf CM’
    by (simp[Abbr ‘CM’] >> irule wf_server_v >> simp[wf_chat_handler]) >>
  qabbrev_tac ‘fd = w2n d’ >>
  qabbrev_tac ‘H = MAP sfs (ghist ifds (srelabel (CWr CM)) s0 N)’ >>
  qabbrev_tac ‘IH = CIn CM H’ >>
  qabbrev_tac ‘TT = trans CM IH’ >>
  ‘LENGTH IH = N’ by simp[Abbr ‘IH’, Abbr ‘H’] >>
  ‘∀k. k ≤ N ⇒ CIn CM (MAP sfs (ghist ifds (srelabel (CWr CM)) s0 k)) = TAKE k IH’
    by (rpt strip_tac >>
        simp[Abbr ‘IH’, Abbr ‘H’, GSYM tap_hist_TAKE, GSYM MAP_TAKE, ghist_TAKE]) >>
  ‘∀k. k ≤ N ⇒ TSg (CWr CM) ifds s0 k = untag (trans CM (TAKE k IH))’
    by (rpt strip_tac >> simp[trans_with_tap]) >>
  ‘∀j. j ≤ LENGTH g ⇒
       FILTER (on_fd_v chatV fd) (trans CM (TAKE (a + j) IH)) =
       trans (chat_handler fd) (TAKE j g)’
    by (rpt strip_tac >> ‘a + j ≤ N’ by simp[] >>
        qpat_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘j’ mp_tac) >>
        qpat_assum ‘∀k. k ≤ N ⇒ CIn _ _ = _’ (qspec_then ‘a + j’ mp_tac) >>
        impl_tac >- simp[] >> disch_then SUBST1_TAC >>
        impl_tac >- simp[] >> simp[]) >>
  (* the writer's view *)
  drule chat_handler_writer_views >> strip_tac >>
  qabbrev_tac ‘WR = trans (writer fd) G’ >>
  ‘trans CM (TAKE N IH) = TT’ by simp[Abbr ‘TT’, TAKE_LENGTH_ID_rwt] >>
  ‘FILTER (wq fd) TT = WR’
    by (qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd_v _ _) _ = _’
          (qspec_then ‘LENGTH g’ mp_tac) >> simp[] >>
        disch_then (mp_tac o AP_TERM “FILTER (wq fd)”) >>
        simp[FILTER_wq_on_fd_v] >> strip_tac >>
        qpat_x_assum ‘∀j. FILTER (wq fd) _ = _’ (qspec_then ‘LENGTH g’ mp_tac) >>
        simp[TAKE_LENGTH_ID_rwt, Abbr ‘WR’] >> metis_tac[]) >>
  (* the hub's facts on TT *)
  ‘∀k. k ≤ N ⇒ fresh (untag (trans CM (TAKE k IH)))’
    by (rpt strip_tac >> qpat_assum ‘∀k. fresh _’ (qspec_then ‘k’ mp_tac) >>
        qpat_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- simp[] >> disch_then SUBST1_TAC >> simp[]) >>
  ‘fresh (untag TT)’ by metis_tac[LESS_EQ_REFL] >>
  ‘fds_ok (untag TT)’
    by (qpat_assum ‘trans CM (TAKE N IH) = TT’ (SUBST1_TAC o SYM) >> metis_tac[LESS_EQ_REFL]) >>
  ‘answers_ok chat_tap chat_delta empty_store TT’
    by simp[Abbr ‘TT’, Abbr ‘IH’, tap_answers] >>
  (* the rounds before a, and before R *)
  ‘a ≤ LENGTH IH ∧ R ≤ LENGTH IH’ by simp[] >>
  qspecl_then [‘a’, ‘IH’, ‘CM’] mp_tac (Q.GENL [‘k’, ‘h’, ‘m’] trans_rounds_split) >>
  impl_tac >- simp[] >> disch_then (qx_choosel_then [‘Za’, ‘Xa’] strip_assume_tac) >>
  qspecl_then [‘R’, ‘IH’, ‘CM’] mp_tac (Q.GENL [‘k’, ‘h’, ‘m’] trans_rounds_split) >>
  impl_tac >- simp[] >> disch_then (qx_choosel_then [‘ZR’, ‘XR’] strip_assume_tac) >>
  qabbrev_tac ‘PA = FLAT (GENLIST (round_trans CM IH) a)’ >>
  qabbrev_tac ‘PR = FLAT (GENLIST (round_trans CM IH) R)’ >>
  (* the writer's first round: only its Start, unanswered *)
  ‘FILTER (on_fd_v chatV fd) (trans CM (TAKE a IH)) = trans (chat_handler fd) (TAKE 0 g)’
    by (qpat_assum ‘∀j. j ≤ LENGTH g ⇒
                        FILTER (on_fd_v _ _) (trans CM (TAKE (a + j) IH)) = _’
          (qspec_then ‘0’ mp_tac) >>
        REWRITE_TAC[ADD_CLAUSES, ZERO_LESS_EQ] >> DISCH_THEN ACCEPT_TAC) >>
  ‘FILTER (wq fd) (trans (chat_handler fd) (TAKE 0 g)) = [(Kv (fd, Start), NONE)]’
    by (qpat_assum ‘∀j. FILTER (wq fd) _ = _’ (qspec_then ‘0’ mp_tac) >>
        simp[trans_writer_NIL]) >>
  ‘FILTER (wq fd) (trans CM (TAKE a IH)) = [(Kv (fd, Start), NONE)]’
    by metis_tac[FILTER_wq_on_fd_v] >>
  ‘PA ++ Xa = TT ∧ PR ++ XR = TT’ by (simp[Abbr ‘TT’] >> metis_tac[]) >>
  ‘LENGTH G ≠ 0 ∧ LENGTH G = R − a + 2’
    by (qpat_x_assum ‘a + LENGTH g = N’ mp_tac >> qpat_x_assum ‘a ≤ R’ mp_tac >>
        qpat_x_assum ‘LENGTH G = LENGTH g’ mp_tac >> qunabbrev_tac ‘N’ >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >> intLib.ARITH_TAC) >>
  ‘∃r. WR ≠ [] ∧ HD WR = (Kv (fd, Start), SOME r)’
    by (Cases_on ‘G’ >- fs[] >> qunabbrev_tac ‘WR’ >>
        irule writer_HD_answered >> first_assum ACCEPT_TAC) >>
  (* no writer entry before round a *)
  ‘FILTER (wq fd) PA ++ FILTER (wq fd) Za = [(Kv (fd, Start), NONE)]’
    by (qpat_assum ‘FILTER (wq fd) (trans CM (TAKE a IH)) = _’ mp_tac >>
        qpat_assum ‘trans CM (TAKE a IH) = _’ (fn th => REWRITE_TAC[th]) >>
        REWRITE_TAC[FILTER_APPEND_DISTRIB]) >>
  ‘FILTER (wq fd) PA ++ FILTER (wq fd) Xa = WR’
    by (qpat_assum ‘FILTER (wq fd) TT = WR’ mp_tac >>
        qpat_assum ‘PA ++ Xa = TT’ (fn th => REWRITE_TAC[SYM th]) >>
        REWRITE_TAC[FILTER_APPEND_DISTRIB]) >>
  ‘FILTER (wq fd) PA = []’
    by (Cases_on ‘FILTER (wq fd) PA’ >> REWRITE_TAC[] >>
        qpat_x_assum ‘_ :: _ ++ _ = [_]’ mp_tac >>
        qpat_x_assum ‘_ :: _ ++ _ = WR’ (assume_tac o SYM) >>
        qpat_x_assum ‘HD WR = _’ mp_tac >> asm_rewrite_tac[] >>
        simp[]) >>
  ‘∀p. p < LENGTH TT ∧ wq fd (EL p TT) ⇒ LENGTH PA ≤ p’
    by (rpt strip_tac >> CCONTR_TAC >>
        ‘p < LENGTH PA’ by (pop_assum mp_tac >> simp[]) >>
        ‘EL p TT = EL p PA’
          by (qpat_assum ‘PA ++ Xa = TT’ (SUBST1_TAC o SYM) >> simp[EL_APPEND1]) >>
        ‘MEM (EL p PA) (FILTER (wq fd) PA)’
          by (simp[MEM_FILTER, EL_MEM] >> qpat_x_assum ‘EL p TT = _’ (SUBST1_TAC o SYM) >>
              first_assum ACCEPT_TAC) >>
        qpat_x_assum ‘MEM _ (FILTER _ _)’ mp_tac >>
        qpat_assum ‘FILTER (wq fd) PA = []’ (fn th => REWRITE_TAC[th, MEM])) >>
  (* d's accept is answered before round a *)
  ‘∀x. wq fd x ⇒ on_fdc fd x’
    by (rw[wq_def, on_fdc_def, on_fd_def] >> simp[]) >>
  ‘EXISTS (on_fdc fd) (trans CM (TAKE a IH))’
    by (‘MEM (Kv (fd, Start), NONE) (FILTER (wq fd) (trans CM (TAKE a IH)))’
          by (qpat_assum ‘FILTER (wq fd) (trans CM (TAKE a IH)) = _’
                (fn th => REWRITE_TAC[th]) >> simp[]) >>
        pop_assum mp_tac >> simp[MEM_FILTER, EXISTS_MEM] >> strip_tac >>
        qexists_tac ‘(Kv (fd, Start), NONE)’ >> simp[on_fdc_def]) >>
  ‘MEM fd (acceptedc (trans CM (TAKE a IH)))’
    by (qpat_assum ‘∀k. k ≤ N ⇒ fresh _’ (qspec_then ‘a’ mp_tac) >>
        impl_tac >- (qpat_assum ‘a ≤ R’ mp_tac >> simp[Abbr ‘N’]) >>
        REWRITE_TAC[GSYM freshc_untag] >> strip_tac >>
        qunabbrev_tac ‘CM’ >> irule chat_isolates_acc >> conj_tac >>
        first_assum ACCEPT_TAC) >>
  ‘∃l. MEM (Sock (Accept l), SOME (SockR (Accepted fd))) PA’
    by (irule MEM_acceptedc >>
        qpat_x_assum ‘MEM fd (acceptedc _)’ mp_tac >>
        qpat_assum ‘trans CM (TAKE a IH) = _’ SUBST1_TAC >>
        qpat_assum ‘EVERY _ Za’ (fn th => simp[MATCH_MP acceptedc_NONE th])) >>
  (* the writer's entries, each with the hub's state before it *)
  qabbrev_tac ‘Wl = FILTER (wq fd ∘ FST) (with_state TT)’ >>
  ‘MAP FST Wl = WR’
    by (qunabbrev_tac ‘Wl’ >> REWRITE_TAC[MAP_FST_FILTER_FST, MAP_FST_with_state] >>
        first_assum ACCEPT_TAC) >>
  ‘LENGTH Wl = LENGTH WR’ by metis_tac[LENGTH_MAP] >>
  ‘∀k. k < LENGTH Wl ⇒
       ∃p. p < LENGTH TT ∧ wq fd (EL p TT) ∧
           EL k Wl = (EL p TT, tap_fold chat_tap chat_delta empty_store (TAKE p TT))’
    by (qunabbrev_tac ‘Wl’ >> rpt strip_tac >>
        irule with_state_FILTER_EL_pos >> first_assum ACCEPT_TAC) >>
  ‘0 < LENGTH WR’
    by (REWRITE_TAC[GSYM NOT_ZERO_LT_ZERO, LENGTH_NIL] >>
        qpat_assum ‘WR ≠ []’ ACCEPT_TAC) >>
  qpat_assum ‘∀k. k < LENGTH Wl ⇒ _’ (qspec_then ‘0’ mp_tac) >>
  impl_tac >- (qpat_assum ‘LENGTH Wl = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘p0’ strip_assume_tac) >>
  ‘EL p0 TT = (Kv (fd, Start), SOME r)’
    by (qpat_x_assum ‘HD WR = _’ (SUBST1_TAC o SYM) >>
        qpat_assum ‘MAP FST Wl = WR’ (SUBST1_TAC o SYM) >>
        ‘HD (MAP FST Wl) = EL 0 (MAP FST Wl)’ by simp[] >> pop_assum SUBST1_TAC >>
        ‘0 < LENGTH Wl’ by (qpat_assum ‘LENGTH Wl = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        simp[EL_MAP]) >>
  ‘LENGTH PA ≤ p0’ by (first_assum irule >> simp[]) >>
  (* the hub knew d's join when the writer asked *)
  ‘MEM (Sock (Accept l), SOME (SockR (Accepted fd))) (TAKE p0 TT)’
    by (‘TAKE p0 TT = PA ++ TAKE (p0 − LENGTH PA) Xa’
          by (qpat_assum ‘PA ++ Xa = TT’ (SUBST1_TAC o SYM) >> simp[TAKE_APPEND2]) >>
        pop_assum SUBST1_TAC >> simp[]) >>
  drule joins_accept >>
  disch_then (qspec_then ‘empty_store’ (qx_choose_then ‘j0’ assume_tac)) >>
  ‘r = KvR (Pos j0)’
    by (qpat_assum ‘answers_ok _ _ _ _’
          (mp_tac o Q.SPECL [‘p0’, ‘(fd, Start)’, ‘r’] o REWRITE_RULE[answers_ok_def]) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then SUBST1_TAC >> REWRITE_TAC[chat_delta_def] >> simp[] >>
        qpat_assum ‘ALOOKUP _ _ = SOME j0’ SUBST1_TAC >> simp[]) >>
  ‘fds_ok (untag (TAKE p0 TT))’ by metis_tac[fds_ok_TAKE] >>
  ‘hub_inv (tap_fold chat_tap chat_delta empty_store (TAKE p0 TT)) (untag (TAKE p0 TT))’
    by (irule tap_inv >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘hub_inv _ _’ (strip_assume_tac o REWRITE_RULE[hub_inv_def]) >>
  first_x_assum (qspecl_then [‘fd’, ‘j0’] mp_tac) >>
  impl_tac >- (qunabbrev_tac ‘fd’ >> simp[w2n_lt]) >>
  disch_then (qx_choosel_then [‘U1’, ‘U2’] strip_assume_tac) >>
  (* every entry of d's writer is after round a *)
  ‘∀e. MEM e WR ⇒ ∃p. p < LENGTH TT ∧ EL p TT = e ∧ LENGTH PA ≤ p’
    by (rpt strip_tac >>
        ‘MEM e (FILTER (wq fd) TT)’
          by (qpat_assum ‘FILTER (wq fd) TT = WR’ (fn th => REWRITE_TAC[th]) >>
              first_assum ACCEPT_TAC) >>
        drule MEM_FILTER_pos >> strip_tac >> qexists_tac ‘p’ >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_assum ‘∀p. p < LENGTH TT ∧ _ ⇒ _’ irule >>
        conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_assum ‘EL p TT = e’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  ‘∀p. LENGTH PA ≤ p ⇒
       MEM (Sock (Accept l), SOME (SockR (Accepted fd))) (TAKE p TT)’
    by (rpt strip_tac >>
        ‘TAKE p TT = PA ++ TAKE (p − LENGTH PA) Xa’
          by (qpat_assum ‘PA ++ Xa = TT’ (SUBST1_TAC o SYM) >> simp[TAKE_APPEND2]) >>
        pop_assum SUBST1_TAC >> simp[]) >>
  (* the hub's kind of answers *)
  ‘answers_kind fd WR’
    by (simp[answers_kind_def] >> conj_tac >> rpt strip_tac >>
        qpat_assum ‘∀e. MEM e WR ⇒ _’ (drule_then strip_assume_tac) >>
        qpat_assum ‘answers_ok _ _ _ _’
          (mp_tac o Q.SPEC ‘p’ o REWRITE_RULE[answers_ok_def])
        >- (disch_then (qspecl_then [‘(fd, Fetch i)’, ‘r'’] mp_tac) >>
            impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
            disch_then SUBST1_TAC >> simp[chat_delta_def])
        >> disch_then (qspecl_then [‘(fd, Start)’, ‘r'’] mp_tac) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then SUBST1_TAC >> REWRITE_TAC[chat_delta_def] >> simp[] >>
        qpat_assum ‘∀p. LENGTH PA ≤ p ⇒ MEM _ (TAKE p TT)’ drule >> strip_tac >>
        drule joins_accept >>
        disch_then (qspec_then ‘empty_store’ (qx_choose_then ‘j1’ assume_tac)) >>
        pop_assum mp_tac >> simp[]) >>
  (* the writer's window: a new answered Fetch in rounds R, R + 1 *)
  ‘R − a ≤ LENGTH g’
    by (qpat_x_assum ‘a + LENGTH g = N’ mp_tac >> qpat_x_assum ‘a ≤ R’ mp_tac >>
        qunabbrev_tac ‘N’ >> rpt (pop_assum kall_tac) >> intLib.ARITH_TAC) >>
  ‘FILTER (wq fd) (trans CM (TAKE R IH)) = trans (writer fd) (TAKE (R − a) G)’
    by (qpat_assum ‘∀j. j ≤ LENGTH g ⇒
                        FILTER (on_fd_v _ _) (trans CM (TAKE (a + j) IH)) = _’
          (qspec_then ‘R − a’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        ‘a + (R − a) = R’ by (qpat_x_assum ‘a ≤ R’ mp_tac >> rpt (pop_assum kall_tac) >>
                             intLib.ARITH_TAC) >>
        pop_assum SUBST1_TAC >>
        disch_then (mp_tac o AP_TERM “FILTER (wq fd)”) >>
        REWRITE_TAC[FILTER_wq_on_fd_v] >> disch_then SUBST1_TAC >>
        qpat_assum ‘∀j. FILTER (wq fd) _ = _’ (qspec_then ‘R − a’ ACCEPT_TAC)) >>
  ‘nfa fd (trans CM (TAKE R IH)) = nfa fd (trans (writer fd) (TAKE (R − a) G))’
    by (pop_assum (SUBST1_TAC o SYM) >> REWRITE_TAC[nfa_FILTER_wq]) >>
  ‘nfa fd PR ≤ nfa fd (trans (writer fd) (TAKE (R − a) G))’
    by (pop_assum (SUBST1_TAC o SYM) >>
        qpat_assum ‘trans CM (TAKE R IH) = _’ SUBST1_TAC >>
        REWRITE_TAC[nfa_APPEND2] >> rpt (pop_assum kall_tac) >> intLib.ARITH_TAC) >>
  ‘nfa fd (trans (writer fd) (TAKE (R − a) G)) <
   nfa fd (trans (writer fd) (TAKE (R − a + 2) G))’
    by (qspecl_then [‘fd’, ‘G’, ‘R − a’] mp_tac (Q.GENL [‘fd’, ‘G’, ‘m’] writer_window) >>
        ‘trans (writer fd) G = WR’ by simp[Abbr ‘WR’] >>
        pop_assum (fn th => REWRITE_TAC[th]) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                     qpat_assum ‘LENGTH G = _’ SUBST1_TAC >> REWRITE_TAC[LESS_EQ_REFL]) >>
        REWRITE_TAC[]) >>
  ‘TAKE (R − a + 2) G = G’
    by (qpat_assum ‘LENGTH G = _’ (SUBST1_TAC o SYM) >> REWRITE_TAC[TAKE_LENGTH_ID]) >>
  ‘nfa fd PR < nfa fd WR’
    by (‘trans (writer fd) G = WR’ by simp[Abbr ‘WR’] >>
        qpat_x_assum ‘nfa fd (trans (writer fd) (TAKE (R − a) G)) < _’ mp_tac >>
        qpat_x_assum ‘nfa fd PR ≤ _’ mp_tac >>
        qpat_assum ‘TAKE (R − a + 2) G = G’ (fn th => REWRITE_TAC[th]) >>
        pop_assum (fn th => REWRITE_TAC[th]) >>
        rpt (pop_assum kall_tac) >> intLib.ARITH_TAC) >>
  ‘nfa fd PR < nfa fd (PR ++ XR)’
    by (‘nfa fd (PR ++ XR) = nfa fd WR’
          by (qpat_assum ‘PR ++ XR = TT’ SUBST1_TAC >>
              qpat_assum ‘FILTER (wq fd) TT = WR’ (SUBST1_TAC o SYM) >>
              REWRITE_TAC[nfa_FILTER_wq]) >>
        pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule nfa_split_exists >>
  qpat_assum ‘PR ++ XR = TT’ SUBST1_TAC >>
  disch_then (qx_choose_then ‘p’ strip_assume_tac) >>
  (* that Fetch, among the writer's entries *)
  ‘wq fd (EL p TT)’ by (irule afetch_wq >> first_assum ACCEPT_TAC) >>
  qspecl_then [‘TT’, ‘p’, ‘wq fd’] mp_tac (Q.GENL [‘TR’, ‘p’, ‘P’] FILTER_with_state_EL) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum ‘Abbrev (Wl = _)’ (fn th => REWRITE_TAC[REWRITE_RULE[markerTheory.Abbrev_def] th |> SYM]) >>
  qabbrev_tac ‘k = LENGTH (FILTER (wq fd) (TAKE p TT))’ >>
  strip_tac >>
  (* the hub's log at each writer entry *)
  ‘∀q. q < LENGTH TT ⇒
       (tap_fold chat_tap chat_delta empty_store (TAKE q TT)).log =
       lines_done (untag (TAKE q TT))’
    by (rpt strip_tac >> irule log_at >> irule fds_ok_TAKE >> first_assum ACCEPT_TAC) >>
  qabbrev_tac ‘lg = λk. if k < LENGTH Wl then (SND (EL k Wl)).log
                        else lines_done (untag TT)’ >>
  ‘transitive (λ(x : ((asyncServer$action, num # cquery) kact #
                      (canswer, asyncServer$response) kres option) # cstore) y.
                 (SND x).log ≼ (SND y).log)’
    by (simp[relationTheory.transitive_def] >> metis_tac[IS_PREFIX_TRANS]) >>
  ‘SORTED (λx y. (SND x).log ≼ (SND y).log) Wl’
    by (qunabbrev_tac ‘Wl’ >> irule SORTED_FILTER >> conj_tac
        >- first_assum ACCEPT_TAC
        >> irule with_state_sorted >> first_assum ACCEPT_TAC) >>
  ‘∀m n. m < n ∧ n < LENGTH Wl ⇒ (SND (EL m Wl)).log ≼ (SND (EL n Wl)).log’
    by (qpat_assum ‘transitive _’ (fn th => assume_tac (MATCH_MP SORTED_EL_LESS th)) >>
        pop_assum (qspec_then ‘Wl’ mp_tac) >>
        qpat_assum ‘SORTED _ Wl’ (fn th => REWRITE_TAC[th]) >> BETA_TAC >>
        disch_then (fn th => rpt strip_tac >> mp_tac (Q.SPECL [‘m’, ‘n’] th)) >>
        simp[]) >>
  ‘∀m. m < LENGTH Wl ⇒ (SND (EL m Wl)).log ≼ lines_done (untag TT)’
    by (rpt strip_tac >>
        qpat_assum ‘∀k. k < LENGTH Wl ⇒ ∃p. _’ (qspec_then ‘m’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (qx_choose_then ‘q’ strip_assume_tac) >>
        qpat_x_assum ‘EL m Wl = _’ SUBST1_TAC >> REWRITE_TAC[SND] >>
        qpat_assum ‘∀q. q < LENGTH TT ⇒ _’ (qspec_then ‘q’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
        irule lines_done_mono >> irule untag_mono >>
        REWRITE_TAC[IS_PREFIX_APPEND] >> qexists_tac ‘DROP q TT’ >>
        REWRITE_TAC[TAKE_DROP]) >>
  ‘mono_log lg’
    by (simp[mono_log_def, Abbr ‘lg’] >> rpt strip_tac >>
        Cases_on ‘k' < LENGTH Wl’ >> Cases_on ‘k'' < LENGTH Wl’ >> simp[]
        >- (Cases_on ‘k'' = k'’ >- simp[] >>
            qpat_assum ‘∀m n. m < n ∧ n < LENGTH Wl ⇒ _’ irule >> simp[])
        >> qpat_assum ‘∀m. m < LENGTH Wl ⇒ _’ irule >> simp[]) >>
  ‘fits_log fd lg WR’
    by (REWRITE_TAC[fits_log_def] >> qx_genl_tac [‘kk’, ‘ii’, ‘aa’] >> strip_tac >>
        ‘kk < LENGTH Wl’
          by (qpat_assum ‘LENGTH Wl = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        qpat_assum ‘∀k. k < LENGTH Wl ⇒ ∃p. _’ (qspec_then ‘kk’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (qx_choose_then ‘q’ strip_assume_tac) >>
        ‘EL kk WR = EL q TT’
          by (qpat_assum ‘MAP FST Wl = WR’ (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
        ‘EL q TT = (Kv (fd, Fetch ii), SOME (KvR aa))’
          by (qpat_x_assum ‘EL kk WR = EL q TT’ (SUBST1_TAC o SYM) >>
              first_assum ACCEPT_TAC) >>
        qpat_assum ‘answers_ok _ _ _ _’
          (mp_tac o Q.SPECL [‘q’, ‘(fd, Fetch ii)’, ‘KvR aa’] o
           REWRITE_RULE[answers_ok_def]) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        simp[chat_delta_def, Abbr ‘lg’]) >>
  (* telescoping, at that Fetch *)
  ‘0 < LENGTH Wl’
    by (qpat_assum ‘LENGTH Wl = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  ‘j0 ≤ LENGTH (lg 0)’
    by (simp[Abbr ‘lg’] >> irule IS_PREFIX_LENGTH >> simp[lines_done_APPEND_prefix]) >>
  ‘trans (writer fd) G = WR’ by simp[Abbr ‘WR’] >>
  qspecl_then [‘lg’, ‘fd’, ‘G’, ‘j0’] mp_tac (Q.GENL [‘lg’, ‘fd’, ‘R’, ‘j’] writer_told) >>
  qpat_assum ‘trans (writer fd) G = WR’ (fn th => REWRITE_TAC[th]) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then (qspec_then ‘k’ mp_tac) >>
  ‘EL k WR = EL p TT’
    by (qpat_assum ‘MAP FST Wl = WR’ (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
  impl_tac
  >- (conj_tac
      >- (qpat_assum ‘LENGTH Wl = _’ (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
      >> qpat_assum ‘EL k WR = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  ‘lg k = lines_done (untag (TAKE p TT))’ by simp[Abbr ‘lg’] >>
  (* the answers the library names are the writer's *)
  ‘conn_answers chatV CWr CIn chat_handler lfdn ifds s0 N d = kanswers chatV WR’
    by (‘conn_answers chatV CWr CIn chat_handler lfdn ifds s0 N d =
         kanswers chatV (FILTER (on_fd_v chatV fd) TT)’
          by (REWRITE_TAC[conn_answers_def] >> qunabbrev_tac ‘TT’ >>
              qunabbrev_tac ‘IH’ >> qunabbrev_tac ‘H’ >> qunabbrev_tac ‘CM’ >>
              qunabbrev_tac ‘fd’ >> REWRITE_TAC[]) >>
        pop_assum SUBST1_TAC >>
        qpat_assum ‘FILTER (wq fd) TT = WR’ (SUBST1_TAC o SYM) >>
        ONCE_REWRITE_TAC[GSYM FILTER_wq_on_fd_v] >>
        irule EQ_SYM >> irule kanswers_on_fd_v_wq >> simp[EVERY_MEM, MEM_FILTER]) >>
  (* what d was owed at round R *)
  ‘owed_m fd (TSg (CWr CM) ifds s0 R) = owed_m fd (untag PR)’
    by (qpat_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘R’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
        qpat_assum ‘trans CM (TAKE R IH) = _’ SUBST1_TAC >>
        ‘untag (PR ++ ZR) = untag PR ++ untag ZR’ by simp[untag_def] >>
        pop_assum SUBST1_TAC >>
        irule owed_m_NONE >> irule untag_NONE >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST1_TAC >>
  qpat_assum ‘conn_answers _ _ _ _ _ _ _ _ _ = _’ SUBST1_TAC >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘CONCAT (cout (DROP 1 (kanswers chatV (TAKE (SUC k) WR))))’ >>
  REWRITE_TAC[told_TAKE_prefix] >>
  qpat_assum ‘CONCAT _ = DROP j0 _’ SUBST1_TAC >>
  qpat_assum ‘lg k = _’ SUBST1_TAC >>
  ‘untag TT = U1 ++ U2 ++ untag (DROP p0 TT)’
    by (qpat_assum ‘untag (TAKE p0 TT) = _’ (SUBST1_TAC o SYM) >>
        simp[GSYM untag_def] >>
        ‘TT = TAKE p0 TT ++ DROP p0 TT’ by simp[] >>
        pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        simp[untag_def]) >>
  ‘rich_list$SPLITP (acc_of fd) (untag TT) = (U1, U2 ++ untag (DROP p0 TT))’
    by (qpat_assum ‘untag TT = _’ SUBST1_TAC >> irule SPLITP_acc_of >>
        qpat_assum ‘fresh (untag TT)’ mp_tac >>
        qpat_assum ‘untag TT = _’ SUBST1_TAC >> simp[fresh_def]) >>
  ‘untag PR ≼ untag TT’
    by (irule untag_mono >> qpat_assum ‘PR ++ XR = TT’ (SUBST1_TAC o SYM) >> simp[]) >>
  simp[owed_m_def] >>
  Cases_on ‘rich_list$SPLITP (acc_of fd) (untag PR)’ >> rename1 ‘(Q1, Q2)’ >>
  Cases_on ‘Q2’ >> simp[] >>
  ‘Q1 = U1’
    by (qspecl_then [‘untag TT’, ‘untag PR’, ‘U1’, ‘U2 ++ untag (DROP p0 TT)’]
          mp_tac (Q.GEN ‘P’ SPLITP_prefix_same |> Q.ISPEC ‘acc_of fd’) >>
        simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_assum ‘j0 = _’ (SUBST1_TAC o SYM) >>
  irule DROP_prefix >> irule lines_done_mono >> irule untag_mono >>
  ‘TAKE p TT = PR ++ TAKE (p − LENGTH PR) XR’
    by (qpat_assum ‘PR ++ XR = TT’ (SUBST1_TAC o SYM) >> simp[TAKE_APPEND2]) >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem chat_cover:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM d (wacc (SPg (chat_server lfdn) ifds s0 R)) ⇒
  ∃N. owed_m (w2n d) (TSg (chat_server lfdn) ifds s0 R) ≼
      CONCAT (cout (DROP 1 (conn_answers chatV CWr CIn chat_handler lfdn ifds s0 N d)))
Proof
  strip_tac >> drule_all chat_cover_at >> strip_tac >>
  qexists_tac ‘R + 2’ >> first_assum ACCEPT_TAC
QED
