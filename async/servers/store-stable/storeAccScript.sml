(*
  What the Level 2 store server waits for (design/37 §5, step C3):
  loopInterestAcc's sw_acc for the skeleton over any vocabulary, then for the
  store.

  - sv_acc: server_v2, with handlers that accept nothing and wait for
    nothing but their own fd, waits only for Readable lfd and Readable fd
    of fds it has accepted;
  - store_acc: with_store2 Always over it waits for Always (while a query
    is pending), the listener, and the connections the store server has
    accepted, counted in its (socket) transcript.

  MAIN: sv_acc, store_acc.
*)
Theory storeAcc
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServerSafety echoBlockingWaits skeletonV skeletonVProgress
  skeletonVLive protoV proto2 loopInterestAcc withStore
  withStore2 skeletonVKv skeletonVActs protoVActs
Libs
  preamble

Theorem server_v2_run[local]:
  (∀fd. (h2 fd).run = hf fd) ⇒ (server_v2 V h2 lfd).run = server_v V hf lfd
Proof
  strip_tac >>
  ‘∀fd. erase (h2 fd) = hf fd’ by simp[erase_def] >>
  drule erase_server_v2 >> simp[erase_def]
QED

(* MAIN: what the skeleton waits for *)
Theorem sv_acc:
  vocab_ok V ∧ (∀fd. (h2 fd).run = hf fd) ∧
  (∀fd h g. accs_v V g (trans (hf fd) h) = 0) ∧
  (∀fd h. (h2 fd).interest h ⊆ {Readable fd}) ⇒
  ∀h x. Readable x ∈ (server_v2 V h2 lfd).interest h ⇒
        x = lfd ∨ 0 < accs_v V x (trans (server_v V hf lfd) h)
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ‘(server_v2 V h2 lfd).run = server_v V hf lfd’
       by (irule server_v2_run >> simp[])
  >> pop_assum (SUBST1_TAC o SYM)
  >> ONCE_REWRITE_TAC[server_v2_unfold] >> REWRITE_TAC[server_v_body2_def]
  >> simp[bind2_def]
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C0 K0 h’
  >> qmatch_goalsub_abbrev_tac ‘trans (bind C0.run F0) h’
  >> ‘wf C0.run ∧ settled C0.run’ by simp[Abbr ‘C0’, wait_on_def, wf_wait, settled_wait]
  >> qspecl_then [‘C0.run’, ‘h’] strip_assume_tac history_split
  >- (qspecl_then [‘C0’, ‘K0’, ‘h’] mp_tac
        (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_running) >>
      simp[] >> rpt strip_tac >> gvs[Abbr ‘C0’, wait_on_def])
  >> gvs[]
  >> ‘h1 ≠ []’ by (gvs[Abbr ‘C0’, wait_on_def] >> metis_tac[first_done_wait_nonempty])
  >> ‘trans (bind C0.run F0) (h1 ++ h2') = trans C0.run h1 ++ trans (F0 ()) h2'’
       by (MATCH_MP_TAC trans_bind_continues >> gvs[])
  >> ‘bind_interest C0 K0 (h1 ++ h2') = (K0 ()).interest h2'’
       by (MATCH_MP_TAC bind_interest_settled >> gvs[])
  >> simp[]
  >> ‘trans C0.run h1 = []’ by simp[Abbr ‘C0’, wait_on_def]
  >> simp[Abbr ‘K0’, Abbr ‘F0’, bind2_def]
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C1 K1 h2'’
  >> qmatch_goalsub_abbrev_tac ‘trans (bind C1.run F1) h2'’
  >> ‘wf C1.run ∧ settled C1.run’ by simp[Abbr ‘C1’, emit2_def, wf_emit, settled_emit]
  >> qspecl_then [‘C1.run’, ‘h2'’] strip_assume_tac history_split
  >- (qspecl_then [‘C1’, ‘K1’, ‘h2'’] mp_tac
        (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_running) >>
      simp[] >> rpt strip_tac >> gvs[Abbr ‘C1’, emit2_def])
  >> rename1 ‘first_done C1.run hA xA’
  >> rename1 ‘h2' = hA ++ hB’
  >> ‘trans (bind C1.run F1) (hA ++ hB) = trans C1.run hA ++ trans (F1 xA) hB’
       by (MATCH_MP_TAC trans_bind_continues >> gvs[])
  >> ‘bind_interest C1 K1 (hA ++ hB) = (K1 xA).interest hB’
       by (MATCH_MP_TAC bind_interest_settled >> gvs[])
  >> gvs[]
  >> gvs[Abbr ‘C1’, emit2_def]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH hB < LENGTH h1 + (LENGTH hB + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, Abbr ‘F1’]
  >> ‘V.sact (V.acc lfd) = SOME (Accept lfd)’ by fs[vocab_ok_def]
  >> simp[]
  >> ‘(server_v2 V h2 lfd).run = server_v V hf lfd’ by (irule server_v2_run >> simp[])
  >> Cases_on ‘vaccd V res’ >> simp[]
  (* no new connection: the server again *)
  >- (strip_tac >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘hB’ mp_tac) >>
      simp[] >> disch_then drule >> rw[] >> simp[])
  (* a new connection fd: its handler, beside the rest of the server *)
  >> rename1 ‘vaccd V res = SOME fd’
  >> simp[map2_def, both2_def, sproj_both_counts]
  >> qabbrev_tac ‘R = right_view (hf fd) (server_v V hf lfd) hB’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH hB + 1)’ by simp[Abbr ‘R’]
  >> strip_tac
  >- ((* the handler waits for it: x = fd, the accepted one *)
      drule waiting_on_interest >> strip_tac >>
      ‘Readable x ∈ {Readable fd}’ by metis_tac[SUBSET_DEF] >>
      gvs[vaccd_def] >> every_case_tac >> gvs[accs_def, is_acc_def])
  >> drule waiting_on_interest >> strip_tac
  >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘R’ mp_tac) >> simp[]
  >> disch_then drule >> rw[] >> simp[]
QED

(* MAIN: the Level 2 store server (now = Always) waits for Always, the
   listener, or a connection the store server has accepted *)
Theorem store_acc:
  Readable x ∈
    waiting_on (with_store2 Always δ st
                  (server_v2 sockV (λfd. proto_handler_v2 sockV P (ansq fd) (fin fd) (fd, "")) lfd))
               h ⇒
  x = lfd ∨
  0 < accs x (trans (with_store δ st
                       (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfd))
                    h)
Proof
  strip_tac >> drule waiting_on_interest >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘server_v2 sockV H2 lfd’ >>
  qabbrev_tac ‘HF = λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")’ >>
  ‘∀fd. (H2 fd).run = HF fd’
    by simp[Abbr ‘H2’, Abbr ‘HF’, GSYM erase_def, erase_proto_handler_v2] >>
  ‘(server_v2 sockV H2 lfd).run = server_v sockV HF lfd’
    by (irule server_v2_run >> simp[]) >>
  ‘asyncLevel1$wf (server_v sockV HF lfd)’
    by (irule wf_server_v >> simp[Abbr ‘HF’, wf_proto_handler_v]) >>
  (* Always is not Readable x: the skeleton waits for it *)
  qabbrev_tac ‘IH = inner_hist δ st (server_v sockV HF lfd) h’ >>
  ‘Readable x ∈ (server_v2 sockV H2 lfd).interest IH’
    by (qpat_x_assum ‘Readable x ∈ (with_store2 _ _ _ _).interest h’ mp_tac >>
        simp[with_store2_def, Abbr ‘IH’] >> rw[]) >>
  qspecl_then [‘sockV’, ‘H2’, ‘HF’, ‘lfd’] mp_tac
    (Q.GENL [‘V’, ‘h2’, ‘hf’, ‘lfd’] sv_acc) >>
  impl_tac
  >- (simp[vocab_ok_sockV, Abbr ‘H2’, proto_handler2_interest] >>
      ‘hcounts_v sockV HF’
        by (simp[Abbr ‘HF’] >> irule proto_v_hcounts >>
            simp[vocab_ok_sockV, vocab_qok_sockV]) >>
      fs[hcounts_v_def]) >>
  disch_then drule >>
  fs[Abbr ‘HF’] >> simp[trans_with_store, GSYM sproj_sockV, Abbr ‘IH’]
QED
