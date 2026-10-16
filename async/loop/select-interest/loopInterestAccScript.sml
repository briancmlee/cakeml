(*
  Option C §2.5 (a), model side: the Level 2 protocol server waits only for
  the listener and for connections it has accepted.

  - server_v2_idV: for the identity vocabulary, server_v2 is #53's
    server_with2;
  - sw_acc: the generic skeleton at Level 2, with a handler that accepts
    nothing and waits for nothing but its own fd, waits only for Readable
    lfd and Readable fd of fds it has accepted (#56's sw_live, without
    the EOF bookkeeping);
  - proto_acc: so for the protocol server (proto_handler_serves,
    proto_handler2_interest).

  MAIN: sw_acc, proto_acc.
*)
Theory loopInterestAcc
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 asyncTranscript
  echoServer echoServerSafety echoServer2 skeleton skeleton2
  echoBlockingWaits skeletonV protoInterface protoServer protoV
  proto2 proto2SockModel
Libs
  preamble

Theorem server_with2_unfold[local]:
  server_with2 h2 lfd = server_with_body2 h2 (server_with2 h2) lfd
Proof
  simp[server_with2_def, Once (MATCH_MP fix2_unfold server_with_body2_contractive)]
QED

Theorem server_with2_run[local]:
  (∀fd. (h2 fd).run = hf fd) ⇒ (server_with2 h2 lfd).run = server_with hf lfd
Proof
  strip_tac >>
  ‘∀fd. erase (h2 fd) = hf fd’ by simp[erase_def] >>
  drule erase_server_with2 >> simp[erase_def]
QED

(* MAIN: for the identity vocabulary, the skeleton is server_with2 *)
Theorem server_v2_idV:
  server_v2 idVu h2 = server_with2 h2
Proof
  ‘server_v_body2 idVu h2 = server_with_body2 h2’
    by (simp[FUN_EQ_THM, server_v_body2_def, server_with_body2_def, idV_def] >>
        rpt gen_tac >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >>
        rename1 ‘vaccd _ res’ >> Cases_on ‘res’ >>
        simp[vaccd_def, idV_def]) >>
  simp[server_v2_def, server_with2_def, FUN_EQ_THM]
QED

(* MAIN: what the generic skeleton waits for *)
Theorem sw_acc:
  (∀fd. (h2 fd).run = hf fd) ∧
  (∀fd h g. accs g (trans (hf fd) h) = 0) ∧
  (∀fd h. (h2 fd).interest h ⊆ {Readable fd}) ⇒
  ∀h x. Readable x ∈ (server_with2 h2 lfd).interest h ⇒
        x = lfd ∨ 0 < accs x (trans (server_with hf lfd) h)
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ‘trans (server_with hf lfd) h = trans (server_with2 h2 lfd).run h’
       by (drule server_with2_run >> simp[])
  >> pop_assum SUBST1_TAC
  >> ONCE_REWRITE_TAC[server_with2_unfold] >> REWRITE_TAC[server_with_body2_def]
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
  >> ‘(server_with2 h2 lfd).run = server_with hf lfd’ by (drule server_with2_run >> simp[])
  >> reverse (Cases_on ‘res’) >> simp[is_acc_def]
  >> TRY (qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘hB’ mp_tac) >> simp[] >>
          NO_TAC)
  >> rename1 ‘Accepted fd’
  >> simp[map2_def, both2_def, trans_both_counts]
  >> qabbrev_tac ‘L = left_view (hf fd) (server_with hf lfd) hB’
  >> qabbrev_tac ‘R = right_view (hf fd) (server_with hf lfd) hB’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH hB + 1)’ by simp[Abbr ‘R’]
  >> strip_tac
  >- ((* the handler waits for it: x = fd, the accepted one *)
      drule waiting_on_interest >> strip_tac >>
      ‘Readable x ∈ {Readable fd}’ by metis_tac[SUBSET_DEF] >> gvs[])
  >> drule waiting_on_interest >> strip_tac
  >> qpat_x_assum ‘∀y. LENGTH y < _ ⇒ _’ (qspec_then ‘R’ mp_tac) >> simp[]
  >> disch_then drule >> simp[]
QED

(* bind_interest_cases at the level of bind2 (which ties the types) *)
Theorem bind2_interest_cases[local]:
  wf c.run ∧ settled c.run ⇒
  (∀n. n ≤ LENGTH h ⇒ (c.run (TAKE n h)).result = NONE) ∧
  (bind2 c f).interest h = c.interest h ∨
  ∃h1 h2 x. h = h1 ++ h2 ∧ first_done c.run h1 x ∧
            (bind2 c f).interest h = (f x).interest h2
Proof
  simp[bind2_def, bind_interest_cases]
QED

(* After an emit2, a bind2 waits for what its continuation waits for, on a
   shorter history *)
Theorem bind2_emit2_sub[local]:
  (∀x h'. LENGTH h' < LENGTH h ⇒ (f x).interest h' ⊆ E) ⇒
  (bind2 (emit2 a) f).interest h ⊆ E
Proof
  strip_tac >> simp[bind2_def]
  >> qmatch_goalsub_abbrev_tac ‘bind_interest C2 K2 h’
  >> qspecl_then [‘C2’, ‘K2’, ‘h’] mp_tac
       (Q.GENL [‘c’, ‘f’, ‘h’] bind_interest_cases)
  >> impl_tac >- simp[Abbr ‘C2’, emit2_def, wf_emit, settled_emit]
  >> strip_tac >> simp[]
  >- simp[Abbr ‘C2’, emit2_def]
  >> gvs[Abbr ‘C2’, Abbr ‘K2’, emit2_def]
  >> drule first_done_emit >> strip_tac >> gvs[]
  >> first_x_assum irule >> simp[]
QED

(* After a wait_on e, likewise, and the wait itself declares e *)
Theorem bind2_wait_on_sub[local]:
  e ∈ E ∧ (∀x h'. LENGTH h' < LENGTH h ⇒ (f x).interest h' ⊆ E) ⇒
  (bind2 (wait_on e p) f).interest h ⊆ E
Proof
  strip_tac
  >> qspecl_then [‘wait_on e p’, ‘f’, ‘h’] mp_tac
       (Q.GENL [‘c’, ‘f’, ‘h’] bind2_interest_cases)
  >> impl_tac >- simp[wait_on_def, wf_wait, settled_wait]
  >> strip_tac >> ASM_REWRITE_TAC[]
  >- gvs[wait_on_def]
  >> ‘h1 ≠ []’ by (gvs[wait_on_def] >> metis_tac[first_done_wait_nonempty])
  >> qpat_x_assum ‘∀x h'. _’ irule >> Cases_on ‘h1’ >> gvs[]
QED

(* The protocol handler at Level 2 waits for nothing but its own fd *)
Theorem proto_handler2_interest:
  ∀h buf. (proto_handler_v2 V P ansq fin (fd, buf)).interest h ⊆ {Readable fd}
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[proto_handler_v2_unfold] >> REWRITE_TAC[proto_body_v2_def]
  >> simp[]
  >> Cases_on ‘P.parse buf’ >> simp[return2_def]
  >- (CASE_TAC
      >- (irule bind2_emit2_sub >> rpt strip_tac >> BETA_TAC >>
          first_x_assum irule >> simp[])
      >> irule bind2_emit2_sub >> rpt strip_tac >> BETA_TAC >>
      irule bind2_emit2_sub >> rpt strip_tac >> BETA_TAC >>
      first_x_assum irule >> fs[])
  >> irule bind2_wait_on_sub >> simp[] >> rpt strip_tac >> BETA_TAC
  >> irule bind2_emit2_sub >> rpt strip_tac >> BETA_TAC
  >> rpt CASE_TAC >> simp[return2_def] >> first_x_assum irule >> fs[]
QED

(* The protocol handler accepts nothing *)
Theorem proto_handler_accs:
  proto_ok P ⇒ ∀g. accs g (trans (proto_handler P resp (fd, buf)) h) = 0
Proof
  rw[] >> drule proto_handler_serves >>
  disch_then (qspecl_then [‘resp’, ‘fd’, ‘h’, ‘buf’] strip_assume_tac) >>
  ‘EVERY (λp. ¬is_acc g p) (trans (proto_handler P resp (fd, buf)) h)’
    suffices_by simp[accs_def, LENGTH_NIL, FILTER_EQ_NIL] >>
  irule EVERY_MONOTONIC >> first_assum (irule_at Any) >>
  Cases >> simp[on_fd_def, is_acc_def] >> rw[] >> simp[]
QED

(* MAIN: the protocol server waits only for the listener and the
   connections it accepted *)
Theorem proto_acc:
  proto_ok P ⇒
  ∀h x. Readable x ∈ waiting_on (proto_server_v2 idVu P (K (NONE : unit option))
                                   (λr (k : unit option). resp r) lfd) h ⇒
        x = lfd ∨ 0 < accs x (trans (proto_server P resp lfd) h)
Proof
  rpt strip_tac >> drule waiting_on_interest >> strip_tac >>
  gvs[proto_server_v2_def, server_v2_idV, proto_server_def] >>
  qpat_x_assum ‘Readable x ∈ _.interest h’ mp_tac >>
  qid_spec_tac ‘x’ >> qid_spec_tac ‘h’ >>
  ho_match_mp_tac sw_acc >> rpt conj_tac
  >- simp[GSYM erase_def, erase_proto_handler_v2, GSYM proto_handler_idV]
  >- metis_tac[proto_handler_accs]
  >> simp[proto_handler2_interest]
QED
