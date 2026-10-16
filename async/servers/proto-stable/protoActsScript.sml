(*
  What the generic protocol server's actions need (model; option C,
  design/33 §2.5 (c)): the protocol handler has the facts skeletonActs asks
  of a handler (proto_hcounts, proto_hacts), so

  - the protocol server accepts only when the listener is readable in the
    new snapshot, and
  - reads a connection g only when g is readable in it and the server has
    accepted g more often than it has read g's EOF
  (proto_server_new_actions).  For every protocol (no hypothesis on P).

  MAIN: proto_server_new_actions.
*)
Theory protoActs
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncTranscript echoServer
  echoServerSafety echoProgress skeleton echoBlockingWaits
  echoCause protoInterface protoServer protoCause skeletonActs
Libs
  preamble

Overload H = “λP resp fd buf. proto_handler P resp (fd, buf)”

Theorem NA_return[local]:
  NA (return x) h = []
Proof
  simp[new_actions_def, log_of_def, return_def]
QED

(* ------------------------------------------------------------------------
   Counting accepts and EOFs
   ------------------------------------------------------------------------ *)

(* The handler accepts nothing, reads EOF only on its fd, at most once, and
   only as its last step *)
Theorem proto_handler_counts:
  ∀h buf. accs g (trans (H P resp fd buf) h) = 0 ∧
          (g ≠ fd ⇒ eofs g (trans (H P resp fd buf) h) = 0) ∧
          eofs fd (trans (H P resp fd buf) h) ≤ 1 ∧
          ((H P resp fd buf h).result = NONE ⇒ eofs fd (trans (H P resp fd buf) h) = 0)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[proto_handler_unfold]
  >> Cases_on ‘P.parse buf’ >> simp[return_def]
  (* a complete request: the write, then the rest *)
  >- (rename1 ‘PComplete req rest’
      >> qmatch_goalsub_abbrev_tac ‘bind (emit WR) K1’
      >> qspecl_then [‘emit WR’, ‘K1’, ‘h’] mp_tac
           (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
      >> simp[wf_emit, settled_emit] >> strip_tac
      >- gvs[trans_emit, is_acc_def, is_eof_def, Abbr ‘WR’]
      >> ‘(bind (emit WR) K1 (h1 ++ h2)).result = (K1 x h2).result’
           by (irule bind_result_continues >> simp[settled_emit])
      >> drule first_done_emit >> strip_tac
      >> gvs[trans_emit, is_acc_def, is_eof_def, Abbr ‘WR’, Abbr ‘K1’]
      >> first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[])
  (* incomplete: wait, read, continue *)
  >> qmatch_goalsub_abbrev_tac ‘bind (readable fd) K0’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- (‘(bind (readable fd) K0 h).result = NONE’
        by (irule bind_result_running >> gvs[readable_def]) >>
      gvs[readable_def])
  >> drule first_done_wait_nonempty >> strip_tac
  >> ‘(bind (readable fd) K0 (h1 ++ h2)).result = (K0 () h2).result’
       by (irule bind_result_continues >> simp[readable_def, settled_wait])
  >> gvs[readable_def] >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘bind (emit (Read fd)) K1’
  >> qspecl_then [‘emit (Read fd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (‘(bind (emit (Read fd)) K1 h2).result = NONE’
        by (irule bind_result_running >> simp[]) >>
      gvs[trans_emit] >> Cases_on ‘h2’ >> simp[is_acc_def, is_eof_def] >>
      first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def] >>
      Cases_on ‘oHD h.results’ >> simp[])
  >> ‘(bind (emit (Read fd)) K1 (h1' ++ h2')).result = (K1 x h2').result’
       by (irule bind_result_continues >> simp[settled_emit])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> Cases_on ‘res’ >> simp[is_acc_def, is_eof_def, return_def]
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED

(* MAIN: the facts skeletonActs asks of a handler, EOF bookkeeping *)
Theorem proto_hcounts:
  hcounts (λfd. proto_handler P resp (fd, buf))
Proof
  rw[hcounts_def] >> metis_tac[proto_handler_counts]
QED

(* ------------------------------------------------------------------------
   Its actions
   ------------------------------------------------------------------------ *)

(* Started, the handler emits at most a write *)
Theorem proto_init_actions:
  MEM a (H P resp fd buf []).actions ⇒ ∃d. a = Write fd d
Proof
  ONCE_REWRITE_TAC[proto_handler_unfold] >>
  Cases_on ‘P.parse buf’ >> simp[return_def, bind_emit_NIL] >>
  qmatch_goalsub_abbrev_tac ‘bind (readable fd) G’ >>
  ‘bind (rdy fd) G [] = <| actions := (rdy fd []).actions; result := NONE |>’
    by (irule bind_running >> simp[readable_def, wait_def, first_some_def]) >>
  simp[readable_def, wait_def]
QED

(* Later, it accepts nothing, and reads its fd only when the fd is readable
   in the new snapshot, staying unfinished *)
Theorem proto_new_actions:
  ∀q s buf a. MEM a (NA (H P resp fd buf) (q ++ [s])) ⇒
              (∀l. a ≠ Accept l) ∧
              ∀g. a = Read g ⇒ g = fd ∧ Readable fd ∈ s.ready ∧
                               (H P resp fd buf (q ++ [s])).result = NONE
Proof
  gen_tac >> completeInduct_on ‘LENGTH q’ >> rpt gen_tac >> strip_tac >>
  gvs[PULL_FORALL] >> rpt gen_tac >>
  ONCE_REWRITE_TAC[proto_handler_unfold] >>
  Cases_on ‘P.parse buf’ >> simp[NA_return]
  (* a complete request: the write, then the rest *)
  >- (strip_tac >> drule emit_new >> strip_tac >> gvs[]
      >- (drule proto_init_actions >> strip_tac >> simp[])
      >> qpat_assum ‘oHD s1.results = SOME _’ (fn th => simp[MATCH_MP bind_emit_CONS th]) >>
      first_x_assum (qspecl_then [‘q'’, ‘s’] mp_tac) >> simp[] >>
      disch_then drule >> simp[])
  (* incomplete: wait, read, continue *)
  >> strip_tac >> drule rdy_new >> strip_tac
  >- (qmatch_asmsub_abbrev_tac ‘MEM a (G () []).actions’ >>
      ‘(bind (readable fd) G (q ++ [s] ++ [])).result = (G () []).result’
        by (irule bind_result_continues >>
            gvs[first_readable_def, readable_def, settled_wait]) >>
      fs[] >> gvs[Abbr ‘G’, bind_emit_NIL])
  >> qmatch_asmsub_abbrev_tac ‘MEM a (NA (G ()) (q2 ++ [s]))’
  >> ‘∀t. (bind (readable fd) G (h1 ++ t)).result = (G () t).result’
       by (gen_tac >> irule bind_result_continues >>
           gvs[first_readable_def, readable_def, settled_wait])
  >> gvs[] >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> qpat_x_assum ‘∀t. _’ (fn th => REWRITE_TAC[th])
  >> fs[Abbr ‘G’] >> drule emit_new >> strip_tac >> gvs[]
  >- (Cases_on ‘r’ >> gvs[return_def] >>
      drule proto_init_actions >> strip_tac >> simp[])
  >> qpat_assum ‘oHD s1.results = SOME _’ (fn th => simp[MATCH_MP bind_emit_CONS th])
  >> ‘LENGTH q' < LENGTH (h1 ++ s1 :: q')’ by simp[]
  >> Cases_on ‘r’ >> gvs[NA_return]
  >> first_x_assum (qspecl_then [‘q'’, ‘s’] mp_tac) >> simp[]
  >> disch_then drule >> simp[]
QED

(* MAIN: the facts skeletonActs asks of a handler, actions *)
Theorem proto_hacts:
  hacts (λfd. proto_handler P resp (fd, buf))
Proof
  rw[hacts_def, wf_proto_handler]
  >- (drule proto_init_actions >> strip_tac >> simp[])
  >- (drule proto_init_actions >> strip_tac >> simp[])
  >> drule proto_new_actions >> simp[]
QED

(* MAIN: the protocol server accepts only when the listener is readable in
   the new snapshot, and reads g only when g is readable in it and g's
   handler has not finished *)
Theorem proto_server_new_actions:
  MEM a (NA (proto_server P resp lfd) (q ++ [s])) ⇒
  (∀l. a = Accept l ⇒ l = lfd ∧ Readable lfd ∈ s.ready) ∧
  ∀g. a = Read g ⇒ Readable g ∈ s.ready ∧
                   eofs g (trans (proto_server P resp lfd) (q ++ [s])) <
                   accs g (trans (proto_server P resp lfd) (q ++ [s]))
Proof
  simp[proto_server_def] >> strip_tac >>
  qspecl_then [‘λfd. proto_handler P resp (fd, "")’, ‘lfd’] mp_tac
    (Q.GENL [‘hf’, ‘lfd’] sw_new_actions) >>
  simp[proto_hcounts, proto_hacts] >> disch_then drule >> simp[]
QED
