(*
  The query handler proto_handler_v (protoV) has the facts skeletonVActs
  asks of a handler, over any vocabulary with vocab_ok and vocab_qok
  (design/37 §5, step B): protoActs's proto_hcounts / proto_hacts for
  proto_handler_v, whose complete requests may emit a query (V.qry) before
  the write.  Queries are not socket actions (vocab_qok), so they do not
  count.

  MAIN: proto_v_hcounts, proto_v_hacts, proto_sv_new_actions.
*)
Theory protoVActs
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncTranscript echoServer
  echoServerSafety echoProgress skeleton echoBlockingWaits
  echoCause protoInterface protoCause skeletonActs skeletonV
  protoV skeletonVProgress skeletonVActs
Libs
  preamble

Overload HV = “λV P ansq fin fd buf. proto_handler_v V P ansq fin (fd, buf)”

Theorem NA_return[local]:
  NA (return x) h = []
Proof
  simp[new_actions_def, log_of_def, return_def]
QED

(* The vocabulary's socket actions *)
Theorem vocab_sact[local]:
  vocab_ok V ⇒
  V.sact (V.acc l) = SOME (Accept l) ∧ V.sact (V.rd fd) = SOME (Read fd) ∧
  V.sact (V.wr fd d) = SOME (Write fd d)
Proof
  simp[vocab_ok_def]
QED

Theorem counts_entries[local]:
  vocab_ok V ∧ vocab_qok V ⇒
  accs_v V g [(V.wr fd d, r)] = 0 ∧ eofs_v V g [(V.wr fd d, r)] = 0 ∧
  accs_v V g [(V.qry q, r)] = 0 ∧ eofs_v V g [(V.qry q, r)] = 0 ∧
  accs_v V g [(V.rd fd, r)] = 0 ∧
  eofs_v V g [(V.rd fd, r)] = (if g = fd ∧ OPTION_BIND r V.sres = SOME Eof then 1 else 0)
Proof
  rw[sproj_def, vocab_ok_def, vocab_qok_def, is_acc_def, is_eof_def] >> gvs[]
QED

(* ------------------------------------------------------------------------
   Counting accepts and EOFs
   ------------------------------------------------------------------------ *)

(* An emit, then a continuation: its transcript and result *)
(* bind_emit_CONS, closed, with type variables that cannot clash with a
   goal's: rewriting with MATCH_MP of an assumption fixes the theorem's type
   variables that also occur in the assumption *)
Theorem emit_cons[local]:
  ∀(s : ('zev, 'zres) snapshot) r (a : 'zact) (f : 'zres -> ('zev, 'zres) snapshot list -> ('zact, 'zr option) asyncCore$outcome) q.
  oHD s.results = SOME r ⇒
  bind (emit a) f (s :: q) = <| actions := a :: (f r q).actions; result := (f r q).result |>
Proof
  rpt strip_tac >>
  ‘first_done (emit a) [s] r’ by simp[first_done_def, emit_def] >>
  drule_then (Q.ISPECL_THEN [‘f’, ‘q’] mp_tac) bind_continues >>
  simp[new_actions_def, log_of_def, emit_def]
QED

Theorem emit_cons_result[local]:
  ∀(s : ('zev, 'zres) snapshot) r (a : 'zact) (f : 'zres -> ('zev, 'zres) snapshot list -> ('zact, 'zr option) asyncCore$outcome) q. oHD s.results = SOME r ∧ (bind (emit a) f (s :: q)).result = NONE ⇒
              (f r q).result = NONE
Proof
  rpt strip_tac >> drule_then (Q.ISPECL_THEN [‘a’, ‘f’, ‘q’] assume_tac) emit_cons >>
  gvs[]
QED

(* trans_bind_cases, closed, so that qspecl_then instantiates its types *)
Theorem trans_bind_cases_all:
  ∀m f h. wf m ∧ settled m ⇒
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ∧
  trans (bind m f) h = trans m h ∨
  ∃h1 h2 x. h = h1 ++ h2 ∧ first_done m h1 x ∧
            trans (bind m f) h = trans m h1 ++ trans (f x) h2
Proof
  rpt gen_tac >> MATCH_ACCEPT_TAC trans_bind_cases
QED

Theorem emit_split:
  ∀a f h.
  trans (bind (emit a) f) h = trans (emit a) h ∧
  (bind (emit a) f h).result = NONE ∨
  ∃s1 h2 r. h = s1 :: h2 ∧ oHD s1.results = SOME r ∧
            trans (bind (emit a) f) h = (a, SOME r) :: trans (f r) h2 ∧
            (bind (emit a) f h).result = (f r h2).result
Proof
  rpt gen_tac >>
  qspecl_then [‘emit a’, ‘f’, ‘h’] mp_tac trans_bind_cases_all >>
  simp[wf_emit, settled_emit] >> strip_tac
  >- (disj1_tac >> simp[] >> irule bind_result_running >> simp[])
  >> disj2_tac >> drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
  drule_then (Q.ISPECL_THEN [‘f’, ‘h2’] mp_tac) bind_continues >>
  simp[new_actions_def, log_of_def, emit_def]
QED

Theorem trans_emit_counts[local]:
  vocab_ok V ∧ vocab_qok V ⇒
  accs_v V g (trans (emit (V.wr fd d)) h) = 0 ∧ eofs_v V g (trans (emit (V.wr fd d)) h) = 0 ∧
  accs_v V g (trans (emit (V.qry q)) h) = 0 ∧ eofs_v V g (trans (emit (V.qry q)) h) = 0
Proof
  simp[trans_emit, counts_entries]
QED

Theorem counts_CONS_entry[local]:
  accs_v V g (p :: tr) = accs_v V g [p] + accs_v V g tr ∧
  eofs_v V g (p :: tr) = eofs_v V g [p] + eofs_v V g tr
Proof
  simp[sproj_def]
QED

Theorem sproj_NIL[local]:
  sproj V [] = []
Proof
  simp[sproj_def]
QED

(* The handler accepts nothing, reads EOF only on its fd, at most once, and
   only as its last step *)
Theorem proto_v_counts:
  vocab_ok V ∧ vocab_qok V ⇒
  ∀h buf. accs_v V g (trans (HV V P ansq fin fd buf) h) = 0 ∧
          (g ≠ fd ⇒ eofs_v V g (trans (HV V P ansq fin fd buf) h) = 0) ∧
          eofs_v V fd (trans (HV V P ansq fin fd buf) h) ≤ 1 ∧
          ((HV V P ansq fin fd buf h).result = NONE ⇒
           eofs_v V fd (trans (HV V P ansq fin fd buf) h) = 0)
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[proto_handler_v_unfold]
  >> Cases_on ‘P.parse buf’ >> simp[return_def, sproj_NIL]
  (* a complete request: (the query,) the write, then the rest *)
  >- (rename1 ‘PComplete req rest’ >> Cases_on ‘ansq req’ >> simp[]
      >- (qmatch_goalsub_abbrev_tac ‘bind (emit WR) K1’ >>
          qspecl_then [‘WR’, ‘K1’, ‘h’] strip_assume_tac
            emit_split >>
          gvs[Abbr ‘WR’, trans_emit_counts] >>
          ONCE_REWRITE_TAC[counts_CONS_entry] >> simp[counts_entries, Abbr ‘K1’] >>
          first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[])
      >> rename1 ‘ansq req = SOME q’ >>
      qmatch_goalsub_abbrev_tac ‘bind (emit QR) K1’ >>
      qspecl_then [‘QR’, ‘K1’, ‘h’] strip_assume_tac
        emit_split >>
      gvs[Abbr ‘QR’, trans_emit_counts] >>
      ONCE_REWRITE_TAC[counts_CONS_entry] >> simp[counts_entries, Abbr ‘K1’] >>
      qmatch_goalsub_abbrev_tac ‘bind (emit WR) K2’ >>
      qspecl_then [‘WR’, ‘K2’, ‘h2’] strip_assume_tac
        emit_split >>
      gvs[Abbr ‘WR’, trans_emit_counts] >>
      ONCE_REWRITE_TAC[counts_CONS_entry] >> simp[counts_entries, Abbr ‘K2’] >>
      first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[])
  (* incomplete: wait, read, continue *)
  >> qmatch_goalsub_abbrev_tac ‘bind (readable fd) K0’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       trans_bind_cases_all
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- (‘(bind (readable fd) K0 h).result = NONE’
        by (irule bind_result_running >> gvs[readable_def]) >>
      gvs[readable_def, sproj_def])
  >> drule first_done_wait_nonempty >> strip_tac
  >> ‘(bind (readable fd) K0 (h1 ++ h2)).result = (K0 () h2).result’
       by (irule bind_result_continues >> simp[readable_def, settled_wait])
  >> gvs[readable_def] >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘bind (emit RD) K1’
  >> qspecl_then [‘RD’, ‘K1’, ‘h2’] strip_assume_tac
       emit_split
  (* the read unanswered; or answered, but the handler is still running,
     so not with EOF *)
  >- (gvs[Abbr ‘RD’, trans_emit] >> simp[counts_entries] >>
      Cases_on ‘h2’ >> gvs[] >> rw[] >>
      drule_all emit_cons_result >> simp[Abbr ‘K1’, return_def])
  >> gvs[Abbr ‘RD’] >>
  ONCE_REWRITE_TAC[counts_CONS_entry] >> simp[counts_entries] >>
  ‘LENGTH h2' < LENGTH h1 + SUC (LENGTH h2')’ by (Cases_on ‘h1’ >> gvs[]) >>
  simp[Abbr ‘K1’] >>
  Cases_on ‘V.sres r’ >> simp[] >>
  TRY (rename1 ‘V.sres r = SOME x’ >> Cases_on ‘x’) >>
  simp[return_def, sproj_NIL] >>
  first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED

(* MAIN: the EOF bookkeeping skeletonVActs asks of a handler *)
Theorem proto_v_hcounts:
  vocab_ok V ∧ vocab_qok V ⇒ hcounts_v V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, buf))
Proof
  rw[hcounts_v_def] >> metis_tac[proto_v_counts]
QED

(* ------------------------------------------------------------------------
   Its actions
   ------------------------------------------------------------------------ *)

(* Started, the handler emits at most a query or a write *)
Theorem proto_v_init_actions:
  MEM a (HV V P ansq fin fd buf []).actions ⇒
  (∃q. a = V.qry q) ∨ ∃d. a = V.wr fd d
Proof
  ONCE_REWRITE_TAC[proto_handler_v_unfold] >>
  Cases_on ‘P.parse buf’ >> simp[return_def]
  >- (CASE_TAC >> simp[bind_emit_NIL] >> metis_tac[])
  >> qmatch_goalsub_abbrev_tac ‘bind RD G’ >>
  ‘bind RD G [] = <| actions := (RD []).actions; result := NONE |>’
    by (irule bind_running >> simp[Abbr ‘RD’, readable_def, wait_def, first_some_def]) >>
  simp[Abbr ‘RD’, readable_def, wait_def]
QED

Theorem init_not_acc_read[local]:
  vocab_ok V ∧ vocab_qok V ∧ ((∃q. a = V.qry q) ∨ ∃d. a = V.wr fd d) ⇒
  (∀l. V.sact a ≠ SOME (Accept l)) ∧ ∀g. V.sact a ≠ SOME (Read g)
Proof
  rw[vocab_ok_def, vocab_qok_def] >> simp[]
QED

(* Later, it accepts nothing, and reads its fd only when the fd is readable
   in the new snapshot, staying unfinished *)
Theorem proto_v_new_actions:
  vocab_ok V ∧ vocab_qok V ⇒
  ∀q s buf a. MEM a (NA (HV V P ansq fin fd buf) (q ++ [s])) ⇒
              (∀l. V.sact a ≠ SOME (Accept l)) ∧
              ∀g. V.sact a = SOME (Read g) ⇒
                  g = fd ∧ Readable fd ∈ s.ready ∧
                  (HV V P ansq fin fd buf (q ++ [s])).result = NONE
Proof
  strip_tac >> gen_tac >> completeInduct_on ‘LENGTH q’ >> rpt gen_tac >> strip_tac >>
  gvs[PULL_FORALL] >> rpt gen_tac >>
  ONCE_REWRITE_TAC[proto_handler_v_unfold] >>
  Cases_on ‘P.parse buf’ >> simp[NA_return]
  (* a complete request: (the query,) the write, then the rest *)
  >- (rename1 ‘PComplete req rest’ >> Cases_on ‘ansq req’ >> simp[]
      >- (strip_tac >> drule emit_new_v >> strip_tac >> gvs[]
          >- (drule proto_v_init_actions >> strip_tac >> metis_tac[init_not_acc_read])
          >> qpat_assum ‘oHD s1.results = SOME _’ (fn th => simp[MATCH_MP (SPEC_ALL emit_cons) th]) >>
          first_x_assum (qspecl_then [‘q'’, ‘s’] mp_tac) >> simp[] >>
          disch_then drule >> simp[])
      >> rename1 ‘ansq req = SOME qq’ >>
      strip_tac >> drule emit_new_v >> strip_tac >> gvs[]
      (* the query answered by s: the write is emitted *)
      >- (gvs[bind_emit_NIL] >> metis_tac[init_not_acc_read])
      >> qpat_assum ‘oHD s1.results = SOME _’ (fn th => simp[MATCH_MP (SPEC_ALL emit_cons) th]) >>
      qpat_x_assum ‘MEM _ (NA _ _)’ (assume_tac o BETA_RULE) >>
      drule emit_new_v >> strip_tac >> gvs[]
      >- (drule proto_v_init_actions >> strip_tac >> metis_tac[init_not_acc_read])
      >> qpat_assum ‘oHD s1'.results = SOME _’ (fn th => simp[MATCH_MP (SPEC_ALL emit_cons) th]) >>
      first_x_assum (qspecl_then [‘q''’, ‘s’] mp_tac) >> simp[] >>
      disch_then drule >> simp[])
  (* incomplete: wait, read, continue *)
  >> strip_tac >> drule rdy_new_v >> strip_tac
  >- (qmatch_asmsub_abbrev_tac ‘MEM a (G () []).actions’ >>
      ‘(bind (readable fd) G (q ++ [s] ++ [])).result = (G () []).result’
        by (irule bind_result_continues >>
            conj_tac >- simp[readable_def, settled_wait] >>
            simp[first_done_readable]) >>
      fs[] >> gvs[Abbr ‘G’, bind_emit_NIL, vocab_sact])
  >> qmatch_asmsub_abbrev_tac ‘MEM a (NA (G ()) (q2 ++ [s]))’
  >> ‘∀t. (bind (readable fd) G (h1 ++ t)).result = (G () t).result’
       by (gen_tac >> irule bind_result_continues >>
           conj_tac >- simp[readable_def, settled_wait] >>
           simp[first_done_readable])
  >> gvs[] >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> qpat_x_assum ‘∀t. _’ (fn th => REWRITE_TAC[th])
  >> fs[Abbr ‘G’] >> drule emit_new_v >> strip_tac >> gvs[]
  >- (Cases_on ‘V.sres r’ >> gvs[] >>
      TRY (rename1 ‘V.sres r = SOME x’ >> Cases_on ‘x’ >> gvs[return_def]) >>
      drule proto_v_init_actions >> strip_tac >> metis_tac[init_not_acc_read])
  >> qpat_assum ‘oHD s1.results = SOME _’ (fn th => simp[MATCH_MP (SPEC_ALL emit_cons) th])
  >> ‘LENGTH q' < LENGTH (h1 ++ s1 :: q')’ by simp[]
  >> Cases_on ‘V.sres r’ >> gvs[]
  >- (first_x_assum (qspecl_then [‘q'’, ‘s’] mp_tac) >> simp[] >>
      disch_then drule >> simp[])
  >> rename1 ‘V.sres r = SOME x’ >> Cases_on ‘x’ >> gvs[NA_return]
  >> first_x_assum (qspecl_then [‘q'’, ‘s’] mp_tac) >> simp[]
  >> disch_then drule >> simp[]
QED

(* MAIN: the action facts skeletonVActs asks of a handler *)
Theorem proto_v_hacts:
  vocab_ok V ∧ vocab_qok V ⇒ hacts_v V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, buf))
Proof
  rw[hacts_v_def, wf_proto_handler_v]
  >- (drule proto_v_init_actions >> strip_tac >> metis_tac[init_not_acc_read])
  >- (drule proto_v_init_actions >> strip_tac >> metis_tac[init_not_acc_read])
  >> metis_tac[proto_v_new_actions]
QED

(* MAIN: the library's server with query handlers accepts only when the
   listener is readable in the new snapshot, and reads g only when g is
   readable in it and g's handler has not finished *)
Theorem proto_sv_new_actions:
  vocab_ok V ∧ vocab_qok V ∧
  MEM a (NA (server_v V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, "")) lfd) (q ++ [s])) ⇒
  (∀l. V.sact a = SOME (Accept l) ⇒ l = lfd ∧ Readable lfd ∈ s.ready) ∧
  ∀g. V.sact a = SOME (Read g) ⇒
      Readable g ∈ s.ready ∧
      eofs_v V g (trans (server_v V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, "")) lfd) (q ++ [s])) <
      accs_v V g (trans (server_v V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, "")) lfd) (q ++ [s]))
Proof
  strip_tac >>
  ‘hcounts_v V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, "")) ∧
   hacts_v V (λfd. proto_handler_v V P (ansq fd) (fin fd) (fd, ""))’
    by simp[proto_v_hcounts, proto_v_hacts] >>
  drule_all sv_new_actions >> simp[]
QED
