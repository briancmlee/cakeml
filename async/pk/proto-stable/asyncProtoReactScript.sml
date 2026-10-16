(*
  The protocol server reacts to what it waits for (model, Level 2; option
  C, design/33 §2.5 (c)).  The converse of quiet: if the server waits for
  Readable x (waiting_on, its declared interest while running) and a new
  snapshot s has x ready, then it acts with s.

  - wait_react, emit_wait, both_react: the combinators;
  - proto2_reacts: the Level 2 protocol handler (any vocabulary);
  - sw2_reacts: the Level 2 skeleton server_with2, from its handlers;
  - proto_reacts: the HTTP instance (identity vocabulary, no queries),
    whose run is cf-actions' proto_server.

  With quiet, this pins down when the server acts: exactly when something
  it waits for is ready or a response arrives.

  MAIN: proto_reacts.
*)
Theory asyncProtoReact
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncServerWith asyncServer2 asyncHttpServer2H
  asyncM4LiveServer asyncProgress asyncLoop2 asyncServerV asyncProto asyncProtoServer asyncProtoV
  asyncProtoV2 asyncOCProtoModel asyncOCAcc asyncSWActs
Libs
  preamble

(* ------------------------------------------------------------------------
   The combinators
   ------------------------------------------------------------------------ *)

Theorem NA_wait[local]:
  NA (wait p) h = []
Proof
  simp[new_actions_def, log_of_def, wait_def]
QED

Theorem NA_emit_one[local]:
  NA (emit a) [s] = []
Proof
  simp[new_actions_def, log_of_def, emit_def]
QED

Theorem waiting_on_return2[simp]:
  waiting_on (return2 x) h = ∅
Proof
  simp[waiting_on_def, return2_def, return_def]
QED

(* Waiting for e, then KK: either the wait finishes with s, and KK starts;
   or it had finished, and KK waits for x *)
Theorem wait_react:
  x ∈ waiting_on (bind2 (wait_on e (λs. SOME ())) KK) h ∧ x ∈ s.ready ⇒
  NA (bind2 (wait_on e (λs. SOME ())) KK).run (h ++ [s]) = ((KK ()).run []).actions ∨
  ∃h1 h2. h = h1 ++ h2 ∧ h1 ≠ [] ∧ x ∈ waiting_on (KK ()) h2 ∧
          NA (bind2 (wait_on e (λs. SOME ())) KK).run (h ++ [s]) =
          NA (KK ()).run (h2 ++ [s])
Proof
  rw[waiting_on_def, bind2_def, wait_on_def] >>
  qmatch_asmsub_abbrev_tac ‘(bind w _ h).result’ >>
  ‘wf w ∧ settled w’ by simp[Abbr ‘w’, wf_wait, settled_wait] >>
  qspecl_then [‘w’, ‘h’] strip_assume_tac history_split
  (* still waiting: x is e, and s finishes the wait *)
  >- (‘bind_interest <| run := w; interest := K {e} |> KK h = {e}’
        by (DEP_REWRITE_TAC[bind_interest_running] >> simp[]) >>
      ‘x = e’ by (qpat_x_assum ‘x ∈ bind_interest _ _ _’ mp_tac >>
                  qpat_x_assum ‘bind_interest _ _ _ = _’ (fn th => simp[th])) >>
      pop_assum SUBST_ALL_TAC >> disj1_tac >>
      ‘first_done w (h ++ [s]) ()’
        by (simp[first_done_def] >> rpt strip_tac
            >- (qpat_x_assum ‘∀n. n ≤ LENGTH h ⇒ _’ (qspec_then ‘LENGTH h’ mp_tac) >>
                simp[Abbr ‘w’, wait_def, first_some_SNOC])
            >> qpat_x_assum ‘∀n. n ≤ LENGTH h ⇒ _’ (qspec_then ‘n’ mp_tac) >>
            simp[TAKE_APPEND1]) >>
      qspecl_then [‘w’, ‘h ++ [s]’, ‘()’, ‘λx. (KK ()).run’] mp_tac
        (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’] new_actions_bind_at) >>
      simp[] >> simp[Abbr ‘w’, NA_wait])
  (* the wait finished earlier *)
  >> rename1 ‘first_done w h1 uu’ >> Cases_on ‘uu’ >>
  disj2_tac >> qexistsl [‘h1’, ‘h2’] >> simp[] >>
  conj_tac >- (strip_tac >> gvs[Abbr ‘w’] >> metis_tac[first_done_wait_nonempty]) >>
  ‘bind_interest <| run := w; interest := K {e} |> KK (h1 ++ h2) = (KK ()).interest h2’
    by (irule bind_interest_settled >> simp[]) >>
  ‘(bind w (λx. (KK x).run) (h1 ++ h2)).result = ((KK ()).run h2).result’
    by (qspecl_then [‘w’, ‘h1’, ‘()’, ‘λx. (KK x).run’, ‘h2’] mp_tac
          (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] bind_result_continues) >> simp[]) >>
  gvs[] >>
  ‘NA w h1 = []’ by simp[Abbr ‘w’, NA_wait] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  qspecl_then [‘w’, ‘h1’, ‘()’, ‘h2 ++ [s]’, ‘λx. (KK x).run’] mp_tac
    (Q.GENL [‘m’, ‘h1’, ‘x’, ‘q’, ‘f’] new_actions_bind_after) >>
  simp[]
QED

(* Waiting for x after an emit: the emit was answered, and the
   continuation waits for x *)
Theorem emit_wait:
  x ∈ waiting_on (bind2 (emit2 a) KK) h ⇒
  ∃s1 hB r. h = s1 :: hB ∧ oHD s1.results = SOME r ∧ x ∈ waiting_on (KK r) hB ∧
            ∀s. NA (bind2 (emit2 a) KK).run (h ++ [s]) = NA (KK r).run (hB ++ [s])
Proof
  rw[waiting_on_def, bind2_def] >>
  ‘wf (emit2 a).run ∧ settled (emit2 a).run’ by simp[emit2_def, wf_emit, settled_emit] >>
  qspecl_then [‘(emit2 a).run’, ‘h’] strip_assume_tac history_split
  >- (‘bind_interest (emit2 a) KK h = (emit2 a).interest h’
        by (irule bind_interest_running >> simp[]) >>
      gvs[emit2_def])
  >> gvs[emit2_def] >> drule first_done_emit >> strip_tac >> gvs[] >>
  rename1 ‘oHD s1.results = SOME r’ >>
  ‘bind_interest (emit2 a) KK ([s1] ++ h2) = (KK r).interest h2’
    by (irule bind_interest_settled >> simp[emit2_def, settled_emit]) >>
  ‘(bind (emit a) (λx. (KK x).run) ([s1] ++ h2)).result = ((KK r).run h2).result’
    by (qspecl_then [‘emit a’, ‘[s1]’, ‘r’, ‘λx. (KK x).run’, ‘h2’] mp_tac
          (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’, ‘h2’] bind_result_continues) >>
        simp[settled_emit]) >>
  gvs[emit2_def] >> gen_tac >> qmatch_goalsub_rename_tac ‘_ :: (h2 ++ [ss])’ >>
  qspecl_then [‘emit a’, ‘[s1]’, ‘r’, ‘h2 ++ [ss]’, ‘λx. (KK x).run’] mp_tac
    (Q.GENL [‘m’, ‘h1’, ‘x’, ‘q’, ‘f’] new_actions_bind_after) >>
  simp[NA_emit_one]
QED

(* Two computations side by side: one that waits for x reacts to it *)
Theorem both_react:
  x ∈ waiting_on (map2 f (both2 c1 c2)) h ∧ x ∈ s.ready ∧
  (∀s'. x ∈ waiting_on c1 (left_view c1.run c2.run h) ∧ x ∈ s'.ready ⇒
        NA c1.run (left_view c1.run c2.run h ++ [s']) ≠ []) ∧
  (∀s'. x ∈ waiting_on c2 (right_view c1.run c2.run h) ∧ x ∈ s'.ready ⇒
        NA c2.run (right_view c1.run c2.run h ++ [s']) ≠ []) ⇒
  NA (map2 f (both2 c1 c2)).run (h ++ [s]) ≠ []
Proof
  rw[waiting_on_def, map2_def, both2_def] >>
  simp[both_new_actions, left_view_SNOC_eq, right_view_SNOC_eq] >>
  gvs[waiting_on_def] >> rw[] >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* ------------------------------------------------------------------------
   The handler and the skeleton
   ------------------------------------------------------------------------ *)

(* The Level 2 protocol handler reacts to what it waits for *)
Theorem proto2_reacts:
  ∀h buf s x.
    x ∈ waiting_on (proto_handler_v2 V P ansq fin (fd, buf)) h ∧ x ∈ s.ready ⇒
    NA (proto_handler_v2 V P ansq fin (fd, buf)).run (h ++ [s]) ≠ []
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘x ∈ waiting_on _ _’ mp_tac >>
  ONCE_REWRITE_TAC[proto_handler_v2_unfold] >> REWRITE_TAC[proto_body_v2_def] >>
  simp[] >> Cases_on ‘P.parse buf’ >> simp[]
  (* a complete request: one or two emits, then the rest *)
  >- (CASE_TAC
      >- (strip_tac >> drule emit_wait >> strip_tac >> gvs[] >>
          first_x_assum irule >> simp[] >> metis_tac[])
      >> strip_tac >> drule emit_wait >> strip_tac >> gvs[] >>
      drule emit_wait >> strip_tac >> gvs[] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  (* incomplete: the wait, then the read *)
  >> strip_tac >> drule_all wait_react >> strip_tac >> simp[]
  >- simp[bind2_def, emit2_def, bind_emit_NIL]
  >> gvs[] >> drule emit_wait >> strip_tac >> gvs[] >>
  ‘LENGTH hB < LENGTH (h1 ++ s1 :: hB)’ by simp[] >>
  qpat_x_assum ‘x ∈ waiting_on _ _’ mp_tac >>
  rpt CASE_TAC >> simp[] >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* The handler facts sw2_reacts needs *)
Definition hreacts_def:
  hreacts h2 ⇔
    ∀fd h s x. x ∈ waiting_on (h2 fd) h ∧ x ∈ s.ready ⇒ NA (h2 fd).run (h ++ [s]) ≠ []
End

Theorem server_with2_unfold[local]:
  server_with2 h2 lfd = server_with_body2 h2 (server_with2 h2) lfd
Proof
  simp[server_with2_def, Once (MATCH_MP fix2_unfold server_with_body2_contractive)]
QED

(* What the Level 2 skeleton does with the accept's response (named, to
   keep the terms small) *)
Definition sw2k_def:
  sw2k h2 lfd res =
    case res of
      Accepted fd => map2 (λp. ()) (both2 (h2 fd) (server_with2 h2 lfd))
    | _ => server_with2 h2 lfd
End

Theorem sw2_unfold_k[local]:
  server_with2 h2 lfd =
  bind2 (wait_on (Readable lfd) (λs. SOME ())) (λu. bind2 (emit2 (Accept lfd)) (sw2k h2 lfd))
Proof
  CONV_TAC (LAND_CONV (REWR_CONV server_with2_unfold)) >>
  REWRITE_TAC[server_with_body2_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, sw2k_def]
QED

(* MAIN: the Level 2 skeleton reacts to what it waits for, if its handlers
   do *)
Theorem sw2_reacts:
  hreacts h2 ⇒
  ∀h s x. x ∈ waiting_on (server_with2 h2 lfd) h ∧ x ∈ s.ready ⇒
          NA (server_with2 h2 lfd).run (h ++ [s]) ≠ []
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘x ∈ waiting_on _ _’ (mp_tac o ONCE_REWRITE_RULE[sw2_unfold_k]) >>
  ONCE_REWRITE_TAC[sw2_unfold_k] >>
  strip_tac >> drule_all wait_react >> strip_tac >> ASM_REWRITE_TAC[]
  (* the wait finishes with s: the accept *)
  >- simp[bind2_def, emit2_def, bind_emit_NIL]
  >> qpat_x_assum ‘x ∈ waiting_on ((λu. _) ()) _’ (assume_tac o BETA_RULE) >>
  drule emit_wait >> strip_tac >>
  ASM_REWRITE_TAC[] >>
  ‘LENGTH hB < LENGTH h’ by gvs[] >>
  Cases_on ‘∃fd. r = Accepted fd’
  (* a new connection: its handler, beside the rest of the server *)
  >- (gvs[sw2k_def] >> irule both_react >> qexists_tac ‘x’ >> simp[] >>
      conj_tac
      >- (gvs[hreacts_def] >> metis_tac[])
      >> rpt strip_tac >>
      first_x_assum (qspec_then ‘right_view (h2 fd).run (server_with2 h2 lfd).run hB’ mp_tac) >>
      simp[] >> metis_tac[])
  (* no new connection: the server again *)
  >> ‘sw2k h2 lfd r = server_with2 h2 lfd’ by (Cases_on ‘r’ >> gvs[sw2k_def])
  >> gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* MAIN: the protocol server (identity vocabulary, no queries) reacts to
   what it waits for: if it waits for Readable x and x is ready in the
   new snapshot, cf-actions' proto_server acts *)
Theorem proto_reacts:
  Readable x ∈ waiting_on (proto_server_v2 idVu P (K (NONE : unit option))
                             (λr (k : unit option). resp r) lfd) h ∧
  Readable x ∈ s.ready ⇒
  NA (proto_server P resp lfd) (h ++ [s]) ≠ []
Proof
  strip_tac >>
  ‘(proto_server_v2 idVu P (K NONE) (λr k. resp r) lfd).run = proto_server P resp lfd’
    by simp[GSYM erase_def, erase_proto_server_idV2] >>
  pop_assum (SUBST1_TAC o SYM) >>
  gvs[proto_server_v2_def, server_v2_idV] >>
  irule sw2_reacts >> simp[hreacts_def] >> rpt conj_tac
  >- (rpt strip_tac >> drule_all proto2_reacts >> simp[])
  >> metis_tac[]
QED
