(*
  The Level 2 skeleton over any vocabulary reacts to what it waits for
  with a socket action (design/37 §5, step C3): protoReact's
  sw2_reacts and proto2_reacts, for server_v2, with "acts" sharpened to
  "performs a socket action".  The sharpening matters under a store:
  with_store shows only the socket actions, so a reaction by a query
  alone would not show.

  - both_react_s: two computations side by side;
  - proto2_reacts_s: the Level 2 query handler (a wait for its fd ends in
    a read);
  - sv2_reacts_s: the Level 2 skeleton server_v2, from its handlers (a
    wait for the listener ends in an accept).

  MAIN: sv2_reacts_s, proto2_reacts_s.
*)
Theory storeReact
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServerSafety skeleton echoServer2 echoProgress asyncLoop2
  skeletonV protoInterface protoV proto2 protoReact
Libs
  preamble

(* The computation performs a socket action in the new round *)
Overload sacts_new = “λV m h. ∃a. MEM a (NA m h) ∧ V.sact a ≠ NONE”

(* The handler facts sv2_reacts_s needs *)
Definition hreacts_v_def:
  hreacts_v V h2 ⇔
    ∀fd h s x. x ∈ waiting_on (h2 fd) h ∧ x ∈ s.ready ⇒
               sacts_new V (h2 fd).run (h ++ [s])
End

(* Two computations side by side: one that waits for x reacts to it *)
Theorem both_react_s:
  x ∈ waiting_on (map2 f (both2 c1 c2)) h ∧ x ∈ s.ready ∧
  (∀s'. x ∈ waiting_on c1 (left_view c1.run c2.run h) ∧ x ∈ s'.ready ⇒
        sacts_new V c1.run (left_view c1.run c2.run h ++ [s'])) ∧
  (∀s'. x ∈ waiting_on c2 (right_view c1.run c2.run h) ∧ x ∈ s'.ready ⇒
        sacts_new V c2.run (right_view c1.run c2.run h ++ [s'])) ⇒
  sacts_new V (map2 f (both2 c1 c2)).run (h ++ [s])
Proof
  rw[waiting_on_def, map2_def, both2_def] >>
  simp[both_new_actions, left_view_SNOC_eq, right_view_SNOC_eq] >>
  gvs[waiting_on_def] >>
  (* the snapshots the two sides see have s's ready set *)
  qmatch_goalsub_abbrev_tac ‘NA c1.run (_ ++ [S1])’ >>
  qmatch_goalsub_abbrev_tac ‘NA c2.run (_ ++ [S2])’ >>
  ‘x ∈ S1.ready ∧ x ∈ S2.ready’ by simp[Abbr ‘S1’, Abbr ‘S2’] >>
  metis_tac[]
QED

(* MAIN: the Level 2 query handler reacts to what it waits for with a
   socket action *)
Theorem proto2_reacts_s:
  vocab_ok V ⇒
  ∀h buf s x.
    x ∈ waiting_on (proto_handler_v2 V P ansq fin (fd, buf)) h ∧ x ∈ s.ready ⇒
    sacts_new V (proto_handler_v2 V P ansq fin (fd, buf)).run (h ++ [s])
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt gen_tac >> strip_tac >>
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
  >- (simp[bind2_def, emit2_def, bind_emit_NIL] >> fs[vocab_ok_def])
  >> gvs[] >> drule emit_wait >> strip_tac >> gvs[] >>
  ‘LENGTH hB < LENGTH (h1 ++ s1 :: hB)’ by simp[] >>
  qpat_x_assum ‘x ∈ waiting_on _ _’ mp_tac >>
  rpt CASE_TAC >> simp[] >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* What the Level 2 skeleton does with the accept's response (named, to
   keep the terms small) *)
Definition sv2k_def:
  sv2k V h2 lfd res =
    case vaccd V res of
      SOME fd => map2 (λp. ()) (both2 (h2 fd) (server_v2 V h2 lfd))
    | NONE => server_v2 V h2 lfd
End

Theorem server_v2_unfold_k[local]:
  server_v2 V h2 lfd =
  bind2 (wait_on (Readable lfd) (λs. SOME ())) (λu.
  bind2 (emit2 (V.acc lfd)) (sv2k V h2 lfd))
Proof
  CONV_TAC (LAND_CONV (REWR_CONV server_v2_unfold)) >>
  REWRITE_TAC[server_v_body2_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, sv2k_def]
QED

(* MAIN: the Level 2 skeleton reacts to what it waits for with a socket
   action, if its handlers do *)
Theorem sv2_reacts_s:
  vocab_ok V ∧ hreacts_v V h2 ⇒
  ∀h s x. x ∈ waiting_on (server_v2 V h2 lfd) h ∧ x ∈ s.ready ⇒
          sacts_new V (server_v2 V h2 lfd).run (h ++ [s])
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘x ∈ waiting_on _ _’ (mp_tac o ONCE_REWRITE_RULE[server_v2_unfold_k]) >>
  ONCE_REWRITE_TAC[server_v2_unfold_k] >>
  strip_tac >> drule_all wait_react >> strip_tac >> ASM_REWRITE_TAC[]
  (* the wait finishes with s: the accept *)
  >- (simp[bind2_def, emit2_def, bind_emit_NIL] >> fs[vocab_ok_def])
  >> qpat_x_assum ‘x ∈ waiting_on ((λu. _) ()) _’ (assume_tac o BETA_RULE) >>
  drule emit_wait >> strip_tac >>
  ASM_REWRITE_TAC[] >>
  ‘LENGTH hB < LENGTH h’ by gvs[] >>
  Cases_on ‘vaccd V r’ >> gvs[sv2k_def]
  (* no new connection: the server again *)
  >- (first_x_assum irule >> simp[] >> metis_tac[])
  (* a new connection: its handler, beside the rest of the server *)
  >> irule both_react_s >> qexists_tac ‘x’ >> simp[] >>
  conj_tac
  >- (gvs[hreacts_v_def] >> metis_tac[])
  >> rpt strip_tac >>
  first_x_assum (qspec_then ‘right_view (h2 x').run (server_v2 V h2 lfd).run hB’ mp_tac) >>
  simp[] >> metis_tac[]
QED
