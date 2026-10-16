(*
  Relabelling distributes over the library's combinators (model).

  relabel fa fs m (relabel) runs m in another vocabulary.  When the
  snapshot translation fs is pointwise on the responses (snap_map: the
  ready set by fe, each response by fr), relabelling commutes with return,
  wait, map, bind and both, and turns emit a into
  map fr (emit (fa a)).  So the relabelled echo server is again a library
  computation, written in the socket vocabulary, which is what the CakeML
  code in that vocabulary implements (echoSockServer).
*)
Theory relabelDist
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncLevel2
  asyncTranscript relabel
Libs
  BasicProvers

(* A snapshot translation that is pointwise on the responses *)
Definition snap_map_def:
  snap_map fe fr (s : ('e, 'r) snapshot) =
    <| ready := fe s.ready; now := s.now; results := MAP fr s.results |>
End

Theorem log_of_relabel:
  log_of (relabel fa fs m) h = MAP fa (log_of m (MAP fs h))
Proof
  simp[log_of_def, relabel_def]
QED

Theorem first_prefix_MAP:
  ∀f h P. first_prefix (λp. P (MAP f p)) h = first_prefix P (MAP f h)
Proof
  gen_tac >> Induct >> simp[Once first_prefix_def]
  >- simp[Once first_prefix_def]
  >> rpt gen_tac >> CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [first_prefix_def]))
  >> simp[] >> rw[]
  >> first_x_assum (qspec_then ‘λu. P (f h :: u)’ mp_tac) >> simp[]
QED

Theorem skip_results_MAP:
  skip_results k (MAP (snap_map fe fr) h) =
  MAP (snap_map fe fr) (skip_results k h)
Proof
  Cases_on ‘h’ >> simp[skip_results_def, snap_map_def, MAP_DROP]
QED

Theorem relabel_return:
  relabel fa fs (return x) = return x
Proof
  simp[FUN_EQ_THM, relabel_def, return_def]
QED

Theorem first_some_MAP[local]:
  ∀h. first_some p (MAP f h) = first_some (p o f) h
Proof
  Induct >> simp[first_some_def]
QED

Theorem relabel_wait:
  relabel fa fs (wait p) = wait (p o fs)
Proof
  simp[FUN_EQ_THM, relabel_def, wait_def, first_some_MAP]
QED

(* emit, relabelled: emit the translated action, and translate its
   response back *)
Theorem relabel_emit:
  relabel fa (snap_map fe fr) (emit a) = map fr (emit (fa a))
Proof
  simp[FUN_EQ_THM, relabel_def, emit_def, map_def] >> Cases >>
  simp[snap_map_def] >> Cases_on ‘h.results’ >> simp[]
QED

Theorem relabel_map:
  relabel fa fs (map f m) = map f (relabel fa fs m)
Proof
  simp[FUN_EQ_THM, relabel_def, map_def]
QED

(* MAIN: relabelling distributes over bind *)
Theorem relabel_bind:
  relabel fa (snap_map fe fr) (bind m f) =
  bind (relabel fa (snap_map fe fr) m) (λx. relabel fa (snap_map fe fr) (f x))
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac ‘h’ >>
  simp[relabel_def, bind_def] >>
  ‘first_prefix (λp. (m (MAP (snap_map fe fr) p)).result ≠ NONE) h =
   first_prefix (λp. (m p).result ≠ NONE) (MAP (snap_map fe fr) h)’
    by (qspecl_then [‘snap_map fe fr’, ‘h’, ‘λq. (m q).result ≠ NONE’] mp_tac
          first_prefix_MAP >> simp[]) >>
  simp[] >> CASE_TAC >> simp[GSYM MAP_TAKE, new_actions_relabel, GSYM MAP_DROP,
                             skip_results_MAP]
QED

(* The views of both, relabelled *)
Theorem par_views_relabel:
  ∀fa fe fr m1 m2 h. par_views (log_of m1) (log_of m2) (MAP (snap_map fe fr) h) =
      (MAP (snap_map fe fr)
         (FST (par_views (log_of (relabel fa (snap_map fe fr) m1))
                         (log_of (relabel fa (snap_map fe fr) m2)) h)),
       MAP (snap_map fe fr)
         (SND (par_views (log_of (relabel fa (snap_map fe fr) m1))
                         (log_of (relabel fa (snap_map fe fr) m2)) h)))
Proof
  ntac 5 gen_tac >>
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, par_views_SNOC] >>
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac ‘par_views A1 A2 h’ >>
  Cases_on ‘par_views A1 A2 h’ >> gvs[] >>
  simp[Abbr ‘A1’, GSYM relabel_def, new_actions_relabel] >>
  simp[snap_map_def, MAP_TAKE, MAP_DROP]
QED

Theorem par_views_relabel_SNOC[local]:
  par_views (log_of (relabel fa (snap_map fe fr) m1))
            (log_of (relabel fa (snap_map fe fr) m2)) (h ++ [x]) = (q, r) ⇒
  par_views (log_of m1) (log_of m2) (MAP (snap_map fe fr) h ++ [snap_map fe fr x]) =
  (MAP (snap_map fe fr) q, MAP (snap_map fe fr) r)
Proof
  strip_tac >>
  ‘MAP (snap_map fe fr) h ++ [snap_map fe fr x] = MAP (snap_map fe fr) (h ++ [x])’
    by simp[] >>
  pop_assum SUBST1_TAC >>
  metis_tac[par_views_relabel, pairTheory.FST, pairTheory.SND]
QED

Theorem par_actions_relabel:
  ∀h. par_actions (log_of (relabel fa (snap_map fe fr) m1))
                  (log_of (relabel fa (snap_map fe fr) m2)) h =
      MAP fa (par_actions (log_of m1) (log_of m2) (MAP (snap_map fe fr) h))
Proof
  Induct_on ‘h’ using SNOC_INDUCT
  >- simp[par_actions_NIL, log_of_relabel]
  >> simp[SNOC_APPEND, par_actions_SNOC] >> rpt gen_tac
  >> qmatch_goalsub_abbrev_tac ‘par_views A1 A2 (h ++ [x])’
  >> Cases_on ‘par_views A1 A2 (h ++ [x])’ >> gvs[]
  >> simp[Abbr ‘A1’, Abbr ‘A2’, new_actions_relabel]
  >> drule par_views_relabel_SNOC >> simp[]
QED

Theorem relabel_views[local]:
  MAP (snap_map fe fr)
    (FST (par_views (log_of (relabel fa (snap_map fe fr) m1))
                    (log_of (relabel fa (snap_map fe fr) m2)) h)) =
  FST (par_views (log_of m1) (log_of m2) (MAP (snap_map fe fr) h)) ∧
  MAP (snap_map fe fr)
    (SND (par_views (log_of (relabel fa (snap_map fe fr) m1))
                    (log_of (relabel fa (snap_map fe fr) m2)) h)) =
  SND (par_views (log_of m1) (log_of m2) (MAP (snap_map fe fr) h))
Proof
  metis_tac[par_views_relabel, pairTheory.FST, pairTheory.SND]
QED

(* MAIN: relabelling distributes over both *)
Theorem relabel_both:
  relabel fa (snap_map fe fr) (both m1 m2) =
  both (relabel fa (snap_map fe fr) m1) (relabel fa (snap_map fe fr) m2)
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac ‘h’ >>
  simp[relabel_def, both_def, par_log_def, left_view_def, right_view_def] >>
  simp[GSYM relabel_def, par_actions_relabel, relabel_views]
QED
