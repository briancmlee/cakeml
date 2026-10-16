(*
  Relabelling at Level 2 (option C, design/33 §2.2): a Level 2 computation
  in the model's vocabulary, run in the socket vocabulary.

  relabel2 fa fe fr ie c relabels the run as relabel's relabel does
  (actions by fa, snapshots by snap_map fe fr), and the declared interest
  by ie, a map from model event sets to socket event sets.  It distributes
  over the Level 2 combinators (as relabel does over the Level 1 ones,
  relabelDist), so the socket-vocabulary handler unfolds to the
  library code that the CakeML handler mirrors.

  For sockets, ie is sie: the fds c with Readable (w2n c) declared; so
  wait_on (Readable fd) becomes wait_on (n2w fd) (srelabel2_wait_readable).
*)
Theory relabel2
Ancestors
  pair list rich_list arithmetic option pred_set words
  asyncCore asyncLevel1 asyncChoose asyncLevel2 echoServer loopPollWorld
  relabel relabelDist echoSockModel
Libs
  BasicProvers wordsLib

Definition relabel2_def:
  relabel2 fa fe fr ie c =
    <| run := relabel fa (snap_map fe fr) c.run;
       interest := λh. ie (c.interest (MAP (snap_map fe fr) h)) |>
End

(* ie is a relabelling of event sets: it keeps ∅ and unions *)
Definition ie_ok_def:
  ie_ok ie ⇔ ie ∅ = ∅ ∧ ∀A B. ie (A ∪ B) = ie A ∪ ie B
End

Theorem comp2_eq[local]:
  c1 = c2 ⇔ c1.run = c2.run ∧ c1.interest = c2.interest
Proof
  simp[DB.fetch "asyncLevel2" "comp2_component_equality"]
QED

Theorem erase_relabel2:
  erase (relabel2 fa fe fr ie c) = relabel fa (snap_map fe fr) (erase c)
Proof
  simp[erase_def, relabel2_def]
QED

Theorem relabel2_return2:
  ie_ok ie ⇒ relabel2 fa fe fr ie (return2 x) = return2 x
Proof
  rw[comp2_eq, relabel2_def, return2_def, relabel_return, ie_ok_def, FUN_EQ_THM]
QED

Theorem relabel2_emit2:
  ie_ok ie ⇒ relabel2 fa fe fr ie (emit2 a) = map2 fr (emit2 (fa a))
Proof
  rw[comp2_eq, relabel2_def, emit2_def, map2_def, relabel_emit, ie_ok_def,
     FUN_EQ_THM]
QED

Theorem relabel2_map2:
  relabel2 fa fe fr ie (map2 f c) = map2 f (relabel2 fa fe fr ie c)
Proof
  rw[comp2_eq, relabel2_def, map2_def, relabel_map]
QED

Theorem relabel2_wait_on:
  relabel2 fa fe fr ie (wait_on e p) =
    <| run := wait (λs. if e ∈ fe s.ready then p (snap_map fe fr s) else NONE);
       interest := K (ie {e}) |>
Proof
  rw[comp2_eq, relabel2_def, wait_on_def, relabel_wait, FUN_EQ_THM,
     combinTheory.o_DEF, snap_map_def]
QED

Theorem relabel_result[local]:
  (relabel fa fs m h).result = (m (MAP fs h)).result
Proof
  simp[relabel_def]
QED

(* MAIN: relabelling distributes over bind2 *)
Theorem relabel2_bind2:
  relabel2 fa fe fr ie (bind2 c f) =
  bind2 (relabel2 fa fe fr ie c) (λx. relabel2 fa fe fr ie (f x))
Proof
  rw[comp2_eq]
  >- simp[relabel2_def, bind2_def, relabel_bind]
  >> simp[relabel2_def, bind2_def, FUN_EQ_THM] >> qx_gen_tac ‘h’
  >> simp[bind_interest_def, relabel_result]
  >> ‘first_prefix (λp. (c.run (MAP (snap_map fe fr) p)).result ≠ NONE) h =
      first_prefix (λp. (c.run p).result ≠ NONE) (MAP (snap_map fe fr) h)’
       by (qspecl_then [‘snap_map fe fr’, ‘h’, ‘λp. (c.run p).result ≠ NONE’]
             mp_tac first_prefix_MAP >> simp[])
  >> simp[]
  >> CASE_TAC >> simp[]
  >> simp[new_actions_relabel, GSYM skip_results_MAP, MAP_TAKE, MAP_DROP]
QED

Theorem relabel_views2[local]:
  MAP (snap_map fe fr) (left_view (relabel fa (snap_map fe fr) m1)
                                  (relabel fa (snap_map fe fr) m2) h) =
  left_view m1 m2 (MAP (snap_map fe fr) h) ∧
  MAP (snap_map fe fr) (right_view (relabel fa (snap_map fe fr) m1)
                                   (relabel fa (snap_map fe fr) m2) h) =
  right_view m1 m2 (MAP (snap_map fe fr) h)
Proof
  simp[left_view_def, right_view_def] >>
  metis_tac[par_views_relabel, pairTheory.FST, pairTheory.SND]
QED

Theorem waiting_on_relabel2[local]:
  ie_ok ie ⇒
  waiting_on (relabel2 fa fe fr ie c) h =
  ie (waiting_on c (MAP (snap_map fe fr) h))
Proof
  rw[waiting_on_def, relabel2_def, relabel_result, ie_ok_def]
QED

(* MAIN: relabelling distributes over both2 *)
Theorem relabel2_both2:
  ie_ok ie ⇒
  relabel2 fa fe fr ie (both2 c1 c2) =
  both2 (relabel2 fa fe fr ie c1) (relabel2 fa fe fr ie c2)
Proof
  rw[comp2_eq]
  >- simp[relabel2_def, both2_def, relabel_both]
  >> simp[both2_def, FUN_EQ_THM] >> qx_gen_tac ‘h’
  >> simp[waiting_on_relabel2]
  >> simp[relabel2_def]
  >> simp[GSYM relabel2_def, relabel_views2]
  >> fs[ie_ok_def]
QED

(* ------------------------------------------------------------------------
   Sockets
   ------------------------------------------------------------------------ *)

Definition sie_def:
  sie (I : echoServer$event set) = { c : word64 | Readable (w2n c) ∈ I }
End

Theorem ie_ok_sie:
  ie_ok sie
Proof
  simp[ie_ok_def, sie_def, EXTENSION] >> metis_tac[]
QED

Overload srelabel2 = “relabel2 sfa sfe sfr sie”

Theorem erase_srelabel2:
  erase (srelabel2 c) = srelabel (erase c)
Proof
  simp[erase_relabel2]
QED

(* MAIN: waiting for a readable connection, in the socket vocabulary *)
Theorem srelabel2_wait_readable:
  fd < dimword(:64) ⇒
  srelabel2 (wait_on (Readable fd) (λs. SOME ())) = wait_on (n2w fd) (λs. SOME ())
Proof
  rw[comp2_eq, relabel2_wait_on, wait_on_def, FUN_EQ_THM, sie_def, sfe_def,
     EXTENSION]
  >- (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> qx_gen_tac ‘s’ >>
      ‘(∃x:word64. fd = w2n x ∧ x ∈ s.ready) ⇔ (n2w fd : word64) ∈ s.ready’
        by (eq_tac >> rw[] >> gvs[n2w_w2n] >> qexists_tac ‘n2w fd’ >>
            simp[w2n_n2w]) >>
      simp[])
  >> eq_tac >> rw[] >> gvs[] >> metis_tac[n2w_w2n, w2n_n2w, LESS_MOD]
QED
