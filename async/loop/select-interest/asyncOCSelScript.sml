(*
  Option C §2.3: the loop's select set.  The CakeML loop sorts the fds
  that the computation declares (in any order, maybe repeated: EVSET) into
  a strictly increasing list, so the select set is a function of the
  model's declared interest:

      qsel c h = the declared fds of c after h, strictly increasing.

  MAIN: sort_num_set_eq (sorting forgets order and repetition), qsel_sort
  (what the code computes is qsel), sel_covers_qsel (it covers what c waits
  for, given finite2 c).
*)
Theory asyncOCSel
Ancestors
  pair list rich_list arithmetic option pred_set words sorting misc
  asyncCore asyncLevel1 asyncLevel2 asyncM4BlkSelWorld asyncOCFinite
Libs
  BasicProvers wordsLib

Definition ins_num_def:
  ins_num (x:num) [] = [x] ∧
  ins_num x (y :: r) =
    if x < y then x :: y :: r else if x = y then y :: r else y :: ins_num x r
End

Definition sort_num_def:
  sort_num [] = [] ∧
  sort_num (x :: r) = ins_num x (sort_num r)
End

Theorem set_ins_num[local]:
  ∀l. set (ins_num x l) = x INSERT set l
Proof
  Induct >> rw[ins_num_def] >> simp[EXTENSION] >> metis_tac[]
QED

Theorem set_sort_num:
  ∀l. set (sort_num l) = set l
Proof
  Induct >> simp[sort_num_def, set_ins_num]
QED

Theorem SORTED_ins_num[local]:
  ∀l. SORTED $< l ⇒ SORTED $< (ins_num x l)
Proof
  Induct >> rw[ins_num_def] >> gvs[SORTED_EQ, set_ins_num] >>
  rw[] >> gvs[]
QED

Theorem SORTED_sort_num:
  ∀l. SORTED $< (sort_num l)
Proof
  Induct >> simp[sort_num_def, SORTED_ins_num]
QED

Theorem SORTED_lt_ALL_DISTINCT[local]:
  ∀l. SORTED ($< : num -> num -> bool) l ⇒ ALL_DISTINCT l
Proof
  Induct >> rw[] >> gvs[SORTED_EQ] >> strip_tac >> res_tac >> fs[]
QED

(* MAIN: sorting forgets order and repetition *)
Theorem sort_num_set_eq:
  set l1 = set l2 ⇒ sort_num l1 = sort_num l2
Proof
  strip_tac >> qspec_then ‘$< : num -> num -> bool’ mp_tac SORTED_PERM_EQ >>
  impl_tac
  >- simp[relationTheory.transitive_def, relationTheory.antisymmetric_def] >>
  disch_then irule >> simp[SORTED_sort_num] >>
  irule PERM_ALL_DISTINCT >>
  simp[SORTED_lt_ALL_DISTINCT, SORTED_sort_num, set_sort_num]
QED

Theorem MEM_sort_num:
  MEM x (sort_num l) ⇔ MEM x l
Proof
  metis_tac[set_sort_num]
QED

(* The select set: the declared fds after h, strictly increasing *)
Definition qsel_def:
  qsel c h : word64 list =
    MAP n2w (sort_num (MAP w2n (SET_TO_LIST (waiting_on c h : word64 set))))
End

Theorem MAP_w2n_n2w_sort[local]:
  MAP w2n (MAP (n2w : num -> word64) (sort_num (MAP w2n (l : word64 list)))) =
  sort_num (MAP w2n l)
Proof
  simp[MAP_MAP_o, miscTheory.MAP_EQ_ID, MEM_sort_num, MEM_MAP] >> rw[] >>
  qspec_then ‘y’ mp_tac w2n_lt >> simp[]
QED

(* MAIN: what the code computes from any list of the declared fds *)
Theorem qsel_sort:
  set l = waiting_on c h ∧ FINITE (waiting_on c h) ⇒
  sort_num (MAP w2n l) = MAP w2n (qsel c h)
Proof
  strip_tac >> REWRITE_TAC[qsel_def, MAP_w2n_n2w_sort] >>
  irule sort_num_set_eq >> simp[LIST_TO_SET_MAP, SET_TO_LIST_INV]
QED

Theorem set_qsel:
  FINITE (waiting_on c h) ⇒ set (qsel c h) = waiting_on c h
Proof
  rw[qsel_def, LIST_TO_SET_MAP, set_sort_num, IMAGE_IMAGE, SET_TO_LIST_INV] >>
  rw[EXTENSION] >> eq_tac >> rw[] >> simp[] >> qexists_tac ‘x’ >> simp[]
QED

(* MAIN: the select set covers what c waits for *)
Theorem sel_covers_qsel:
  finite2 c ⇒ sel_covers c (qsel c)
Proof
  rw[sel_covers_def] >>
  ‘FINITE (waiting_on c h)’ by gvs[finite2_def, waiting_on_def] >>
  simp[set_qsel] >> simp[waiting_on_def]
QED
