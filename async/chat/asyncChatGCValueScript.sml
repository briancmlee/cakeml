(*
  The GC hub's store as a CakeML value.

  The program carries the hub's store st in its closures as a value v with
  GSTORE st v (the translator's refinement of the gstore record; the CF
  proof of with_tap keeps STORE st v for the store st of the model's run at
  every round).  gc_value_size: such a v is a record whose log field is a
  CakeML list of exactly LENGTH st.glog cells; with gc_space, that is
  gend st − cmin st cells: the bytes after the least client cursor.
*)
Theory asyncChatGCValue
Ancestors
  asyncChatGC asyncChatGCProg ml_translator semanticPrimitives
Libs
  preamble ml_translatorLib

Overload GSTORE = “ASYNCCHATGC_GSTORE_TYPE”

(* A CakeML list value with the given element values *)
Definition list_value_def:
  list_value [] = Conv (SOME (TypeStamp «[]» 1)) [] ∧
  list_value (x :: xs) = Conv (SOME (TypeStamp «::» 1)) [x; list_value xs]
End

Theorem LIST_TYPE_list_value:
  ∀l v. LIST_TYPE a l v ⇒ ∃vs. v = list_value vs ∧ LENGTH vs = LENGTH l
Proof
  Induct >> rw[LIST_TYPE_def, list_value_def] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  metis_tac[list_value_def, LENGTH]
QED

(* MAIN: the value of a GC store holds its log as a list of exactly
   LENGTH st.glog cells *)
Theorem gc_value_size:
  GSTORE st v ⇒
  ∃stamp vb vs vr. v = Conv (SOME stamp) (vb :: list_value vs :: vr) ∧
                   LENGTH vs = LENGTH st.glog
Proof
  Cases_on ‘st’ >> rw[fetch "asyncChatGCProg" "ASYNCCHATGC_GSTORE_TYPE_def"] >>
  imp_res_tac LIST_TYPE_list_value >> simp[] >>
  first_assum (irule_at Any) >> simp[]
QED

(* MAIN: with the GC invariant, that is the bytes after the least cursor *)
Theorem gc_value_space:
  GSTORE st v ∧ gc_inv st ⇒
  ∃stamp vb vs vr. v = Conv (SOME stamp) (vb :: list_value vs :: vr) ∧
                   LENGTH vs = gend st − cmin st
Proof
  rpt strip_tac >> drule gc_value_size >> strip_tac >>
  drule gc_space >> strip_tac >> metis_tac[]
QED
