(*
  General CF lemmas used by the spike: an application whose postcondition
  is pure (it only constrains the returned value, and keeps no heap) can
  collect infinitely many such postconditions into one.

  Reason: CakeML's semantics is deterministic, so in a given state the
  application returns one value; each postcondition is a fact about that
  same value.  This is what lets us prove a coinductive representation
  predicate from its finite approximations (see asyncCfProgScript.sml).
*)
Theory libDet
Ancestors
  set_sep cfApp cfHeapsBase cfStore evaluate evaluateProps
Libs
  preamble

(* Two terminating runs of the same expression from the same state, with
   different clocks, return the same values and end in the same heap. *)
Theorem evaluate_ck_Rval_det:
  evaluate_ck ck1 st env es = (s1, Rval r1) ∧
  evaluate_ck ck2 st env es = (s2, Rval r2) ⇒
  r1 = r2 ∧ st2heap p s1 = st2heap p s2
Proof
  simp[evaluate_ck_def] >> strip_tac >>
  Cases_on ‘ck1 ≤ ck2’
  >- (‘∃d. ck2 = ck1 + d’ by (qexists_tac ‘ck2 - ck1’ >> simp[]) >>
      gvs[] >>
      qpat_x_assum ‘evaluate (st with clock := ck1) _ _ = _’ assume_tac >>
      drule_then (qspec_then ‘d’ mp_tac) evaluate_add_to_clock >>
      simp[] >> strip_tac >> gvs[st2heap_clock])
  >- (‘∃d. ck1 = ck2 + d’ by (qexists_tac ‘ck1 - ck2’ >> simp[]) >>
      gvs[] >>
      qpat_x_assum ‘evaluate (st with clock := ck2) _ _ = _’ assume_tac >>
      drule_then (qspec_then ‘d’ mp_tac) evaluate_add_to_clock >>
      simp[] >> strip_tac >> gvs[st2heap_clock])
QED

(* The same, at the level of CF's evaluate_to_heap. *)
Theorem evaluate_to_heap_Val_det:
  evaluate_to_heap st env exp p heap1 (Val v1) ∧
  evaluate_to_heap st env exp p heap2 (Val v2) ⇒
  v1 = v2 ∧ heap1 = heap2
Proof
  rw[evaluate_to_heap_def] >>
  metis_tac[evaluate_ck_Rval_det, listTheory.CONS_11]
QED

(* Key lemma: applications with pure postconditions can be conjoined, even
   infinitely often (one postcondition per index i). *)
Theorem app_basic_forall:
  (∀i. app_basic p f x H (POSTv v. &P i v)) ⇒
  app_basic p f x H (POSTv v. &(∀i. P i v))
Proof
  rw[app_basic_def, POSTv_cond, PULL_EXISTS] >>
  first_assum (qspec_then ‘ARB’ (drule_all_then strip_assume_tac)) >>
  qexistsl [‘env’, ‘exp’, ‘h_g’, ‘heap’, ‘v’] >> rw[] >>
  first_x_assum (qspecl_then [‘i’, ‘h_i’, ‘h_k’, ‘st’] mp_tac) >>
  rpt (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  fs[evaluate_to_heap_def] >> rveq >>
  ‘[v] = [v']’ by metis_tac[evaluate_ck_Rval_det] >> fs[]
QED

(* Unfolding the postcondition of a partial application. *)
Theorem POSTv_SEP_EXISTS_cond:
  (POSTv g. SEP_EXISTS H'. H' * &c g H') r h ⇔
  ∃g H'. r = Val g ∧ H' h ∧ c g H'
Proof
  Cases_on ‘r’ >> simp[POSTv_def, SEP_EXISTS_THM, cond_STAR] >>
  simp[set_sepTheory.cond_def] >> metis_tac[]
QED

(* The kept and garbage parts of a split can be merged. *)
Theorem SPLIT3_merge:
  SPLIT3 heap (a,k,b) ⇒
  SPLIT3 heap (a ∪ b,k,∅) ∧ a ∪ b = heap DIFF k
Proof
  rw[SPLIT3_def] >> fs[EXTENSION, IN_DISJOINT] >> metis_tac[]
QED

(* An application from a heap satisfying H can also start from exactly
   that heap plus some disjoint garbage. *)
Theorem app_exact_pre:
  app p g xs H Q ∧ H a ∧ DISJOINT a b ⇒
  app p g xs (λh. h = a ∪ b) Q
Proof
  rw[] >> irule app_wgframe >> qexistsl [‘H’, ‘GC’, ‘Q’] >> rw[]
  >- (rw[SEP_IMP_def, STAR_def, GC_def, SEP_EXISTS_THM, SPLIT_def] >>
      qexistsl [‘a’, ‘b’] >> simp[] >> qexists_tac ‘λx. T’ >> simp[])
  >- (rw[SEP_IMPPOST_def, SEP_IMP_REFL])
QED

(* Key lemma, curried version: the same for an application to any non-empty
   argument list.  The intermediate closures returned by partial applications
   are the same for every postcondition, again by determinism. *)
Theorem app_forall:
  ∀p P xs f H.
    xs ≠ [] ∧ (∀i. app p f xs H (POSTv v. &P i v)) ⇒
    app (p:'ffi ffi_proj) f xs H (POSTv v. &(∀i. P i v))
Proof
  ntac 2 gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  Cases_on ‘xs’ >- gvs[app_def, app_basic_forall] >>
  gvs[app_def] >>
  rw[app_basic_def, POSTv_SEP_EXISTS_cond, PULL_EXISTS] >>
  ‘∀i. ∃env exp g h_f h_g heap H'.
         SPLIT3 heap (h_f,h_k,h_g) ∧ do_opapp [f; h] = SOME (env,exp) ∧
         H' h_f ∧ app p g (h'::t) H' (POSTv v. &P i v) ∧
         evaluate_to_heap st env exp p heap (Val g)’
    by (gen_tac >> first_x_assum (qspec_then ‘i’ mp_tac) >>
        rw[app_basic_def, POSTv_SEP_EXISTS_cond, PULL_EXISTS] >>
        first_x_assum drule_all >> metis_tac[]) >>
  first_assum (qspec_then ‘ARB’ strip_assume_tac) >>
  (* keep this run's closure g; its kept heap and garbage become the
     exact precondition of the remaining applications *)
  drule SPLIT3_merge >> strip_tac >>
  qexistsl [‘env’, ‘exp’, ‘h_f ∪ h_g’, ‘∅’, ‘heap’, ‘g’,
            ‘λx. x = h_f ∪ h_g’] >> simp[] >>
  qpat_x_assum ‘∀f' H'. _ ⇒ _’ irule >> qx_gen_tac ‘i’ >>
  qpat_x_assum ‘∀i. ∃env. _’
    (qspec_then ‘i’ (qx_choosel_then
       [‘env1’, ‘exp1’, ‘g1’, ‘hf1’, ‘hg1’, ‘heap1’, ‘H1’] strip_assume_tac)) >>
  gvs[] >>
  ‘g1 = g ∧ heap1 = heap’
    by (qpat_x_assum ‘evaluate_to_heap _ _ _ _ heap1 _’ (fn th1 =>
          qpat_x_assum ‘evaluate_to_heap _ _ _ _ heap _’ (fn th2 =>
            ACCEPT_TAC (MATCH_MP (GEN_ALL evaluate_to_heap_Val_det)
                                 (CONJ th1 th2))))) >>
  gvs[] >>
  ‘heap DIFF h_k = hf1 ∪ hg1’ by metis_tac[SPLIT3_merge] >>
  pop_assum SUBST1_TAC >>
  irule app_exact_pre >> fs[SPLIT3_def] >> metis_tac[]
QED
