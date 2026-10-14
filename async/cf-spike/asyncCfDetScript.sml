(*
  A small, general CF lemma used by the spike: a single application whose
  postcondition is pure (it only constrains the returned value, and keeps
  no heap) can collect infinitely many such postconditions into one.

  Reason: CakeML's semantics is deterministic, so in a given state the
  application returns one value; each postcondition is a fact about that
  same value.  This is what lets us prove a coinductive representation
  predicate from its finite approximations (see asyncCfProgScript.sml).
*)
Theory asyncCfDet
Ancestors
  cfApp cfHeapsBase evaluate evaluateProps
Libs
  preamble

(* Two terminating runs of the same expression from the same state, with
   different clocks, return the same values. *)
Theorem evaluate_ck_Rval_det:
  evaluate_ck ck1 st env es = (s1, Rval r1) ∧
  evaluate_ck ck2 st env es = (s2, Rval r2) ⇒
  r1 = r2
Proof
  rw[evaluate_ck_def] >>
  Cases_on ‘ck1 ≤ ck2’
  >- (‘∃d. ck2 = ck1 + d’ by (qexists_tac ‘ck2 - ck1’ >> simp[]) >>
      gvs[] >>
      qpat_x_assum ‘evaluate (st with clock := ck1) _ _ = _’ assume_tac >>
      drule_then (qspec_then ‘d’ mp_tac) evaluate_add_to_clock >>
      simp[] >> strip_tac >> gvs[])
  >- (‘∃d. ck1 = ck2 + d’ by (qexists_tac ‘ck1 - ck2’ >> simp[]) >>
      gvs[] >>
      qpat_x_assum ‘evaluate (st with clock := ck2) _ _ = _’ assume_tac >>
      drule_then (qspec_then ‘d’ mp_tac) evaluate_add_to_clock >>
      simp[] >> strip_tac >> gvs[])
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
