(*
  Lemmas the async translator (asyncTranslateLib) applies, in the abstract
  vocabulary of asyncM4ServerProg (events, actions, responses).

  bind_guarded_any: the combined guarded-bind rule.  The first part cannot
  finish before a poll, so the continuation is needed only one level less
  deep, and not at all at depth 0.  The translator uses it at every bind
  whose first part is a guarded primitive (readable, emit); recursive calls
  under such a bind are then proved from the induction hypothesis at a
  smaller depth.
*)
Theory asyncTranslate
Ancestors
  asyncCore asyncLevel1 asyncServer asyncCfActModel asyncCfActProg
  asyncCfActSpec asyncCfActBoth asyncM4Approx asyncM4ServerProg ml_translator
Libs
  preamble basis cfTacticsLib

Theorem bind_guarded_any:
  wf m ∧ (m []).result = NONE ∧ COMP p ACT A (SNAPSHOT READY R) m mv ∧
  (0 < n ⇒
   ∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (n - 1) (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) n
                (bind m g) v)
Proof
  Cases_on ‘n’ >> rpt strip_tac
  >- (irule bind_guarded_spec_0 >> simp[] >> metis_tac[COMP_IMP_COMPd])
  >> irule bind_guarded_spec_d >> gs[] >> qexists_tac ‘A’ >>
  simp[COMP_IMP_COMPd]
QED

(* The guarded primitives' facts *)
Theorem readable_NIL:
  (readable fd []).result = NONE
Proof
  simp[readable_def, wait_needs_snapshot]
QED

Theorem wf_readable:
  wf (readable fd)
Proof
  simp[readable_def, wf_wait]
QED
