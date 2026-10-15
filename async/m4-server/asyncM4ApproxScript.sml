(*
  Recursion in the actions/responses CF layer: depth-indexed specs.

  A recursive CakeML computation (the echo handler, the server) calls
  itself inside a continuation of bind.  To prove that it implements the
  model's fix-defined computation, we prove for every depth n that it
  implements the model "up to depth n" (COMPd n), and take the limit
  (app_COMP_of_approxd).  The step from depth n to depth n+1 needs specs of
  the library's combinators whose hypotheses are themselves only up to
  depth n: this theory proves them for poll, skip, bind and both.

  STEPAd n is the n-th approximation of asyncCfActProg's STEPA, which
  additionally fixes the shape (Done with a related result, or Pending) at
  the bottom level.  That shape is what the CakeML code inspects (bind's
  case split, skip, both's case split), so with it the combinators
  preserve every depth, including 0.  (cf-actions' STEPAn 0 is T, which is
  too weak for that.)
*)
Theory asyncM4Approx
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActBothModel
  asyncCfActProg asyncCfActSpec asyncCfActBoth ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfActBoth"

(* Build a value made of nested constructors, e.g. ([], Done x) *)
val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

Theorem LIST_TYPE_NIL[local,simp]:
  LIST_TYPE A [] v ⇔ v = Conv (SOME (TypeStamp «[]» 1)) []
Proof
  simp[LIST_TYPE_def]
QED

(* ------------------------------------------------------------------------
   The depth-indexed predicate
   ------------------------------------------------------------------------ *)

(* STEPAd p ACT RES WORLD n m s: the residual s implements the model
   computation m for its next n polls, and the residual after those n polls
   has the right shape: Done with a related result if the model has
   finished, Pending if not. *)
Definition STEPAd_def:
  (STEPAd p ACT RES WORLD 0 m v ⇔
     (∃A x xv. m = finished A x ∧ RES x xv ∧ v = DoneV xv) ∨
     (∃kv. (m []).result = NONE ∧ v = PendingV kv)) ∧
  (STEPAd p ACT RES WORLD (SUC n) m v ⇔
     (∃A x xv. m = finished A x ∧ RES x xv ∧ v = DoneV xv) ∨
     (∃kv. (m []).result = NONE ∧ v = PendingV kv ∧
           ∀w wv. WORLD w wv ⇒
             returns p kv [wv]
               (POLL_RESULT ACT (STEPAd p ACT RES WORLD n) (suspended m [w]))))
End

(* COMPd p ACT RES WORLD n m v: the CakeML pair v implements m up to depth n *)
Definition COMPd_def:
  COMPd p ACT RES WORLD n m v ⇔ POLL_RESULT ACT (STEPAd p ACT RES WORLD n) m v
End

Theorem STEPAd_Done:
  STEPAd p ACT RES WORLD n m (DoneV xv) ⇔ ∃A x. m = finished A x ∧ RES x xv
Proof
  Cases_on ‘n’ >> simp[STEPAd_def]
QED

Theorem STEPAd_finished:
  RES x xv ⇒ STEPAd p ACT RES WORLD n (finished A x) (DoneV xv)
Proof
  simp[STEPAd_Done] >> metis_tac[]
QED

(* Depth n+1 implies depth n *)
Theorem STEPAd_SUC_IMP:
  ∀n m v. STEPAd p ACT RES WORLD (SUC n) m v ⇒ STEPAd p ACT RES WORLD n m v
Proof
  Induct >> rpt gen_tac >> simp[Once STEPAd_def] >> rw[] >>
  gs[STEPAd_finished] >> simp[STEPAd_def] >>
  rpt strip_tac >> irule returns_mono >>
  first_x_assum (drule_then (irule_at Any)) >> rpt strip_tac >>
  irule POLL_RESULT_mono >> first_x_assum (irule_at Any) >> simp[]
QED

Theorem COMPd_SUC_IMP:
  COMPd p ACT RES WORLD (SUC n) m v ⇒ COMPd p ACT RES WORLD n m v
Proof
  rw[COMPd_def] >> irule POLL_RESULT_mono >> first_x_assum (irule_at Any) >>
  simp[STEPAd_SUC_IMP]
QED

(* The real predicate implies every depth *)
Theorem STEPA_IMP_STEPAd:
  ∀n m v. STEPA p ACT RES WORLD m v ⇒ STEPAd p ACT RES WORLD n m v
Proof
  Induct >> rpt gen_tac >> simp[Once STEPA_cases] >> rw[] >>
  gs[STEPAd_finished] >> simp[STEPAd_def] >>
  rpt strip_tac >> irule returns_mono >>
  first_x_assum (drule_then (irule_at Any)) >> rpt strip_tac >>
  irule POLL_RESULT_mono >> first_x_assum (irule_at Any) >> simp[]
QED

Theorem COMP_IMP_COMPd:
  COMP p ACT RES WORLD m v ⇒ COMPd p ACT RES WORLD n m v
Proof
  rw[COMP_def, COMPd_def] >> irule POLL_RESULT_mono >>
  first_x_assum (irule_at Any) >> simp[STEPA_IMP_STEPAd]
QED

Theorem STEPAn_finished[local]:
  RES x xv ⇒ STEPAn p ACT RES WORLD n (finished A x) (DoneV xv)
Proof
  Cases_on ‘n’ >> simp[STEPAn_def] >> metis_tac[]
QED

(* Each depth implies cf-actions' approximation at the same depth *)
Theorem STEPAd_IMP_STEPAn:
  ∀n m v. STEPAd p ACT RES WORLD n m v ⇒ STEPAn p ACT RES WORLD n m v
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[Once STEPAd_def] >> rw[] >>
  gs[STEPAn_finished] >> simp[STEPAn_def] >>
  rpt strip_tac >> irule returns_mono >>
  first_x_assum (drule_then (irule_at Any)) >> rpt strip_tac >>
  irule POLL_RESULT_mono >> first_x_assum (irule_at Any) >> simp[]
QED

(* MAIN: the limit argument for recursive computations: if a call returns,
   for every depth n, a value implementing m up to depth n, then it returns
   a value implementing m. *)
Theorem app_COMP_of_approxd:
  args ≠ [] ∧
  (∀n. app p f args H (POSTv v. &COMPd p ACT RES WORLD n m v)) ⇒
  app (p:'ffi ffi_proj) f args H (POSTv v. &COMP p ACT RES WORLD m v)
Proof
  strip_tac >> irule app_COMP_of_approx >> simp[] >> gen_tac >>
  irule app_weaken >>
  qexists_tac ‘POSTv v. &COMPd p ACT RES WORLD n m v’ >> simp[] >>
  rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def,
     POSTv_cond, COMPd_def] >>
  irule POLL_RESULT_mono >> first_x_assum (irule_at Any) >>
  simp[STEPAd_IMP_STEPAn]
QED

(* Actions emitted before the first round don't change the residual *)
Theorem STEPAd_prepend:
  STEPAd p ACT RES WORLD n g sv ⇒ STEPAd p ACT RES WORLD n (prepend A g) sv
Proof
  Cases_on ‘n’ >> simp[Once STEPAd_def] >> rw[] >>
  gs[prepend_finished, STEPAd_finished] >>
  simp[STEPAd_def, suspended_prepend]
QED

(* ------------------------------------------------------------------------
   poll and skip, up to depth n
   ------------------------------------------------------------------------ *)

(* Polling consumes one level of depth *)
Theorem poll_spec_d:
  COMPd p ACT RES WORLD (SUC n) m cv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll_v [cv; wv] emp
    (POSTv v. &COMPd p ACT RES WORLD n (suspended m [w]) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def poll_v_def >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ _ _’ mp_tac >> simp[STEPAd_def] >> rw[]
  >- (xmatch >> xmatch >> xcons >>
      simp[COMPd_def, POLL_RESULT_def, suspended_finished_one, STEPAd_Done] >>
      simp[finished_def] >> metis_tac[])
  >- (xmatch >> xmatch >> first_x_assum drule >>
      rw[returns_def, GSYM COMPd_def] >> xapp >> simp[COMPd_def])
QED

Theorem skip_spec_d:
  STEPAd p ACT RES (SNAPSHOT READY (R : 'r -> v -> bool)) n g sv ∧ NUM k kv ⇒
  app (p:'ffi ffi_proj) skip_v [kv; sv] emp
    (POSTv v. &STEPAd p ACT RES (SNAPSHOT READY R) n (skipping k g) v)
Proof
  rpt strip_tac >> xcf_with_def skip_v_def >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ _ sv’ mp_tac >>
  Cases_on ‘n’ >> simp[STEPAd_def] >> strip_tac >> gvs[]
  >- (xmatch >> xvar >> xsimpl >> simp[skipping_finished] >> metis_tac[])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl)
  >- (xmatch >> xvar >> xsimpl >> simp[skipping_finished] >> metis_tac[])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      simp[suspended_skipping] >>
      rpt strip_tac >> simp[returns_def] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      gvs[SNAPSHOT_def] >> xmatch >>
      xlet ‘POSTv dv. &LIST_TYPE R (DROP k w.results) dv’
      >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.drop_v_thm) >>
          xsimpl >> simp[mllistTheory.drop_def] >>
          qexistsl [‘k’, ‘w.results’, ‘R’] >> simp[]) >>
      xlet ‘POSTv tv. &(tv = Conv NONE [rv; nv; dv])’
      >- (xcon >> xsimpl) >>
      gvs[] >>
      first_x_assum (qspecl_then [‘skip_snap k w’, ‘Conv NONE [rv; nv; dv]’]
                       mp_tac) >>
      impl_tac >- simp[SNAPSHOT_def, skip_snap_def] >>
      rw[returns_def] >> xapp)
QED

(* ------------------------------------------------------------------------
   bind, up to depth n
   ------------------------------------------------------------------------ *)

(* bind's finished case, at any depth: as bind_Done_spec_n *)
Theorem bind_Done_spec_d:
  STEPAd p ACT A (SNAPSHOT READY R) k m (DoneV xv) ∧
  LIST_TYPE (ACT : 'act -> v -> bool) (m []).actions av ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [Conv NONE [av; DoneV xv]; gv] emp
    (POSTv v. &COMPd p ACT B (SNAPSHOT READY R) n (bind m g) v)
Proof
  rw[STEPAd_Done] >> rename1 ‘finished As x’ >>
  gvs[finished_def] >>
  xcf_with_def bind_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv r. &COMPd p ACT B (SNAPSHOT READY R) n (g x) r’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  gvs[COMPd_def, POLL_RESULT_def] >> xmatch >>
  rename1 ‘LIST_TYPE ACT (g x []).actions av2’ >>
  xlet ‘POSTv nv. &NUM (LENGTH As) nv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> metis_tac[]) >>
  xlet ‘POSTv sv2. &STEPAd p ACT B (SNAPSHOT READY R) n
                      (skipping (LENGTH As) (g x)) sv2’
  >- (xapp_spec skip_spec_d >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv lv. &LIST_TYPE ACT (As ++ (g x []).actions) lv’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xcon >> xsimpl >>
  ‘finished As x = λh. <|actions := As; result := SOME x|>’
    by simp[FUN_EQ_THM, finished_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  simp[bind_finished, POLL_RESULT_def] >>
  irule STEPAd_prepend >> simp[]
QED

(* MAIN (helper): bind up to depth n.  If the first part and every
   continuation are implemented up to depth n, so is bind m g. *)
Theorem bind_spec_d:
  ∀n m mv.
    wf m ∧ COMPd p ACT A (SNAPSHOT READY R) n m mv ∧
    (∀x xv. A x xv ⇒
       returns p gv [xv]
         (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
    app (p:'ffi ffi_proj) bind_v [mv; gv] emp
      (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) n
                  (bind m g) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ m mv’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ m sv’ mp_tac >>
  simp[Once STEPAd_def] >> rw[]
  >- (irule bind_Done_spec_d >> simp[STEPAd_Done] >> metis_tac[])
  >- (xcf_with_def bind_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[COMPd_def, POLL_RESULT_def, bind_NIL_running, STEPAd_def])
  >- (irule bind_Done_spec_d >> simp[STEPAd_Done] >> metis_tac[])
  >- (xcf_with_def bind_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[COMPd_def, POLL_RESULT_def, bind_NIL_running, STEPAd_def,
           suspended_bind] >>
      rpt strip_tac >> simp[returns_def] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv r. &COMPd p ACT A (SNAPSHOT READY R) n (suspended m [w]) r’
      >- (first_x_assum drule >> rw[returns_def, GSYM COMPd_def] >> xapp) >>
      first_x_assum (qspecl_then [‘suspended m [w]’, ‘r’] mp_tac) >>
      simp[wf_suspended, GSYM COMPd_def] >>
      impl_tac
      >- (rpt strip_tac >> irule returns_mono >>
          qpat_x_assum ‘∀x xv. A x xv ⇒ _’ (drule_then (irule_at Any)) >>
          rpt strip_tac >> irule COMPd_SUC_IMP >> simp[]) >>
      strip_tac >> xapp)
QED

(* A guarded bind (the first part has not finished in its first round) is
   implemented up to depth 0 whatever the continuation: bind does not call
   it before the first poll. *)
Theorem bind_guarded_spec_0:
  (m []).result = NONE ∧ COMPd p ACT A (SNAPSHOT READY R) 0 m mv ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B
                (SNAPSHOT READY (R : 'r -> v -> bool)) 0 (bind m g) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ m mv’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[STEPAd_def, finished_def] >>
  xcf_with_def bind_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
  simp[COMPd_def, POLL_RESULT_def, bind_NIL_running, STEPAd_def]
QED

(* MAIN (helper): a guarded bind gains one level of depth: if the first
   part has not finished in its first round, continuations up to depth n
   give bind m g up to depth n+1.  This is where recursion through a
   continuation makes progress. *)
Theorem bind_guarded_spec_d:
  wf m ∧ (m []).result = NONE ∧ COMPd p ACT A (SNAPSHOT READY R) (SUC n) m mv ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) (SUC n)
                (bind m g) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ m mv’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[STEPAd_def, finished_def] >>
  xcf_with_def bind_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
  simp[COMPd_def, POLL_RESULT_def, bind_NIL_running, STEPAd_def,
       suspended_bind] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv r. &COMPd p ACT A (SNAPSHOT READY R) n (suspended m [w]) r’
  >- (first_x_assum drule >> rw[returns_def, GSYM COMPd_def] >> xapp) >>
  ‘app p bind_v [r; gv] emp
     (POSTv v. &COMPd p ACT B (SNAPSHOT READY R) n (bind (suspended m [w]) g) v)’
    by (irule bind_spec_d >> simp[wf_suspended] >> metis_tac[]) >>
  gvs[COMPd_def] >> qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl
QED

(* ------------------------------------------------------------------------
   both, up to depth n
   ------------------------------------------------------------------------ *)

(* The common start of both_spec_d: take the two pairs apart, compute
   acts1 @ acts2, and split on whether each side is Done. *)
val both_prelude =
  rpt strip_tac >>
  qpat_assum ‘COMPd _ _ _ _ _ m1 _’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  qpat_assum ‘COMPd _ _ _ _ _ m2 _’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[] >>
  xcf_with_def both_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv av. &LIST_TYPE ACT ((m1 []).actions ++ (m2 []).actions) av’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ m1 _’ mp_tac >> simp[Once STEPAd_def] >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ m2 _’ mp_tac >> simp[Once STEPAd_def] >>
  rw[] >>
  (xlet_auto >- (xcon >> xsimpl));

(* Both sides Done: both returns (acts, Done (x, y)) *)
val both_done_tac =
  qmatch_goalsub_rename_tac ‘both (finished A1 x1) (finished A2 x2)’ >>
  xmatch >> xcons >>
  simp[COMPd_def, POLL_RESULT_def, both_finished_finished, STEPAd_Done] >>
  irule_at Any EQ_REFL >> gvs[finished_def, PAIR_TYPE_def];

(* The two sides M1 and M2 of both, read off the goal *)
fun both_sides w =
  let
    val t = find_term (fn t => (same_const (rator (rator t)) “both”
                                handle HOL_ERR _ => false)) w
  in (rand (rator t), rand t) end;

(* Otherwise: both returns (acts, Pending k).  At depth n+1, the closure k
   polls each side (one level of depth) and continues with both (the
   induction hypothesis). *)
fun both_pending_tac (n_is_suc : bool) (g as (_, w)) =
  let val (M1, M2) = both_sides w in
  (xmatch >> xfun ‘k’ >> xcons >>
  simp[COMPd_def, POLL_RESULT_def, both_NIL_poll] >>
  asm_simp_tac (srw_ss()) [STEPAd_def, both_NIL_poll, finished_def] >>
  (if not n_is_suc then ALL_TAC else
  simp[suspended_both] >>
  rpt strip_tac >> simp[returns_def, GSYM COMPd_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def] >> xmatch >>
  qabbrev_tac ‘kk = LENGTH (^M1 []).actions’ >>
  xlet ‘POSTv kv. &NUM kk kv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> simp[Abbr ‘kk’] >> metis_tac[]) >>
  xlet ‘POSTv tv. &LIST_TYPE R (TAKE kk w.results) tv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.take_v_thm) >>
      xsimpl >> simp[mllistTheory.take_def] >> metis_tac[]) >>
  xlet ‘POSTv w1. &(w1 = Conv NONE [rv; nv; tv])’ >- (xcon >> xsimpl) >>
  xlet ‘POSTv c1'. &COMPd p ACT A (SNAPSHOT READY R) n
                        (suspended ^M1 [take_snap kk w]) c1'’
  >- (‘SNAPSHOT READY R (take_snap kk w) w1’
        by simp[SNAPSHOT_def, take_snap_def] >>
      qpat_assum ‘COMPd _ _ A _ _ _ _’ (fn th1 =>
        qpat_assum ‘SNAPSHOT _ _ (take_snap _ _) _’ (fn th2 =>
          assume_tac (MATCH_MP poll_spec_d (CONJ th1 th2)))) >>
      qpat_x_assum ‘app _ poll_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv dv. &LIST_TYPE R (DROP kk w.results) dv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.drop_v_thm) >>
      xsimpl >> simp[mllistTheory.drop_def] >> metis_tac[]) >>
  xlet ‘POSTv w2. &(w2 = Conv NONE [rv; nv; dv])’ >- (xcon >> xsimpl) >>
  xlet ‘POSTv c2'. &COMPd p ACT B (SNAPSHOT READY R) n
                        (suspended ^M2 [skip_snap kk w]) c2'’
  >- (‘SNAPSHOT READY R (skip_snap kk w) w2’
        by simp[SNAPSHOT_def, skip_snap_def] >>
      qpat_assum ‘COMPd _ _ B _ _ _ _’ (fn th1 =>
        qpat_assum ‘SNAPSHOT _ _ (skip_snap _ _) _’ (fn th2 =>
          assume_tac (MATCH_MP poll_spec_d (CONJ th1 th2)))) >>
      qpat_x_assum ‘app _ poll_v _ _ _’ xapp_spec >> xsimpl) >>
  first_x_assum (qspecl_then [‘suspended ^M1 [take_snap kk w]’,
                              ‘suspended ^M2 [skip_snap kk w]’, ‘c1'’, ‘c2'’]
                   mp_tac) >>
  simp[wf_suspended] >> strip_tac >> xapp)) g
  end;

(* MAIN (helper): both up to depth n.  If both sides are implemented up to
   depth n, so is both m1 m2. *)
Theorem both_spec_d:
  ∀n m1 m2 c1 c2.
    wf m1 ∧ wf m2 ∧
    COMPd p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) n m1 c1 ∧
    COMPd p ACT B (SNAPSHOT READY R) n m2 c2 ⇒
    app (p:'ffi ffi_proj) both_v [c1; c2] emp
      (POSTv v. &COMPd p (ACT : 'act -> v -> bool) (PAIR_TYPE A B)
                  (SNAPSHOT READY R) n (both m1 m2) v)
Proof
  Induct
  >- (both_prelude >> FIRST [both_done_tac, both_pending_tac false])
  >- (both_prelude >> FIRST [both_done_tac, both_pending_tac true])
QED
