(*
  Recursion in the Level 2 CF library: depth-indexed specs, as
  libApprox does at Level 1.

  A recursive Level 2 computation (a handler, the server) calls itself
  inside a continuation of bind2.  We prove for every depth n that it
  implements the model up to depth n (COMPId n), and take the limit
  (app_COMPI_of_approxd).  STEPId n is the n-th approximation of STEPI
  that also fixes the shape at the bottom level: Done2 with a related
  result, or Pending2 with the declared events -- the interest is part of
  the shape, since the loop reads it at every depth.
*)
Theory lib2Approx
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 libModel libProg
  libBothModel loopBlock2Model loopBlock2Prog loopBlock2Spec
  lib2Model lib2Prog lib2Spec ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "lib2Prog"

val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

Theorem LIST_TYPE_NIL[local,simp]:
  LIST_TYPE A [] v ⇔ v = Conv (SOME (TypeStamp «[]» 1)) []
Proof
  simp[LIST_TYPE_def]
QED

(* ------------------------------------------------------------------------
   The depth-indexed predicate
   ------------------------------------------------------------------------ *)

Definition STEPId_def:
  (STEPId p ACT RES EV WORLD 0 c v ⇔
     (∃A x xv. c.run = finished A x ∧ RES x xv ∧ v = Done2V xv) ∨
     (∃iv kv. (c.run []).result = NONE ∧ EVSET EV (c.interest []) iv ∧
              v = Pending2V iv kv)) ∧
  (STEPId p ACT RES EV WORLD (SUC n) c v ⇔
     (∃A x xv. c.run = finished A x ∧ RES x xv ∧ v = Done2V xv) ∨
     (∃iv kv. (c.run []).result = NONE ∧ EVSET EV (c.interest []) iv ∧
              v = Pending2V iv kv ∧
              ∀w wv. WORLD w wv ⇒
                returns p kv [wv]
                  (POLL_RESULT2 ACT (STEPId p ACT RES EV WORLD n)
                     (suspended2 c [w]))))
End

Definition COMPId_def:
  COMPId p ACT RES EV WORLD n c v ⇔
    POLL_RESULT2 ACT (STEPId p ACT RES EV WORLD n) c v
End

Theorem STEPId_Done:
  STEPId p ACT RES EV WORLD n c (Done2V xv) ⇔
    ∃A x. c.run = finished A x ∧ RES x xv
Proof
  Cases_on ‘n’ >> simp[STEPId_def]
QED

Theorem STEPId_finished:
  c.run = finished A x ∧ RES x xv ⇒ STEPId p ACT RES EV WORLD n c (Done2V xv)
Proof
  simp[STEPId_Done] >> metis_tac[]
QED

Theorem STEPId_SUC_IMP:
  ∀n c v. STEPId p ACT RES EV WORLD (SUC n) c v ⇒ STEPId p ACT RES EV WORLD n c v
Proof
  Induct >> rpt gen_tac >> simp[Once STEPId_def] >> rw[] >>
  gs[STEPId_finished] >> simp[STEPId_def] >> TRY (metis_tac[] >> NO_TAC) >>
  rpt strip_tac >> irule returns_mono >>
  first_x_assum (drule_then (irule_at Any)) >> rpt strip_tac >>
  irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >> simp[]
QED

Theorem COMPId_SUC_IMP:
  COMPId p ACT RES EV WORLD (SUC n) c v ⇒ COMPId p ACT RES EV WORLD n c v
Proof
  rw[COMPId_def] >> irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >>
  simp[STEPId_SUC_IMP]
QED

(* The real predicate implies every depth *)
Theorem STEPI_IMP_STEPId:
  ∀n c v. STEPI p ACT RES EV WORLD c v ⇒ STEPId p ACT RES EV WORLD n c v
Proof
  Induct >> rpt gen_tac >> simp[Once STEPI_cases] >> rw[] >>
  gs[STEPId_finished] >> simp[STEPId_def] >> TRY (metis_tac[] >> NO_TAC) >>
  rpt strip_tac >> irule returns_mono >>
  first_x_assum (drule_then (irule_at Any)) >> rpt strip_tac >>
  irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >> simp[]
QED

Theorem COMPI_IMP_COMPId:
  COMPI p ACT RES EV WORLD c v ⇒ COMPId p ACT RES EV WORLD n c v
Proof
  rw[COMPI_def, COMPId_def] >> irule POLL_RESULT2_mono >>
  first_x_assum (irule_at Any) >> simp[STEPI_IMP_STEPId]
QED

Theorem STEPIn_finished[local]:
  c.run = finished A x ∧ RES x xv ⇒ STEPIn p ACT RES EV WORLD n c (Done2V xv)
Proof
  Cases_on ‘n’ >> simp[STEPIn_def] >> metis_tac[]
QED

Theorem STEPId_IMP_STEPIn:
  ∀n c v. STEPId p ACT RES EV WORLD n c v ⇒ STEPIn p ACT RES EV WORLD n c v
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[Once STEPId_def] >> rw[] >>
  gs[STEPIn_finished] >> simp[STEPIn_def] >> TRY (metis_tac[] >> NO_TAC) >>
  rpt strip_tac >> irule returns_mono >>
  first_x_assum (drule_then (irule_at Any)) >> rpt strip_tac >>
  irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >> simp[]
QED

(* MAIN: the limit argument for recursive Level 2 computations *)
Theorem app_COMPI_of_approxd:
  args ≠ [] ∧
  (∀n. app p f args H (POSTv v. &COMPId p ACT RES EV WORLD n c v)) ⇒
  app (p:'ffi ffi_proj) f args H (POSTv v. &COMPI p ACT RES EV WORLD c v)
Proof
  strip_tac >> irule app_COMPI_of_approx >> simp[] >> gen_tac >>
  irule app_weaken >>
  qexists_tac ‘POSTv v. &COMPId p ACT RES EV WORLD n c v’ >> simp[] >>
  rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def,
     POSTv_cond, COMPId_def] >>
  irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >>
  simp[STEPId_IMP_STEPIn]
QED

Theorem STEPId_prepend2:
  STEPId p ACT RES EV WORLD n g sv ⇒ STEPId p ACT RES EV WORLD n (prepend2 A g) sv
Proof
  Cases_on ‘n’ >> simp[Once STEPId_def] >> rw[] >>
  gs[prepend2_def, prepend_finished] >>
  TRY (irule STEPId_finished >> simp[prepend_finished] >> metis_tac[] >> NO_TAC) >>
  simp[STEPId_def, prepend2_def] >>
  gvs[GSYM prepend2_def, suspended2_prepend2]
QED

(* ------------------------------------------------------------------------
   poll2, interest and skip2, up to depth n
   ------------------------------------------------------------------------ *)

Theorem poll2_spec_d:
  COMPId p ACT RES EV WORLD (SUC n) c cv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll2_v [cv; wv] emp
    (POSTv v. &COMPId p ACT RES EV WORLD n (suspended2 c [w]) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPId _ _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def poll2_v_def >>
  qpat_x_assum ‘STEPId _ _ _ _ _ _ _ _’ mp_tac >> simp[STEPId_def] >> rw[]
  >- (xmatch >> xmatch >> xcons >>
      simp[COMPId_def, POLL_RESULT2_def, suspended2_run, suspended_finished_one,
           STEPId_Done] >>
      simp[finished_def] >> metis_tac[])
  >- (xmatch >> xmatch >> first_x_assum drule >>
      rw[returns_def, GSYM COMPId_def] >> xapp >> simp[COMPId_def])
QED

Theorem interest_spec_d:
  COMPId p ACT RES EV WORLD n c cv ⇒
  app (p:'ffi ffi_proj) interest_v [cv] emp
    (POSTv v. &EVSET EV (waiting_on c []) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPId _ _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def interest_v_def >>
  qpat_x_assum ‘STEPId _ _ _ _ _ _ _ _’ mp_tac >>
  Cases_on ‘n’ >> simp[STEPId_def] >> rw[] >>
  xmatch >> xmatch >>
  TRY (xvar >> xsimpl >> simp[waiting_on_def] >> NO_TAC) >>
  xcon >> xsimpl >> simp[waiting_on_def, finished_def, EVSET_def] >>
  qexists_tac ‘[]’ >> simp[]
QED

Theorem skip2_spec_d:
  STEPId p ACT RES EV (SNAPSHOT READY (R : 'r -> v -> bool)) n g sv ∧ NUM k kv ⇒
  app (p:'ffi ffi_proj) skip2_v [kv; sv] emp
    (POSTv v. &STEPId p ACT RES EV (SNAPSHOT READY R) n (skipping2 k g) v)
Proof
  rpt strip_tac >> xcf_with_def skip2_v_def >>
  qpat_x_assum ‘STEPId _ _ _ _ _ _ _ sv’ mp_tac >>
  Cases_on ‘n’ >> simp[STEPId_def] >> strip_tac >> gvs[]
  >- (xmatch >> xvar >> xsimpl >>
      simp[skipping2_def, skipping_finished] >> metis_tac[])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      simp[skipping2_def, skip_results_def] >>
      gvs[skipping2_def, skipping_def, skip_results_def])
  >- (xmatch >> xvar >> xsimpl >>
      simp[skipping2_def, skipping_finished] >> metis_tac[])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      simp[suspended2_skipping2] >>
      simp[skipping2_def, skip_results_def] >>
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
   bind2, up to depth n
   ------------------------------------------------------------------------ *)

Theorem bind2_Done_spec_d:
  STEPId p ACT A EV (SNAPSHOT READY R) k c (Done2V xv) ∧
  LIST_TYPE (ACT : 'act -> v -> bool) (c.run []).actions av ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPId p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
  app (p:'ffi ffi_proj) bind2_v [Conv NONE [av; Done2V xv]; gv] emp
    (POSTv v. &COMPId p ACT B EV (SNAPSHOT READY R) n (bind2 c g) v)
Proof
  rw[STEPId_Done] >> rename1 ‘finished As x’ >>
  ‘bind2 c g = prepend2 As (skipping2 (LENGTH As) (g x))’
    by (irule bind2_finished >> simp[]) >>
  gvs[finished_def] >>
  xcf_with_def bind2_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv r. &COMPId p ACT B EV (SNAPSHOT READY R) n (g x) r’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  gvs[COMPId_def, POLL_RESULT2_def] >> xmatch >>
  rename1 ‘LIST_TYPE ACT ((g x).run []).actions av2’ >>
  xlet ‘POSTv nv. &NUM (LENGTH As) nv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> metis_tac[]) >>
  xlet ‘POSTv sv2. &STEPId p ACT B EV (SNAPSHOT READY R) n
                     (skipping2 (LENGTH As) (g x)) sv2’
  >- (xapp_spec skip2_spec_d >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv lv. &LIST_TYPE ACT (As ++ ((g x).run []).actions) lv’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xcon >> xsimpl >>
  simp[POLL_RESULT2_def, prepend2_def, skipping2_def] >>
  ‘prepend2 As (skipping2 (LENGTH As) (g x)) =
   <| run := prepend As (skipping (LENGTH As) (g x).run);
      interest := λh. (g x).interest (skip_results (LENGTH As) h) |>’
    by simp[prepend2_def, skipping2_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule STEPId_prepend2 >> simp[]
QED

(* MAIN (helper): bind2 up to depth n *)
Theorem bind2_spec_d:
  ∀n c cv.
    wf c.run ∧ COMPId p ACT A EV (SNAPSHOT READY R) n c cv ∧
    (∀x xv. A x xv ⇒
       returns p gv [xv]
         (COMPId p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
    app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
      (POSTv v. &COMPId p (ACT : 'act -> v -> bool) B EV (SNAPSHOT READY R) n
                  (bind2 c g) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMPId _ _ _ _ _ _ c cv’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPId _ _ _ _ _ _ c sv’ mp_tac >>
  simp[Once STEPId_def] >> rw[]
  >- (irule bind2_Done_spec_d >> simp[STEPId_Done] >> metis_tac[])
  >- (xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[COMPId_def, POLL_RESULT2_def, STEPId_def] >>
      simp[bind2_def, bind_NIL_running] >>
      simp[bind_interest_def, Once first_prefix_def] >> gvs[])
  >- (irule bind2_Done_spec_d >> simp[STEPId_Done] >> metis_tac[])
  >- (xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[COMPId_def, POLL_RESULT2_def, STEPId_def] >>
      simp[bind2_def, bind_NIL_running] >>
      conj_tac
      >- (simp[bind_interest_def, Once first_prefix_def] >> gvs[]) >>
      rpt strip_tac >> simp[returns_def] >>
      simp[GSYM bind2_def, suspended2_bind2] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv r. &COMPId p ACT A EV (SNAPSHOT READY R) n (suspended2 c [w]) r’
      >- (first_x_assum drule >> rw[returns_def, GSYM COMPId_def] >> xapp) >>
      first_x_assum (qspecl_then [‘suspended2 c [w]’, ‘r’] mp_tac) >>
      simp[wf_suspended, suspended2_run, GSYM COMPId_def] >>
      impl_tac
      >- (rpt strip_tac >> irule returns_mono >>
          qpat_x_assum ‘∀x xv. A x xv ⇒ _’ (drule_then (irule_at Any)) >>
          rpt strip_tac >> irule COMPId_SUC_IMP >> simp[]) >>
      strip_tac >> xapp)
QED

(* A guarded bind2 (the first part has not finished in its first round) is
   implemented up to depth 0 whatever the continuation *)
Theorem bind2_guarded_spec_0:
  (c.run []).result = NONE ∧ COMPId p ACT A EV (SNAPSHOT READY R) 0 c cv ⇒
  app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
    (POSTv v. &COMPId p (ACT : 'act -> v -> bool) B EV
                (SNAPSHOT READY (R : 'r -> v -> bool)) 0 (bind2 c g) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPId _ _ _ _ _ _ c cv’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  gvs[STEPId_def, finished_def] >>
  xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
  simp[COMPId_def, POLL_RESULT2_def, STEPId_def] >>
  simp[bind2_def, bind_NIL_running] >>
  simp[bind_interest_def, Once first_prefix_def] >> gvs[]
QED

(* MAIN (helper): a guarded bind2 gains one level of depth.  This is where
   recursion through a continuation makes progress. *)
Theorem bind2_guarded_spec_d:
  wf c.run ∧ (c.run []).result = NONE ∧
  COMPId p ACT A EV (SNAPSHOT READY R) (SUC n) c cv ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPId p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
  app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
    (POSTv v. &COMPId p (ACT : 'act -> v -> bool) B EV (SNAPSHOT READY R) (SUC n)
                (bind2 c g) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPId _ _ _ _ _ _ c cv’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  gvs[STEPId_def, finished_def] >>
  xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
  simp[COMPId_def, POLL_RESULT2_def, STEPId_def] >>
  simp[bind2_def, bind_NIL_running] >>
  conj_tac
  >- (simp[bind_interest_def, Once first_prefix_def] >> gvs[]) >>
  rpt strip_tac >> simp[returns_def] >>
  simp[GSYM bind2_def, suspended2_bind2] >>
  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv r. &COMPId p ACT A EV (SNAPSHOT READY R) n (suspended2 c [w]) r’
  >- (first_x_assum drule >> rw[returns_def, GSYM COMPId_def] >> xapp) >>
  ‘app p bind2_v [r; gv] emp
     (POSTv v. &COMPId p ACT B EV (SNAPSHOT READY R) n
                 (bind2 (suspended2 c [w]) g) v)’
    by (irule bind2_spec_d >> simp[wf_suspended, suspended2_run] >> metis_tac[]) >>
  gvs[COMPId_def] >> qpat_x_assum ‘app _ bind2_v _ _ _’ xapp_spec >> xsimpl
QED

(* ------------------------------------------------------------------------
   map2, up to depth n
   ------------------------------------------------------------------------ *)

Theorem map2_spec_d:
  ∀n c cv.
    COMPId p ACT A EV WORLD n c cv ∧
    (∀x xv. A x xv ⇒ returns p fv [xv] (B (f x))) ⇒
    app (p:'ffi ffi_proj) map2_v [fv; cv] emp
      (POSTv v. &COMPId p ACT B EV WORLD n (map2 f c) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMPId _ _ _ _ _ _ c cv’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPId _ _ _ _ _ _ c sv’ mp_tac >>
  simp[Once STEPId_def] >> rw[] >>
  xcf_with_def map2_v_def >> xmatch >> xmatch
  >~ [‘c.run = finished _ _’]
  >- (xlet ‘POSTv yv. &B (f x) yv’
      >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
      xcons >> drule map2_finished >> disch_then (qspec_then ‘f’ assume_tac) >>
      simp[COMPId_def, POLL_RESULT2_def, STEPId_def] >>
      gvs[finished_def, map2_def, asyncLevel1Theory.map_def] >> metis_tac[])
  >~ [‘c.run = finished _ _’]
  >- (xlet ‘POSTv yv. &B (f x) yv’
      >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
      xcons >> drule map2_finished >> disch_then (qspec_then ‘f’ assume_tac) >>
      simp[COMPId_def, POLL_RESULT2_def, STEPId_def] >>
      gvs[finished_def, map2_def, asyncLevel1Theory.map_def] >> metis_tac[])
  >~ [‘COMPId _ _ _ _ _ 0’]
  >- (xfun ‘k2’ >> xcons >>
      simp[COMPId_def, POLL_RESULT2_def, STEPId_def] >>
      simp[map2_def, asyncLevel1Theory.map_def])
  >> xfun ‘k2’ >> xcons >>
  simp[COMPId_def, POLL_RESULT2_def, STEPId_def, suspended2_map2] >>
  simp[map2_def, asyncLevel1Theory.map_def] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv r. &COMPId p ACT A EV WORLD n (suspended2 c [w]) r’
  >- (first_x_assum drule >> rw[returns_def, GSYM COMPId_def] >> xapp) >>
  first_x_assum (qspecl_then [‘suspended2 c [w]’, ‘r’] mp_tac) >>
  simp[] >> strip_tac >>
  ‘map2 f (suspended2 c [w]) =
   <| run := map f (suspended2 c [w]).run; interest := (suspended2 c [w]).interest |>’
    by simp[map2_def] >>
  gvs[COMPId_def] >> xapp
QED

(* ------------------------------------------------------------------------
   both2, up to depth n
   ------------------------------------------------------------------------ *)

Theorem EVSET_APPEND[local]:
  LIST_TYPE EV l1 v1 ∧ LIST_TYPE EV l2 v2 ∧ LIST_TYPE EV (l1 ++ l2) v ⇒
  EVSET EV (LIST_TO_SET l1 ∪ LIST_TO_SET l2) v
Proof
  rw[EVSET_def] >> qexists_tac ‘l1 ++ l2’ >> simp[]
QED

val both2_prelude =
  rpt strip_tac >>
  qpat_assum ‘COMPId _ _ _ _ _ _ c1 _’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  qpat_assum ‘COMPId _ _ _ _ _ _ c2 _’
    (strip_assume_tac o REWRITE_RULE[COMPId_def, POLL_RESULT2_def]) >>
  gvs[] >>
  xcf_with_def both2_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv av. &LIST_TYPE ACT ((c1.run []).actions ++ (c2.run []).actions) av’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  qpat_x_assum ‘STEPId _ _ _ _ _ _ c1 _’ mp_tac >> simp[Once STEPId_def] >>
  qpat_x_assum ‘STEPId _ _ _ _ _ _ c2 _’ mp_tac >> simp[Once STEPId_def] >>
  rw[] >>
  (xlet_auto >- (xcon >> xsimpl));

val both2_done_tac =
  xmatch >> xcons >>
  simp[COMPId_def, POLL_RESULT2_def, both2_def] >>
  gvs[both_finished_finished, finished_def] >>
  simp[STEPId_Done] >>
  irule_at Any EQ_REFL >> simp[PAIR_TYPE_def];

fun both2_pending_tac (n_is_suc : bool) =
  xmatch >> xfun ‘k’ >>
  xlet ‘POSTv i2. &EVSET EV (waiting_on c2 []) i2’
  >- (xapp_spec interest_spec_d >> first_assum (irule_at Any)) >>
  xlet ‘POSTv i1. &EVSET EV (waiting_on c1 []) i1’
  >- (xapp_spec interest_spec_d >> first_assum (irule_at Any)) >>
  qpat_x_assum ‘EVSET _ (waiting_on c1 _) _’
    (strip_assume_tac o REWRITE_RULE[EVSET_def]) >>
  qpat_x_assum ‘EVSET _ (waiting_on c2 _) _’
    (strip_assume_tac o REWRITE_RULE[EVSET_def]) >>
  rename1 ‘LIST_TYPE EV l1 i1’ >> rename1 ‘LIST_TYPE EV l2 i2’ >>
  xlet ‘POSTv ev. &LIST_TYPE EV (l1 ++ l2) ev’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xcons >>
  simp[COMPId_def, POLL_RESULT2_def, both2_NIL] >>
  TRY (conj_tac >- gvs[]) >>
  simp[STEPId_def] >>
  conj_tac
  >- (simp[both2_def, both_NIL_poll] >> gvs[finished_def] >>
      every_case_tac >> gvs[]) >>
  (if not n_is_suc then (simp[both2_NIL] >> metis_tac[EVSET_APPEND]) else
  conj_tac
  >- (simp[both2_NIL] >> metis_tac[EVSET_APPEND]) >>
  rpt strip_tac >> simp[returns_def] >>
  simp[suspended2_both2] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def] >> xmatch >>
  qabbrev_tac ‘kk = LENGTH (c1.run []).actions’ >>
  xlet ‘POSTv nv. &NUM kk nv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> simp[Abbr ‘kk’] >> metis_tac[]) >>
  xlet ‘POSTv tv. &LIST_TYPE R (TAKE kk w.results) tv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.take_v_thm) >>
      xsimpl >> simp[mllistTheory.take_def] >> metis_tac[]) >>
  xlet ‘POSTv w1. &(w1 = Conv NONE [rv; nv; tv])’ >- (xcon >> xsimpl) >>
  xlet ‘POSTv c1'. &COMPId p ACT A EV (SNAPSHOT READY R) n
                        (suspended2 c1 [take_snap kk w]) c1'’
  >- (xapp_spec poll2_spec_d >> simp[SNAPSHOT_def, take_snap_def] >>
      metis_tac[]) >>
  xlet ‘POSTv dv. &LIST_TYPE R (DROP kk w.results) dv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.drop_v_thm) >>
      xsimpl >> simp[mllistTheory.drop_def] >> metis_tac[]) >>
  xlet ‘POSTv w2. &(w2 = Conv NONE [rv; nv; dv])’ >- (xcon >> xsimpl) >>
  xlet ‘POSTv c2'. &COMPId p ACT B EV (SNAPSHOT READY R) n
                        (suspended2 c2 [skip_snap kk w]) c2'’
  >- (xapp_spec poll2_spec_d >> simp[SNAPSHOT_def, skip_snap_def] >>
      metis_tac[]) >>
  first_x_assum (qspecl_then [‘suspended2 c1 [take_snap kk w]’,
                              ‘suspended2 c2 [skip_snap kk w]’, ‘c1'’, ‘c2'’]
                   mp_tac) >>
  simp[wf_suspended, suspended2_run] >> strip_tac >>
  gvs[COMPId_def] >> xapp >>
  xsimpl >> gvs[markerTheory.Abbrev_def, finished_def]);

(* MAIN (helper): both2 up to depth n *)
Theorem both2_spec_d:
  ∀n c1 c2 cv1 cv2.
    wf c1.run ∧ wf c2.run ∧
    COMPId p ACT A EV (SNAPSHOT READY (R : 'r -> v -> bool)) n c1 cv1 ∧
    COMPId p ACT B EV (SNAPSHOT READY R) n c2 cv2 ⇒
    app (p:'ffi ffi_proj) both2_v [cv1; cv2] emp
      (POSTv v. &COMPId p (ACT : 'act -> v -> bool) (PAIR_TYPE A B) EV
                  (SNAPSHOT READY R) n (both2 c1 c2) v)
Proof
  Induct
  >- (both2_prelude >> FIRST [both2_done_tac, both2_pending_tac false])
  >- (both2_prelude >> FIRST [both2_done_tac, both2_pending_tac true])
QED
