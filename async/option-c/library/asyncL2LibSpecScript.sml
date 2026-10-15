(*
  CF specs for the Level 2 library against STEPI / COMPI (asyncL2LibProg):
  - return2, wait_on, never2, emit2: carried over from asyncL2BlkSpec;
  - poll2, interest, skip2, bind2: re-proved (they take a computation
    value, whose events are now any list of the interest);
  - map2 and both2: new.  both2 declares the union of what its unfinished
    sides declare (asyncLevel2 both2_def).
*)
Theory asyncL2LibSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncCfActModel asyncCfActProg
  asyncCfActBothModel asyncL2BlkModel asyncL2BlkProg asyncL2BlkSpec
  asyncL2LibModel asyncL2LibProg ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncL2LibProg"

val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

Theorem LIST_TYPE_NIL[local,simp]:
  LIST_TYPE A [] v ⇔ v = Conv (SOME (TypeStamp «[]» 1)) []
Proof
  simp[LIST_TYPE_def]
QED

Theorem EVSET_NIL[local]:
  EVSET EV ∅ (Conv (SOME (TypeStamp «[]» 1)) [])
Proof
  simp[EVSET_def] >> qexists_tac ‘[]’ >> simp[]
QED

Theorem app_COMP2_COMPI[local]:
  app (p:'ffi ffi_proj) f args H (POSTv v. &COMP2 p ACT RES EV WORLD c v) ⇒
  app p f args H (POSTv v. &COMPI p ACT RES EV WORLD c v)
Proof
  strip_tac >> irule app_weaken >> first_x_assum (irule_at Any) >>
  rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def, POSTv_cond] >>
  metis_tac[COMP2_IMP_COMPI]
QED

(* ------------------------------------------------------------------------
   Carried over
   ------------------------------------------------------------------------ *)

Theorem return2_specI:
  RES x xv ⇒
  app (p:'ffi ffi_proj) return2_v [xv] emp
    (POSTv v. &COMPI p ACT RES EV WORLD (return2 x) v)
Proof
  metis_tac[app_COMP2_COMPI, return2_spec]
QED

Theorem wait_on_specI:
  EV e ev ∧
  (∀w wv. WORLD w wv ⇒
     returns p qv [wv] (OPTION_TYPE RES (if e ∈ w.ready then q w else NONE))) ⇒
  app (p:'ffi ffi_proj) wait_on_v [ev; qv] emp
    (POSTv v. &COMPI p ACT RES EV WORLD (wait_on e q) v)
Proof
  metis_tac[app_COMP2_COMPI, wait_on_spec]
QED

Theorem never2_specI:
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) never2_v [uv] emp
    (POSTv v. &COMPI p ACT RES EV WORLD never2 v)
Proof
  metis_tac[app_COMP2_COMPI, never2_spec]
QED

Theorem emit2_specI:
  ACT a av ⇒
  app (p:'ffi ffi_proj) emit2_v [av] emp
    (POSTv v. &COMPI p ACT R EV (SNAPSHOT READY R) (emit2 a) v)
Proof
  metis_tac[app_COMP2_COMPI, emit2_spec]
QED

(* ------------------------------------------------------------------------
   Re-proved
   ------------------------------------------------------------------------ *)

Theorem poll2_specI:
  COMPI p ACT RES EV WORLD c cv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll2_v [cv; wv] emp
    (POSTv v. &COMPI p ACT RES EV WORLD (suspended2 c [w]) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPI _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def poll2_v_def >>
  qpat_x_assum ‘STEPI _ _ _ _ _ _ _’ mp_tac >> simp[Once STEPI_cases] >> rw[]
  >- (xmatch >> xmatch >> xcons >>
      simp[COMPI_def, POLL_RESULT2_def, suspended2_run, suspended_finished_one,
           STEPI_Done] >>
      simp[finished_def] >> metis_tac[])
  >- (xmatch >> xmatch >> first_x_assum drule >>
      rw[returns_def, GSYM COMPI_eta] >> xapp)
QED

(* MAIN: interest c returns the events c is waiting for (in some order) *)
Theorem interest_specI:
  COMPI p ACT RES EV WORLD c cv ⇒
  app (p:'ffi ffi_proj) interest_v [cv] emp
    (POSTv v. &EVSET EV (waiting_on c []) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPI _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def interest_v_def >>
  qpat_x_assum ‘STEPI _ _ _ _ _ _ _’ mp_tac >> simp[Once STEPI_cases] >> rw[]
  >- (xmatch >> xmatch >> xcon >> xsimpl >>
      simp[waiting_on_def, finished_def, EVSET_NIL])
  >- (xmatch >> xmatch >> xvar >> xsimpl >> simp[waiting_on_def])
QED

Theorem skip2_specI:
  STEPI p ACT RES EV (SNAPSHOT READY (R : 'r -> v -> bool)) g sv ∧ NUM k kv ⇒
  app (p:'ffi ffi_proj) skip2_v [kv; sv] emp
    (POSTv v. &STEPI p ACT RES EV (SNAPSHOT READY R) (skipping2 k g) v)
Proof
  rpt strip_tac >> xcf_with_def skip2_v_def >>
  qpat_x_assum ‘STEPI _ _ _ _ _ _ sv’ mp_tac >> simp[Once STEPI_cases] >> rw[]
  >- (xmatch >> xvar >> xsimpl >>
      simp[STEPI_Done, skipping2_def, skipping_finished] >> metis_tac[])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      simp[STEPI_Pending, suspended2_skipping2] >>
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
      rw[returns_def, GSYM COMPI_eta] >> xapp)
QED

Theorem bind2_Done_specI_n:
  STEPI p ACT A EV (SNAPSHOT READY R) c (Done2V xv) ∧
  LIST_TYPE (ACT : 'act -> v -> bool) (c.run []).actions av ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPI p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
  app (p:'ffi ffi_proj) bind2_v [Conv NONE [av; Done2V xv]; gv] emp
    (POSTv v. &POLL_RESULT2 ACT (STEPIn p ACT B EV (SNAPSHOT READY R) n)
                (bind2 c g) v)
Proof
  rw[STEPI_Done] >> rename1 ‘finished As x’ >>
  ‘bind2 c g = prepend2 As (skipping2 (LENGTH As) (g x))’
    by (irule bind2_finished >> simp[]) >>
  gvs[finished_def] >>
  xcf_with_def bind2_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv r. &COMPI p ACT B EV (SNAPSHOT READY R) (g x) r’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  gvs[COMPI_def, POLL_RESULT2_def] >> xmatch >>
  rename1 ‘LIST_TYPE ACT ((g x).run []).actions av2’ >>
  xlet ‘POSTv nv. &NUM (LENGTH As) nv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> metis_tac[]) >>
  xlet ‘POSTv sv2. &STEPI p ACT B EV (SNAPSHOT READY R)
                     (skipping2 (LENGTH As) (g x)) sv2’
  >- (xapp_spec skip2_specI >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv lv. &LIST_TYPE ACT (As ++ ((g x).run []).actions) lv’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xcon >> xsimpl >>
  simp[POLL_RESULT2_def, prepend2_def, skipping2_def] >>
  irule STEPI_IMP_STEPIn >>
  ‘prepend2 As (skipping2 (LENGTH As) (g x)) =
   <| run := prepend As (skipping (LENGTH As) (g x).run);
      interest := λh. (g x).interest (skip_results (LENGTH As) h) |>’
    by simp[prepend2_def, skipping2_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule STEPI_prepend2 >> simp[]
QED

Theorem bind2_specI_n:
  ∀n c cv.
    wf c.run ∧ COMPI p ACT A EV (SNAPSHOT READY R) c cv ∧
    (∀x xv. A x xv ⇒
       returns p gv [xv]
         (COMPI p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
    app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
      (POSTv v. &POLL_RESULT2 (ACT : 'act -> v -> bool)
                  (STEPIn p ACT B EV (SNAPSHOT READY R) n) (bind2 c g) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMPI _ _ _ _ _ c cv’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPI _ _ _ _ _ c sv’ mp_tac >>
  simp[Once STEPI_cases] >> rw[]
  >- (irule bind2_Done_specI_n >> simp[STEPI_Done] >> metis_tac[])
  >- (xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[POLL_RESULT2_def, bind2_def, bind_NIL_running])
  >- (irule bind2_Done_specI_n >> simp[STEPI_Done] >> metis_tac[])
  >- (xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[POLL_RESULT2_def, bind_NIL_running, STEPIn_def] >>
      simp[bind2_def, bind_NIL_running] >>
      conj_tac
      >- (simp[bind_interest_def, Once first_prefix_def] >> gvs[]) >>
      rpt strip_tac >> simp[returns_def] >>
      simp[GSYM bind2_def, suspended2_bind2] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv r. &COMPI p ACT A EV (SNAPSHOT READY R) (suspended2 c [w]) r’
      >- (first_x_assum drule >> rw[returns_def, GSYM COMPI_eta] >> xapp) >>
      first_x_assum (qspecl_then [‘suspended2 c [w]’, ‘r’] mp_tac) >>
      simp[wf_suspended, suspended2_run] >> strip_tac >> xapp)
QED

(* MAIN: bind2 c g implements the model's bind2 c g *)
Theorem bind2_specI:
  wf c.run ∧ COMPI p ACT A EV (SNAPSHOT READY R) c cv ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPI p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
  app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
    (POSTv v. &COMPI (p:'ffi ffi_proj) (ACT : 'act -> v -> bool) B EV
                (SNAPSHOT READY R) (bind2 c g) v)
Proof
  rpt strip_tac >> irule app_COMPI_of_approx >> simp[] >>
  metis_tac[bind2_specI_n]
QED

(* ------------------------------------------------------------------------
   map2
   ------------------------------------------------------------------------ *)

Theorem map2_specI_n:
  ∀n c cv.
    COMPI p ACT A EV WORLD c cv ∧
    (∀x xv. A x xv ⇒ returns p fv [xv] (B (f x))) ⇒
    app (p:'ffi ffi_proj) map2_v [fv; cv] emp
      (POSTv v. &POLL_RESULT2 ACT (STEPIn p ACT B EV WORLD n) (map2 f c) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMPI _ _ _ _ _ c cv’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPI _ _ _ _ _ c sv’ mp_tac >>
  simp[Once STEPI_cases] >> rw[] >>
  xcf_with_def map2_v_def >> xmatch >> xmatch
  >~ [‘c.run = finished _ _’]
  >- (xlet ‘POSTv yv. &B (f x) yv’
      >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
      xcons >> drule map2_finished >> disch_then (qspec_then ‘f’ assume_tac) >>
      simp[POLL_RESULT2_def, STEPIn_def] >>
      gvs[finished_def, map2_def, asyncLevel1Theory.map_def] >> metis_tac[])
  >~ [‘c.run = finished _ _’]
  >- (xlet ‘POSTv yv. &B (f x) yv’
      >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
      xcons >> drule map2_finished >> disch_then (qspec_then ‘f’ assume_tac) >>
      simp[POLL_RESULT2_def, STEPIn_def] >>
      gvs[finished_def, map2_def, asyncLevel1Theory.map_def] >> metis_tac[])
  >~ [‘STEPIn _ _ _ _ _ 0’]
  >- (xfun ‘k2’ >> xcons >>
      simp[POLL_RESULT2_def, map2_def, asyncLevel1Theory.map_def])
  >> xfun ‘k2’ >> xcons >>
  simp[POLL_RESULT2_def, STEPIn_def, suspended2_map2] >>
  simp[map2_def, asyncLevel1Theory.map_def] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv r. &COMPI p ACT A EV WORLD (suspended2 c [w]) r’
  >- (first_x_assum drule >> rw[returns_def, GSYM COMPI_eta] >> xapp) >>
  first_x_assum (qspecl_then [‘suspended2 c [w]’, ‘r’] mp_tac) >>
  simp[] >> strip_tac >>
  ‘map2 f (suspended2 c [w]) =
   <| run := map f (suspended2 c [w]).run; interest := (suspended2 c [w]).interest |>’
    by simp[map2_def] >>
  gvs[] >> xapp
QED

(* MAIN: map2 f c implements the model's map2 f c: c's actions and
   declared events, and f of its result *)
Theorem map2_specI:
  COMPI p ACT A EV WORLD c cv ∧
  (∀x xv. A x xv ⇒ returns p fv [xv] (B (f x))) ⇒
  app (p:'ffi ffi_proj) map2_v [fv; cv] emp
    (POSTv v. &COMPI p ACT B EV WORLD (map2 f c) v)
Proof
  rpt strip_tac >> irule app_COMPI_of_approx >> simp[] >>
  metis_tac[map2_specI_n]
QED
