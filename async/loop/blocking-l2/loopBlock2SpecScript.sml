(*
  CF specs for the Level 2 library of loopBlock2Prog: return2, poll2,
  interest, wait_on, never2, emit2, skip2 and bind2, each against the HOL
  model's own Level 2 definition (async/model/asyncLevel2Script.sml).
  The proofs follow cf-actions' libSpec, with the declared events
  tracked as well.
*)
Theory loopBlock2Spec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 libModel libProg
  loopBlock2Model loopBlock2Prog ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "loopBlock2Prog"

val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

Theorem LIST_TYPE_NIL[local,simp]:
  LIST_TYPE A [] v ⇔ v = Conv (SOME (TypeStamp «[]» 1)) []
Proof
  simp[LIST_TYPE_def]
QED

Theorem EVLIST_NIL[local]:
  EVLIST EV ∅ (Conv (SOME (TypeStamp «[]» 1)) [])
Proof
  simp[EVLIST_def]
QED

(* MAIN: return2 x builds a finished computation that has emitted nothing. *)
Theorem return2_spec:
  RES x xv ⇒
  app (p:'ffi ffi_proj) return2_v [xv] emp
    (POSTv v. &COMP2 p ACT RES EV WORLD (return2 x) v)
Proof
  strip_tac >> xcf_with_def return2_v_def >> xcons >>
  simp[COMP2_def, POLL_RESULT2_def, STEPA2_Done, return2_def,
       return_finished, finished_def] >>
  metis_tac[]
QED

(* MAIN: polling with snapshot w returns the next round's actions and a
   residual implementing c with w delivered (suspended2 c [w]: the run
   one poll later, and the interest on the longer history). *)
Theorem poll2_spec:
  COMP2 p ACT RES EV WORLD c cv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll2_v [cv; wv] emp
    (POSTv v. &COMP2 p ACT RES EV WORLD (suspended2 c [w]) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMP2 _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP2_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def poll2_v_def >>
  qpat_x_assum ‘STEPA2 _ _ _ _ _ _ _’ mp_tac >> simp[Once STEPA2_cases] >> rw[]
  >- (xmatch >> xmatch >> xcons >>
      simp[COMP2_def, POLL_RESULT2_def, suspended2_run, suspended_finished_one,
           STEPA2_Done] >>
      simp[finished_def] >> metis_tac[])
  >- (xmatch >> xmatch >> first_x_assum drule >>
      rw[returns_def, GSYM COMP2_eta] >> xapp)
QED

(* MAIN: interest c returns the events c is waiting for: the model's
   declared interest while c is unfinished, nothing once it has finished
   (waiting_on c []). *)
Theorem interest_spec:
  COMP2 p ACT RES EV WORLD c cv ⇒
  app (p:'ffi ffi_proj) interest_v [cv] emp
    (POSTv v. &EVLIST EV (waiting_on c []) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMP2 _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP2_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def interest_v_def >>
  qpat_x_assum ‘STEPA2 _ _ _ _ _ _ _’ mp_tac >> simp[Once STEPA2_cases] >> rw[]
  >- (xmatch >> xmatch >> xcon >> xsimpl >>
      simp[waiting_on_def, finished_def, EVLIST_NIL])
  >- (xmatch >> xmatch >> xvar >> xsimpl >> simp[waiting_on_def])
QED

Theorem wait_on_NIL[local]:
  ((wait_on e q).run []).actions = [] ∧ ((wait_on e q).run []).result = NONE ∧
  (wait_on e q).interest h = {e}
Proof
  simp[wait_on_def, wait_def, first_some_def]
QED

Theorem wait_on_spec_n:
  ∀n p e ev q qv.
    EV e ev ∧
    (∀w wv. WORLD w wv ⇒
       returns p qv [wv] (OPTION_TYPE RES (if e ∈ w.ready then q w else NONE))) ⇒
    app (p:'ffi ffi_proj) wait_on_v [ev; qv] emp
      (POSTv v. &POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) (wait_on e q) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def wait_on_v_def >>
  xfun ‘k’ >> xcons >>
  simp[POLL_RESULT2_def, wait_on_NIL, STEPA2n_def] >>
  conj_tac >- simp[EVLIST_def, LIST_TYPE_def] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv ov. &OPTION_TYPE RES (if e ∈ w.ready then q w else NONE) ov’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  Cases_on ‘if e ∈ w.ready then q w else NONE’ >>
  gvs[std_preludeTheory.OPTION_TYPE_def] >> xmatch
  >- (last_x_assum (qspecl_then [‘p’, ‘e’, ‘ev’, ‘q’, ‘qv’] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      ‘suspended2 (wait_on e q) [w] = wait_on e q’
        by (irule suspended2_wait_on_NONE >> Cases_on ‘e ∈ w.ready’ >> gvs[]) >>
      simp[] >> xapp)
  >- (xcons >>
      ‘e ∈ w.ready ∧ q w = SOME x’ by (Cases_on ‘e ∈ w.ready’ >> gvs[]) >>
      drule_all suspended2_wait_on_SOME >> strip_tac >>
      simp[POLL_RESULT2_def, finished_def] >>
      Cases_on ‘n’ >> simp[STEPA2n_def] >> metis_tac[])
QED

(* MAIN: wait_on e q declares e and finishes at the first snapshot w in
   which e is ready and q w = SOME a, with result a. *)
Theorem wait_on_spec:
  EV e ev ∧
  (∀w wv. WORLD w wv ⇒
     returns p qv [wv] (OPTION_TYPE RES (if e ∈ w.ready then q w else NONE))) ⇒
  app (p:'ffi ffi_proj) wait_on_v [ev; qv] emp
    (POSTv v. &COMP2 p ACT RES EV WORLD (wait_on e q) v)
Proof
  rpt strip_tac >> irule app_COMP2_of_approx >> simp[] >>
  metis_tac[wait_on_spec_n]
QED

Theorem never2_NIL[local]:
  (never2.run []).actions = [] ∧ (never2.run []).result = NONE ∧
  never2.interest h = ∅
Proof
  simp[never2_def, never_def, wait_def, first_some_def]
QED

Theorem never2_spec_n:
  ∀n uv. UNIT_TYPE () uv ⇒
    app (p:'ffi ffi_proj) never2_v [uv] emp
      (POSTv v. &POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) never2 v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def never2_v_def >>
  xfun ‘k’ >> xcons >>
  simp[POLL_RESULT2_def, never2_NIL, STEPA2n_def, EVLIST_NIL] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv u. &UNIT_TYPE () u’ >- (xcon >> xsimpl) >>
  simp[suspended2_never2] >> xapp >> gvs[UNIT_TYPE_def]
QED

(* never2: never finishes, declares nothing, does nothing. *)
Theorem never2_spec:
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) never2_v [uv] emp
    (POSTv v. &COMP2 p ACT RES EV WORLD never2 v)
Proof
  rpt strip_tac >> irule app_COMP2_of_approx >> simp[] >>
  metis_tac[never2_spec_n]
QED

(* MAIN: emit2 a emits a in its first round, declares no event (it waits
   only for its response), and finishes at the next snapshot with the
   first response; with no response it never finishes. *)
Theorem emit2_spec:
  ACT a av ⇒
  app (p:'ffi ffi_proj) emit2_v [av] emp
    (POSTv v. &COMP2 p ACT R EV (SNAPSHOT READY R) (emit2 a) v)
Proof
  rpt strip_tac >> xcf_with_def emit2_v_def >> xfun ‘k’ >> xcons >>
  simp[COMP2_def, POLL_RESULT2_def, emit2_def, emit_def, LIST_TYPE_def,
       STEPA2_Pending, EVLIST_NIL] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def] >> xmatch >>
  Cases_on ‘w.results’ >> gvs[LIST_TYPE_def] >> xmatch
  >- (xlet ‘POSTv u. &UNIT_TYPE () u’ >- (xcon >> xsimpl) >>
      ‘suspended2 (emit2 a) [w] = never2’ by simp[suspended2_emit2_NIL] >>
      gvs[emit2_def, emit_def] >> xapp_spec never2_spec >> simp[])
  >- (xcons >>
      ‘(suspended2 (emit2 a) [w]).run = finished [] h’
        by metis_tac[suspended2_emit2_CONS] >>
      gvs[emit2_def, emit_def] >>
      simp[COMP2_def, POLL_RESULT2_def, STEPA2_Done] >>
      simp[finished_def] >> metis_tac[])
QED

(* skip2 k s: the residual s, with the first k responses of its next
   snapshot removed; the declared events are unchanged. *)
Theorem skip2_spec:
  STEPA2 p ACT RES EV (SNAPSHOT READY (R : 'r -> v -> bool)) g sv ∧ NUM k kv ⇒
  app (p:'ffi ffi_proj) skip2_v [kv; sv] emp
    (POSTv v. &STEPA2 p ACT RES EV (SNAPSHOT READY R) (skipping2 k g) v)
Proof
  rpt strip_tac >> xcf_with_def skip2_v_def >>
  qpat_x_assum ‘STEPA2 _ _ _ _ _ _ sv’ mp_tac >> simp[Once STEPA2_cases] >> rw[]
  >- (xmatch >> xvar >> xsimpl >>
      simp[STEPA2_Done, skipping2_def, skipping_finished] >> metis_tac[])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      simp[STEPA2_Pending, suspended2_skipping2] >>
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
      rw[returns_def, GSYM COMP2_eta] >> xapp)
QED

Theorem bind2_Done_spec_n:
  STEPA2 p ACT A EV (SNAPSHOT READY R) c (Done2V xv) ∧
  LIST_TYPE (ACT : 'act -> v -> bool) (c.run []).actions av ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMP2 p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
  app (p:'ffi ffi_proj) bind2_v [Conv NONE [av; Done2V xv]; gv] emp
    (POSTv v. &POLL_RESULT2 ACT (STEPA2n p ACT B EV (SNAPSHOT READY R) n)
                (bind2 c g) v)
Proof
  rw[STEPA2_Done] >> rename1 ‘finished As x’ >>
  ‘bind2 c g = prepend2 As (skipping2 (LENGTH As) (g x))’
    by (irule bind2_finished >> simp[]) >>
  gvs[finished_def] >>
  xcf_with_def bind2_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv r. &COMP2 p ACT B EV (SNAPSHOT READY R) (g x) r’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  gvs[COMP2_def, POLL_RESULT2_def] >> xmatch >>
  rename1 ‘LIST_TYPE ACT ((g x).run []).actions av2’ >>
  xlet ‘POSTv nv. &NUM (LENGTH As) nv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> metis_tac[]) >>
  xlet ‘POSTv sv2. &STEPA2 p ACT B EV (SNAPSHOT READY R)
                     (skipping2 (LENGTH As) (g x)) sv2’
  >- (xapp_spec skip2_spec >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv lv. &LIST_TYPE ACT (As ++ ((g x).run []).actions) lv’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xcon >> xsimpl >>
  simp[POLL_RESULT2_def, prepend2_def, skipping2_def] >>
  irule STEPA2_IMP_STEPA2n >>
  ‘prepend2 As (skipping2 (LENGTH As) (g x)) =
   <| run := prepend As (skipping (LENGTH As) (g x).run);
      interest := λh. (g x).interest (skip_results (LENGTH As) h) |>’
    by simp[prepend2_def, skipping2_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule STEPA2_prepend2 >> simp[]
QED

Theorem bind2_spec_n:
  ∀n c cv.
    wf c.run ∧ COMP2 p ACT A EV (SNAPSHOT READY R) c cv ∧
    (∀x xv. A x xv ⇒
       returns p gv [xv]
         (COMP2 p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
    app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
      (POSTv v. &POLL_RESULT2 (ACT : 'act -> v -> bool)
                  (STEPA2n p ACT B EV (SNAPSHOT READY R) n) (bind2 c g) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMP2 _ _ _ _ _ c cv’
    (strip_assume_tac o REWRITE_RULE[COMP2_def, POLL_RESULT2_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPA2 _ _ _ _ _ c sv’ mp_tac >>
  simp[Once STEPA2_cases] >> rw[]
  >- (irule bind2_Done_spec_n >> simp[STEPA2_Done] >> metis_tac[])
  >- (xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[POLL_RESULT2_def, bind2_def, bind_NIL_running])
  >- (irule bind2_Done_spec_n >> simp[STEPA2_Done] >> metis_tac[])
  >- (xcf_with_def bind2_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[POLL_RESULT2_def, bind_NIL_running, STEPA2n_def] >>
      simp[bind2_def, bind_NIL_running] >>
      conj_tac
      >- (simp[bind_interest_def, Once first_prefix_def] >> gvs[]) >>
      rpt strip_tac >> simp[returns_def] >>
      simp[GSYM bind2_def, suspended2_bind2] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv r. &COMP2 p ACT A EV (SNAPSHOT READY R) (suspended2 c [w]) r’
      >- (first_x_assum drule >> rw[returns_def, GSYM COMP2_eta] >> xapp) >>
      first_x_assum (qspecl_then [‘suspended2 c [w]’, ‘r’] mp_tac) >>
      simp[wf_suspended, suspended2_run] >> strip_tac >> xapp)
QED

(* MAIN: bind2 c g implements the model's bind2 c g: the run as at Level 1,
   and the declared events of every round -- c's while c runs, then g x's
   on the snapshots it is shown -- exactly the model's bind_interest. *)
Theorem bind2_spec:
  wf c.run ∧ COMP2 p ACT A EV (SNAPSHOT READY R) c cv ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMP2 p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
  app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
    (POSTv v. &COMP2 (p:'ffi ffi_proj) (ACT : 'act -> v -> bool) B EV
                (SNAPSHOT READY R) (bind2 c g) v)
Proof
  rpt strip_tac >> irule app_COMP2_of_approx >> simp[] >>
  metis_tac[bind2_spec_n]
QED
