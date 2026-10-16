(*
  CF specs for the replayed Level 2 library (lib2SockProg), against STEPI /
  COMPI: return2, wait_on, never2, emit2, poll2, interest, skip2, bind2,
  map2, both2.  The proofs are loopBlock2Spec's and cakeml/level2's
  lib2Spec's (layer 5).
*)
Theory lib2SockSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 libModel
  libProg libBothModel lib2SockModel lib2SockProg ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "lib2SockProg"



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

(* MAIN: return2 x builds a finished computation that has emitted nothing. *)
Theorem return2_specI:
  RES x xv ⇒
  app (p:'ffi ffi_proj) return2_v [xv] emp
    (POSTv v. &COMPI p ACT RES EV WORLD (return2 x) v)
Proof
  strip_tac >> xcf_with_def return2_v_def >> xcons >>
  simp[COMPI_def, POLL_RESULT2_def, STEPI_Done, return2_def,
       return_finished, finished_def] >>
  metis_tac[]
QED


Theorem wait_on_NIL[local]:
  ((wait_on e q).run []).actions = [] ∧ ((wait_on e q).run []).result = NONE ∧
  (wait_on e q).interest h = {e}
Proof
  simp[wait_on_def, wait_def, first_some_def]
QED


Theorem wait_on_specI_n:
  ∀n p e ev q qv.
    EV e ev ∧
    (∀w wv. WORLD w wv ⇒
       returns p qv [wv] (OPTION_TYPE RES (if e ∈ w.ready then q w else NONE))) ⇒
    app (p:'ffi ffi_proj) wait_on_v [ev; qv] emp
      (POSTv v. &POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) (wait_on e q) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def wait_on_v_def >>
  xfun ‘k’ >> xcons >>
  simp[POLL_RESULT2_def, wait_on_NIL, STEPIn_def] >>
  conj_tac >- (simp[EVSET_def] >> qexists_tac ‘[e]’ >> simp[LIST_TYPE_def]) >>
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
      Cases_on ‘n’ >> simp[STEPIn_def] >> metis_tac[])
QED


(* MAIN: wait_on e q declares e and finishes at the first snapshot w in
   which e is ready and q w = SOME a, with result a. *)
Theorem wait_on_specI:
  EV e ev ∧
  (∀w wv. WORLD w wv ⇒
     returns p qv [wv] (OPTION_TYPE RES (if e ∈ w.ready then q w else NONE))) ⇒
  app (p:'ffi ffi_proj) wait_on_v [ev; qv] emp
    (POSTv v. &COMPI p ACT RES EV WORLD (wait_on e q) v)
Proof
  rpt strip_tac >> irule app_COMPI_of_approx >> simp[] >>
  metis_tac[wait_on_specI_n]
QED


Theorem never2_NIL[local]:
  (never2.run []).actions = [] ∧ (never2.run []).result = NONE ∧
  never2.interest h = ∅
Proof
  simp[asyncLoop2Theory.never2_def, never_def, wait_def, first_some_def]
QED


Theorem never2_specI_n:
  ∀n uv. UNIT_TYPE () uv ⇒
    app (p:'ffi ffi_proj) never2_v [uv] emp
      (POSTv v. &POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) never2 v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def never2_v_def >>
  xfun ‘k’ >> xcons >>
  simp[POLL_RESULT2_def, never2_NIL, STEPIn_def, EVSET_NIL] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv u. &UNIT_TYPE () u’ >- (xcon >> xsimpl) >>
  simp[suspended2_never2] >> xapp >> gvs[UNIT_TYPE_def]
QED


(* never2: never finishes, declares nothing, does nothing. *)
Theorem never2_specI:
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) never2_v [uv] emp
    (POSTv v. &COMPI p ACT RES EV WORLD never2 v)
Proof
  rpt strip_tac >> irule app_COMPI_of_approx >> simp[] >>
  metis_tac[never2_specI_n]
QED


(* MAIN: emit2 a emits a in its first round, declares no event (it waits
   only for its response), and finishes at the next snapshot with the
   first response; with no response it never finishes. *)
Theorem emit2_specI:
  ACT a av ⇒
  app (p:'ffi ffi_proj) emit2_v [av] emp
    (POSTv v. &COMPI p ACT R EV (SNAPSHOT READY R) (emit2 a) v)
Proof
  rpt strip_tac >> xcf_with_def emit2_v_def >> xfun ‘k’ >> xcons >>
  simp[COMPI_def, POLL_RESULT2_def, emit2_def, emit_def, LIST_TYPE_def,
       STEPI_Pending, EVSET_NIL] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def] >> xmatch >>
  Cases_on ‘w.results’ >> gvs[LIST_TYPE_def] >> xmatch
  >- (xlet ‘POSTv u. &UNIT_TYPE () u’ >- (xcon >> xsimpl) >>
      ‘suspended2 (emit2 a) [w] = never2’ by simp[suspended2_emit2_NIL] >>
      gvs[emit2_def, emit_def] >> xapp_spec never2_specI >> simp[])
  >- (xcons >>
      ‘(suspended2 (emit2 a) [w]).run = finished [] h’
        by metis_tac[suspended2_emit2_CONS] >>
      gvs[emit2_def, emit_def] >>
      simp[COMPI_def, POLL_RESULT2_def, STEPI_Done] >>
      simp[finished_def] >> metis_tac[])
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

(* ------------------------------------------------------------------------
   both2
   ------------------------------------------------------------------------ *)

Theorem EVSET_APPEND[local]:
  LIST_TYPE EV l1 v1 ∧ LIST_TYPE EV l2 v2 ∧ LIST_TYPE EV (l1 ++ l2) v ⇒
  EVSET EV (LIST_TO_SET l1 ∪ LIST_TO_SET l2) v
Proof
  rw[EVSET_def] >> qexists_tac ‘l1 ++ l2’ >> simp[]
QED

(* The common start of both2_specI_n: take the pairs apart, compute
   acts1 @ acts2, and split on whether each side is Done. *)
val both2_prelude =
  rpt strip_tac >>
  qpat_assum ‘COMPI _ _ _ _ _ c1 _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  qpat_assum ‘COMPI _ _ _ _ _ c2 _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >>
  xcf_with_def both2_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv av. &LIST_TYPE ACT ((c1.run []).actions ++ (c2.run []).actions) av’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  qpat_x_assum ‘STEPI _ _ _ _ _ c1 _’ mp_tac >> simp[Once STEPI_cases] >>
  qpat_x_assum ‘STEPI _ _ _ _ _ c2 _’ mp_tac >> simp[Once STEPI_cases] >>
  rw[] >>
  (xlet_auto >- (xcon >> xsimpl));

(* Both sides Done: both2 returns (acts, Done2 (x, y)) *)
val both2_done_tac =
  xmatch >> xcons >>
  simp[POLL_RESULT2_def, both2_def] >>
  gvs[both_finished_finished, finished_def] >>
  Cases_on ‘n’ >> simp[STEPIn_def] >>
  irule_at Any EQ_REFL >> simp[PAIR_TYPE_def];

(* Otherwise: both2 returns (acts, Pending2 (es1 @ es2) k).  The closure k
   polls each side with its share of the results and continues with both2
   (by the induction hypothesis, when there is one). *)
fun both2_pending_tac (n_is_suc : bool) =
  xmatch >> xfun ‘k’ >>
  xlet ‘POSTv i2. &EVSET EV (waiting_on c2 []) i2’
  >- (xapp_spec interest_specI >> first_assum (irule_at Any)) >>
  xlet ‘POSTv i1. &EVSET EV (waiting_on c1 []) i1’
  >- (xapp_spec interest_specI >> first_assum (irule_at Any)) >>
  qpat_x_assum ‘EVSET _ (waiting_on c1 _) _’
    (strip_assume_tac o REWRITE_RULE[EVSET_def]) >>
  qpat_x_assum ‘EVSET _ (waiting_on c2 _) _’
    (strip_assume_tac o REWRITE_RULE[EVSET_def]) >>
  rename1 ‘LIST_TYPE EV l1 i1’ >> rename1 ‘LIST_TYPE EV l2 i2’ >>
  xlet ‘POSTv ev. &LIST_TYPE EV (l1 ++ l2) ev’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xcons >>
  simp[POLL_RESULT2_def, both2_NIL] >>
  TRY (conj_tac >- gvs[]) >> TRY (gvs[] >> NO_TAC) >>
  (if not n_is_suc then ALL_TAC else
  simp[STEPIn_def] >>
  conj_tac
  >- (simp[both2_def, both_NIL_poll] >> gvs[finished_def] >>
      every_case_tac >> gvs[]) >>
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
  xlet ‘POSTv c1'. &COMPI p ACT A EV (SNAPSHOT READY R)
                        (suspended2 c1 [take_snap kk w]) c1'’
  >- (xapp_spec poll2_specI >> simp[SNAPSHOT_def, take_snap_def] >>
      metis_tac[]) >>
  xlet ‘POSTv dv. &LIST_TYPE R (DROP kk w.results) dv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.drop_v_thm) >>
      xsimpl >> simp[mllistTheory.drop_def] >> metis_tac[]) >>
  xlet ‘POSTv w2. &(w2 = Conv NONE [rv; nv; dv])’ >- (xcon >> xsimpl) >>
  xlet ‘POSTv c2'. &COMPI p ACT B EV (SNAPSHOT READY R)
                        (suspended2 c2 [skip_snap kk w]) c2'’
  >- (xapp_spec poll2_specI >> simp[SNAPSHOT_def, skip_snap_def] >>
      metis_tac[]) >>
  first_x_assum (qspecl_then [‘suspended2 c1 [take_snap kk w]’,
                              ‘suspended2 c2 [skip_snap kk w]’, ‘c1'’, ‘c2'’]
                   mp_tac) >>
  simp[wf_suspended, suspended2_run] >> strip_tac >> xapp >>
  xsimpl >> gvs[markerTheory.Abbrev_def, finished_def]);

Theorem both2_specI_n:
  ∀n c1 c2 cv1 cv2.
    wf c1.run ∧ wf c2.run ∧
    COMPI p ACT A EV (SNAPSHOT READY (R : 'r -> v -> bool)) c1 cv1 ∧
    COMPI p ACT B EV (SNAPSHOT READY R) c2 cv2 ⇒
    app (p:'ffi ffi_proj) both2_v [cv1; cv2] emp
      (POSTv v. &POLL_RESULT2 (ACT : 'act -> v -> bool)
                  (STEPIn p ACT (PAIR_TYPE A B) EV (SNAPSHOT READY R) n)
                  (both2 c1 c2) v)
Proof
  Induct
  >- (both2_prelude >> FIRST [both2_done_tac, both2_pending_tac false])
  >- (both2_prelude >> FIRST [both2_done_tac, both2_pending_tac true])
QED

(* MAIN: both2 c1 c2 implements the model's both2 c1 c2: each round the
   left side's actions then the right side's, each side its own results,
   the pair of results once both have finished, and while not, the
   declared events of the unfinished sides (in some order). *)
Theorem both2_specI:
  wf c1.run ∧ wf c2.run ∧
  COMPI p ACT A EV (SNAPSHOT READY (R : 'r -> v -> bool)) c1 cv1 ∧
  COMPI p ACT B EV (SNAPSHOT READY R) c2 cv2 ⇒
  app (p:'ffi ffi_proj) both2_v [cv1; cv2] emp
    (POSTv v. &COMPI p (ACT : 'act -> v -> bool) (PAIR_TYPE A B) EV
                (SNAPSHOT READY R) (both2 c1 c2) v)
Proof
  rpt strip_tac >> irule app_COMPI_of_approx >> simp[] >>
  metis_tac[both2_specI_n]
QED
