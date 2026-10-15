(*
  CF specs for the actions/responses library of asyncCfActProg:
  return, poll, wait, never, emit, skip and bind, each against the HOL
  model's own definition (async/model).
*)
Theory asyncCfActSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfActProg"

(* Build a value made of nested constructors, e.g. ([], Done x) *)
val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

Theorem LIST_TYPE_NIL[local,simp]:
  LIST_TYPE A [] v ⇔ v = Conv (SOME (TypeStamp «[]» 1)) []
Proof
  simp[LIST_TYPE_def]
QED

(* MAIN: return x builds a finished computation that has emitted nothing. *)
Theorem return_spec:
  RES x xv ⇒
  app (p:'ffi ffi_proj) return_v [xv] emp
    (POSTv v. &COMP p ACT RES WORLD (return x) v)
Proof
  strip_tac >> xcf_with_def return_v_def >>
  xcons >>
  simp[COMP_def, POLL_RESULT_def, STEPA_Done, return_finished, finished_def] >>
  metis_tac[]
QED

(* MAIN: polling with snapshot w returns the next round's actions and a
   residual: together they implement the model computation with w
   delivered.  (Its actions are the model's new actions, see
   suspended_one_actions_NIL.) *)
Theorem poll_spec:
  COMP p ACT RES WORLD m cv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll_v [cv; wv] emp
    (POSTv v. &COMP p ACT RES WORLD (suspended m [w]) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def poll_v_def >>
  qpat_x_assum ‘STEPA _ _ _ _ _ _’ mp_tac >> simp[Once STEPA_cases] >> rw[]
  >- (xmatch >> xmatch >> xcons >>
      simp[COMP_def, POLL_RESULT_def, suspended_finished_one, STEPA_Done] >>
      simp[finished_def] >> metis_tac[])
  >- (xmatch >> xmatch >> first_x_assum drule >>
      rw[returns_def, GSYM COMP_eta] >> xapp)
QED

(* Finite approximation of wait's spec, by induction on n. *)
Theorem wait_spec_n:
  ∀n p f fv.
    (∀w wv. WORLD w wv ⇒ returns p fv [wv] (OPTION_TYPE RES (f w))) ⇒
    app (p:'ffi ffi_proj) wait_v [fv] emp
      (POSTv v. &POLL_RESULT ACT (STEPAn p ACT RES WORLD n) (wait f) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def wait_v_def >> xfun ‘k’ >> xcons >>
  simp[POLL_RESULT_def, wait_def, first_some_def, STEPAn_def] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv ov. &OPTION_TYPE RES (f w) ov’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  Cases_on ‘f w’ >> gvs[std_preludeTheory.OPTION_TYPE_def] >> xmatch
  >- (last_x_assum (qspecl_then [‘p’, ‘f’, ‘fv’] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      simp[suspended_wait_NONE] >> xapp)
  >- (xcons >> imp_res_tac suspended_wait_SOME >>
      simp[POLL_RESULT_def, finished_def] >>
      Cases_on ‘n’ >> simp[STEPAn_def] >> metis_tac[])
QED

(* MAIN: wait f emits nothing and finishes at the first snapshot w with
   f w = SOME a, with result a.  fv may be any CakeML function that
   implements f. *)
Theorem wait_spec:
  (∀w wv. WORLD w wv ⇒ returns p fv [wv] (OPTION_TYPE RES (f w))) ⇒
  app (p:'ffi ffi_proj) wait_v [fv] emp
    (POSTv v. &COMP p ACT RES WORLD (wait f) v)
Proof
  rpt strip_tac >> irule app_COMP_of_approx >> simp[] >>
  metis_tac[wait_spec_n]
QED

(* never: a computation that never finishes and does nothing. *)
Theorem never_spec:
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) never_v [uv] emp
    (POSTv v. &COMP p ACT RES WORLD never v)
Proof
  rpt strip_tac >> xcf_with_def never_v_def >> xfun ‘f’ >>
  simp[never_def] >> xapp_spec wait_spec >> simp[returns_def] >>
  rpt strip_tac >>
  qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
  xcon >> xsimpl >> simp[std_preludeTheory.OPTION_TYPE_def]
QED

(* MAIN: emit a emits a in its first round and finishes at the next
   snapshot, with the first response in it (the response to a).  With no
   response it never finishes, as in the model. *)
Theorem emit_spec:
  ACT a av ⇒
  app (p:'ffi ffi_proj) emit_v [av] emp
    (POSTv v. &COMP p ACT R (SNAPSHOT READY R) (emit a) v)
Proof
  rpt strip_tac >> xcf_with_def emit_v_def >> xfun ‘k’ >> xcons >>
  simp[COMP_def, POLL_RESULT_def, emit_def, LIST_TYPE_def, STEPA_Pending] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  gvs[SNAPSHOT_def] >> xmatch >>
  Cases_on ‘w.results’ >> gvs[LIST_TYPE_def] >> xmatch
  >- (xlet ‘POSTv u. &UNIT_TYPE () u’ >- (xcon >> xsimpl) >>
      simp[suspended_emit_NIL] >> xapp_spec never_spec >> simp[])
  >- (xcons >>
      ‘suspended (emit a) [w] = finished [] h’
        by metis_tac[suspended_emit_CONS] >>
      simp[COMP_def, POLL_RESULT_def, STEPA_Done] >>
      simp[finished_def] >> metis_tac[])
QED

(* skip k s: the residual s, with the first k responses of its next
   snapshot removed (they answer someone else's actions). *)
Theorem skip_spec:
  STEPA p ACT RES (SNAPSHOT READY (R : 'r -> v -> bool)) g sv ∧ NUM k kv ⇒
  app (p:'ffi ffi_proj) skip_v [kv; sv] emp
    (POSTv v. &STEPA p ACT RES (SNAPSHOT READY R) (skipping k g) v)
Proof
  rpt strip_tac >> xcf_with_def skip_v_def >>
  qpat_x_assum ‘STEPA _ _ _ _ _ sv’ mp_tac >> simp[Once STEPA_cases] >> rw[]
  >- (xmatch >> xvar >> xsimpl >>
      simp[STEPA_Done, skipping_finished] >> metis_tac[])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      simp[STEPA_Pending, suspended_skipping] >>
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
      rw[returns_def, GSYM COMP_eta] >> xapp)
QED

(* bind's finished case (the tuple is built right to left, as CakeML
   evaluates), for any approximation depth n: the first part
   m = finished A x is Done; bind calls g x, getting (acts2, s2), and returns
   (A ++ acts2, skip (LENGTH A) s2), which implements bind m g by
   bind_finished. *)
Theorem bind_Done_spec_n:
  STEPA p ACT A (SNAPSHOT READY R) m (DoneV xv) ∧
  LIST_TYPE (ACT : 'act -> v -> bool) (m []).actions av ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv] (COMP p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [Conv NONE [av; DoneV xv]; gv] emp
    (POSTv v. &POLL_RESULT ACT (STEPAn p ACT B (SNAPSHOT READY R) n) (bind m g) v)
Proof
  rw[STEPA_Done] >> rename1 ‘finished As x’ >>
  gvs[finished_def] >>
  xcf_with_def bind_v_def >> xmatch >> xmatch >>
  xlet ‘POSTv r. &COMP p ACT B (SNAPSHOT READY R) (g x) r’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  gvs[COMP_def, POLL_RESULT_def] >> xmatch >>
  rename1 ‘LIST_TYPE ACT (g x []).actions av2’ >>
  xlet ‘POSTv nv. &NUM (LENGTH As) nv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> metis_tac[]) >>
  xlet ‘POSTv sv2. &STEPA p ACT B (SNAPSHOT READY R) (skipping (LENGTH As) (g x)) sv2’
  >- (xapp_spec skip_spec >> simp[] >> metis_tac[]) >>
  xlet ‘POSTv lv. &LIST_TYPE ACT (As ++ (g x []).actions) lv’
  >- (xapp >>
      xsimpl >> metis_tac[]) >>
  xcon >> xsimpl >>
  ‘finished As x = λh. <|actions := As; result := SOME x|>’
    by simp[FUN_EQ_THM, finished_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  simp[bind_finished, POLL_RESULT_def] >>
  irule STEPA_IMP_STEPAn >> irule STEPA_prepend >> simp[]
QED

(* Finite approximation of bind's spec, by induction on n. *)
Theorem bind_spec_n:
  ∀n m mv.
    wf m ∧ COMP p ACT A (SNAPSHOT READY R) m mv ∧
    (∀x xv. A x xv ⇒
       returns p gv [xv]
         (COMP p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
    app (p:'ffi ffi_proj) bind_v [mv; gv] emp
      (POSTv v. &POLL_RESULT (ACT : 'act -> v -> bool)
                  (STEPAn p ACT B (SNAPSHOT READY R) n) (bind m g) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMP _ _ _ _ m mv’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPA _ _ _ _ m sv’ mp_tac >>
  simp[Once STEPA_cases] >> rw[]
  >- (irule bind_Done_spec_n >> simp[STEPA_Done] >> metis_tac[])
  >- (xcf_with_def bind_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[POLL_RESULT_def, bind_NIL_running])
  >- (irule bind_Done_spec_n >> simp[STEPA_Done] >> metis_tac[])
  >- ((* Pending k: bind returns (acts, Pending k2), k2 w = bind (k w) g *)
      xcf_with_def bind_v_def >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[POLL_RESULT_def, bind_NIL_running, STEPAn_def, suspended_bind] >>
      rpt strip_tac >> simp[returns_def] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv r. &COMP p ACT A (SNAPSHOT READY R) (suspended m [w]) r’
      >- (first_x_assum drule >> rw[returns_def, GSYM COMP_eta] >> xapp) >>
      first_x_assum (qspecl_then [‘suspended m [w]’, ‘r’] mp_tac) >>
      simp[wf_suspended] >> strip_tac >> xapp)
QED

(* MAIN: bind m g implements the model's bind m g, given that m is
   well-formed and implemented by mv, and that for every result x, the
   CakeML function gv returns (for a representation of x) a value
   implementing g x.  The actions of each round, including the round in
   which m finishes and g x starts, are exactly the model's. *)
Theorem bind_spec:
  wf m ∧ COMP p ACT A (SNAPSHOT READY R) m mv ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMP p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &COMP (p:'ffi ffi_proj) (ACT : 'act -> v -> bool) B
                (SNAPSHOT READY R) (bind m g) v)
Proof
  rpt strip_tac >> irule app_COMP_of_approx >> simp[] >>
  metis_tac[bind_spec_n]
QED
