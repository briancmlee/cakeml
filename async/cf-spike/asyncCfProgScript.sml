(*
  CF feasibility spike, Option A: futures as residuals, no refs.

  A CakeML computation is a value of the CakeML datatype
      datatype ('w, 'a) step = Done 'a | Pending ('w -> ('w, 'a) step)
  Polling a Pending k with a snapshot w calls k w, which returns the
  residual computation.  return, wait, bind and poll are plain CakeML
  functions with no refs.

  We relate these values to the HOL model of asyncCfModelScript.sml by a
  coinductive representation predicate STEP, and prove CF specs for all
  four functions.  See async/design/02-cf-feasibility.md.
*)
Theory asyncCfProg
Ancestors
  asyncCfModel asyncCfDet ml_translator basisProg[qualified]
Libs
  preamble ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "basisProg"

(* ------------------------------------------------------------------------
   The CakeML implementation
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  datatype ('w, 'a) step = Done 'a | Pending ('w -> ('w, 'a) step)
End

(* The constructor stamps of Done and Pending, read off the program state *)
local
  val env = get_env (get_ml_prog_state ())
  fun stamp_of c =
    EVAL “nsLookup (^env).c (Short ^c)” |> concl |> rhs
    |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
in
  val done_stamp = stamp_of “«Done»”
  val pending_stamp = stamp_of “«Pending»”
end

(* DoneV xv is the CakeML value Done xv; PendingV kv is Pending kv *)
Overload DoneV = “λxv. Conv (SOME ^done_stamp) [xv]”
Overload PendingV = “λkv. Conv (SOME ^pending_stamp) [kv]”

Quote add_cakeml:
  fun return x = Done x;

  fun poll s w = case s of Done x => s | Pending k => k w;

  fun wait p =
    Pending (fn w => case p w of Some a => Done a | None => wait p);

  fun bind m f =
    case m of
      Done x => f x
    | Pending k => Pending (fn w => bind (k w) f);
End

(* ------------------------------------------------------------------------
   The representation predicate
   ------------------------------------------------------------------------ *)

(* returns p f args R: calling closure f on args terminates normally (no
   exception) with a value satisfying R.  The precondition is the empty
   heap and the postcondition keeps no heap, so f is effectively pure: this
   spike does not cover closures that use refs or I/O. *)
Definition returns_def:
  returns (p:'ffi ffi_proj) f args R ⇔ app p f args emp (POSTv v. &R v)
End

(* returns is monotone in R: this is what makes STEP below well defined. *)
Theorem returns_mono[mono]:
  (∀v. R1 v ⇒ R2 v) ⇒ returns p f args R1 ⇒ returns p f args R2
Proof
  rw[returns_def] >> irule app_weaken >> first_x_assum (irule_at Any) >>
  rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def,
     POSTv_cond] >>
  metis_tac[]
QED

(* STEP p A WORLD m v: the CakeML value v implements the model computation m.
   A relates results to CakeML values, WORLD relates snapshots to values.
   - Done xv implements m if m has finished with some x that xv represents;
   - Pending kv implements m if m has not finished yet, and for every
     snapshot w (represented by wv), calling kv on wv returns a value that
     implements m after w.
   Coinductive, because a computation may stay pending forever. *)
CoInductive STEP:
  (∀m x xv. finished m x ∧ A x xv ⇒ STEP p A WORLD m (DoneV xv)) ∧
  (∀m kv. m [] = NONE ∧
        (∀w wv. WORLD w wv ⇒ returns p kv [wv] (STEP p A WORLD (after w m))) ⇒
        STEP p A WORLD m (PendingV kv))
End

(* ------------------------------------------------------------------------
   Proof technique: finite approximations of STEP

   Recursive code (wait, bind) creates new closures on every poll, whose
   specs mention STEP again.  We prove "n polls deep" approximations by
   induction on n, then pass to the limit.
   ------------------------------------------------------------------------ *)

(* STEPn n: STEP observed for at most n polls. *)
Definition STEPn_def:
  (STEPn p A WORLD 0 m v ⇔ T) ∧
  (STEPn p A WORLD (SUC n) m v ⇔
     (∃x xv. finished m x ∧ A x xv ∧ v = DoneV xv) ∨
     (∃kv. m [] = NONE ∧ v = PendingV kv ∧
           ∀w wv. WORLD w wv ⇒ returns p kv [wv] (STEPn p A WORLD n (after w m))))
End

Theorem returns_forall:
  ∀p f x P.
    (∀i. returns p f [x] (P i)) ⇒ returns p f [x] (λv. ∀i. P i v)
Proof
  rw[returns_def, app_def] >> irule app_basic_forall >> simp[]
QED

Theorem STEP_IMP_STEPn:
  ∀n m v. STEP p A WORLD m v ⇒ STEPn p A WORLD n m v
Proof
  Induct >> simp[STEPn_def] >>
  rpt gen_tac >> simp[Once STEP_cases] >> rw[]
  >- metis_tac[]
  >- (rpt strip_tac >> irule returns_mono >>
      qexists_tac ‘STEP p A WORLD (after w m)’ >> metis_tac[])
QED

(* The limit: a value that satisfies every approximation satisfies STEP. *)
Theorem STEPn_0:
  STEPn p A WORLD 0 m v
Proof
  simp[STEPn_def]
QED

Theorem STEPn_IMP_STEP:
  (∀n. STEPn p A WORLD n m v) ⇒ STEP p A WORLD m v
Proof
  strip_tac >> irule STEP_coind >>
  qexists_tac ‘λm v. ∀n. STEPn p A WORLD n m v’ >> simp[] >>
  rpt strip_tac >>
  first_assum (qspec_then ‘SUC 0’ mp_tac) >>
  simp_tac std_ss [STEPn_def] >> strip_tac >> gvs[]
  >- metis_tac[]
  >- (rpt strip_tac >>
      ‘∀n. returns p kv [wv] (STEPn p A WORLD n (after w a0))’
        by (gen_tac >>
            qpat_x_assum ‘∀n. STEPn _ _ _ n a0 _’ (qspec_then ‘SUC n’ mp_tac) >>
            simp[STEPn_def] >> metis_tac[]) >>
      qspecl_then [‘p’, ‘kv’, ‘wv’, ‘λn. STEPn p A WORLD n (after w a0)’]
        mp_tac returns_forall >> simp[])
QED

(* ------------------------------------------------------------------------
   CF specs
   ------------------------------------------------------------------------ *)

(* MAIN: return x builds a finished computation. *)
Theorem return_spec:
  A x xv ⇒
  app (p:'ffi ffi_proj) return_v [xv] emp
    (POSTv v. &STEP p A WORLD (mret x) v)
Proof
  strip_tac >> xcf_with_def (fetch "-" "return_v_def") >>
  xcon >> xsimpl >>
  simp[Once STEP_cases] >> metis_tac[finished_mret]
QED

(* MAIN: polling a computation with snapshot w returns its residual,
   which implements the model computation after w. *)
Theorem poll_spec:
  STEP p A WORLD m sv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll_v [sv; wv] emp
    (POSTv v. &STEP p A WORLD (after w m) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "poll_v_def") >>
  qpat_x_assum ‘STEP _ _ _ _ _’ mp_tac >>
  simp[Once STEP_cases] >> rw[]
  >- (xmatch >> xvar >> xsimpl >>
      simp[Once STEP_cases] >> metis_tac[finished_after])
  >- (xmatch >> gvs[returns_def] >> xapp >> simp[])
QED

(* Finite approximation of wait's spec, by induction on n. *)
Theorem wait_spec_n:
  ∀n p f fv.
    (∀w wv. WORLD w wv ⇒ returns p fv [wv] (OPTION_TYPE A (f w))) ⇒
    app (p:'ffi ffi_proj) wait_v [fv] emp
      (POSTv v. &STEPn p A WORLD n (mwait f) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "wait_v_def") >>
  xfun ‘k’ >> xcon >> xsimpl >> simp[STEPn_def, mwait_NIL] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv ov. &OPTION_TYPE A (f w) ov’
  >- (qpat_x_assum ‘∀w wv. WORLD w wv ⇒ _’ (drule_then assume_tac) >>
      gvs[returns_def] >> qpat_x_assum ‘app _ fv _ _ _’ xapp_spec >> xsimpl) >>
  Cases_on ‘f w’ >> gvs[std_preludeTheory.OPTION_TYPE_def] >> xmatch
  >- (last_x_assum (qspecl_then [‘p’, ‘f’, ‘fv’] mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      xapp >> xsimpl >> simp[after_mwait_NONE])
  >- (xcon >> xsimpl >> Cases_on ‘n’ >> simp[STEPn_def] >>
      metis_tac[after_mwait_SOME])
QED

(* MAIN: wait f is a computation that finishes at the first polled
   snapshot w with f w = SOME a, with result a.  f may be any CakeML
   function that implements the HOL function f. *)
Theorem wait_spec:
  (∀w wv. WORLD w wv ⇒ returns p fv [wv] (OPTION_TYPE A (f w))) ⇒
  app (p:'ffi ffi_proj) wait_v [fv] emp
    (POSTv v. &STEP p A WORLD (mwait f) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "wait_v_def") >>
  xfun ‘k’ >> xcon >> xsimpl >>
  (* the closure k stored in Pending: prove every approximation of STEP *)
  irule STEPn_IMP_STEP >> qx_gen_tac ‘j’ >> Cases_on ‘j’ >>
  simp[STEPn_def, mwait_NIL] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv ov. &OPTION_TYPE A (f w) ov’
  >- (qpat_x_assum ‘∀w wv. WORLD w wv ⇒ _’ (drule_then assume_tac) >>
      gvs[returns_def] >> qpat_x_assum ‘app _ fv _ _ _’ xapp_spec >> xsimpl) >>
  Cases_on ‘f w’ >> gvs[std_preludeTheory.OPTION_TYPE_def] >> xmatch
  >- ((* the recursive call wait p: use the n-th approximation *)
      qspecl_then [‘n’, ‘p’, ‘f’, ‘fv’] mp_tac wait_spec_n >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      xapp >> xsimpl >> simp[after_mwait_NONE])
  >- (xcon >> xsimpl >> Cases_on ‘n’ >> simp[STEPn_def] >>
      metis_tac[after_mwait_SOME])
QED

(* Finite approximation of bind's spec, by induction on n. *)
Theorem bind_spec_n:
  ∀n p m mv g gv.
    STEP p A WORLD m mv ∧
    (∀x xv. A x xv ⇒ returns p gv [xv] (STEP p B WORLD (g x))) ⇒
    app (p:'ffi ffi_proj) bind_v [mv; gv] emp
      (POSTv v. &STEPn p B WORLD n (mbind m g) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "bind_v_def") >>
  qpat_x_assum ‘STEP _ _ _ m mv’ mp_tac >> simp[Once STEP_cases] >> rw[]
  >- ((* Done x: bind is the continuation g x *)
      qpat_x_assum ‘∀x xv. A x xv ⇒ _’ (drule_then assume_tac) >>
      gvs[returns_def] >> xmatch >>
      qpat_x_assum ‘app _ gv _ _ _’ xapp_spec >> xsimpl >>
      metis_tac[STEP_IMP_STEPn, STEPn_0, mbind_finished])
  >- (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >> simp[STEPn_def])
  >- ((* Done x: bind is the continuation g x *)
      qpat_x_assum ‘∀x xv. A x xv ⇒ _’ (drule_then assume_tac) >>
      gvs[returns_def] >> xmatch >>
      qpat_x_assum ‘app _ gv _ _ _’ xapp_spec >> xsimpl >>
      metis_tac[STEP_IMP_STEPn, STEPn_0, mbind_finished])
  >- ((* Pending k: bind returns Pending k2, where k2 w = bind (k w) g *)
      xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      simp[STEPn_def, mbind_NIL_pending] >>
      rpt strip_tac >> simp[returns_def] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv r. &STEP p A WORLD (after w m) r’
      >- (qpat_x_assum ‘∀w wv. WORLD w wv ⇒ returns _ _ _ (STEP _ _ _ _)’
            (drule_then assume_tac) >>
          gvs[returns_def] >> qpat_x_assum ‘app _ kv _ _ _’ xapp_spec >> xsimpl) >>
      last_x_assum (qspecl_then [‘p’, ‘after w m’, ‘r’, ‘g’, ‘gv’] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      xapp >> xsimpl >> simp[after_mbind_pending])
QED

(* MAIN: bind m g implements the model's bind, given that m is implemented
   by mv and that, for every result x, g x is implemented by what the
   CakeML function gv returns on (a representation of) x. *)
Theorem bind_spec:
  STEP p A WORLD m mv ∧
  (∀x xv. A x xv ⇒ returns p gv [xv] (STEP p B WORLD (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &STEP p B WORLD (mbind m g) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "bind_v_def") >>
  qpat_x_assum ‘STEP _ _ _ m mv’ mp_tac >> simp[Once STEP_cases] >> rw[]
  >- ((* Done x: bind is the continuation g x *)
      qpat_x_assum ‘∀x xv. A x xv ⇒ _’ (drule_then assume_tac) >>
      gvs[returns_def] >> xmatch >>
      qpat_x_assum ‘app _ gv _ _ _’ xapp_spec >> xsimpl >>
      metis_tac[mbind_finished])
  >- ((* Pending k: bind returns Pending k2, where k2 w = bind (k w) g *)
      xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
      irule STEPn_IMP_STEP >> qx_gen_tac ‘j’ >> Cases_on ‘j’ >>
      simp[STEPn_def, mbind_NIL_pending] >>
      rpt strip_tac >> simp[returns_def] >>
      qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv r. &STEP p A WORLD (after w m) r’
      >- (qpat_x_assum ‘∀w wv. WORLD w wv ⇒ returns _ _ _ (STEP _ _ _ _)’
            (drule_then assume_tac) >>
          gvs[returns_def] >> qpat_x_assum ‘app _ kv _ _ _’ xapp_spec >> xsimpl) >>
      (* the recursive call bind (k w) g: use the n-th approximation *)
      qspecl_then [‘n’, ‘p’, ‘after w m’, ‘r’, ‘g’, ‘gv’] mp_tac bind_spec_n >>
      impl_tac >- metis_tac[] >> strip_tac >>
      xapp >> xsimpl >> simp[after_mbind_pending])
QED

(* MAIN: binding a finished computation adds no wrapper: bind (Done x) g
   is exactly g x, whatever g does (any pre/postcondition).  So once a
   computation finishes, the residual of a bind chain is just the
   continuation's residual, and finished binds do not accumulate. *)
Theorem bind_Done_spec:
  app (p:'ffi ffi_proj) gv [xv] H Q ⇒
  app p bind_v [DoneV xv; gv] H Q
Proof
  strip_tac >> xcf_with_def (fetch "-" "bind_v_def") >>
  xmatch >> qpat_x_assum ‘app _ gv _ _ _’ xapp_spec >> xsimpl
QED
