(*
  The depth-indexed specs of asyncM4Approx, replayed for the library as it
  is declared in the socket program (module Async of asyncM3Prog), plus
  both and map, declared here in the same program.

  As in asyncM3Prog: one CakeML program needs the Socket module, the
  library and the server, and the library was built on a separate
  translation chain.  The step datatype has the same constructor stamps in
  both chains (asyncM3Prog's step_stamps_agree), so STEPA/COMP and
  asyncM4Approx's STEPAd/COMPd are reused unchanged; only the CF proofs
  for the new closures are replayed, with the same proofs (names prefixed
  by Async_ / async_).
*)
Theory asyncM4SockApprox
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActBothModel
  asyncCfActProg asyncCfActSpec asyncM4Approx asyncM3Prog asyncM3Loop
  ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM3Loop"

Quote add_cakeml:
  fun async_both c1 c2 =
    case c1 of (acts1, s1) =>
    case c2 of (acts2, s2) =>
      let val acts = acts1 @ acts2 in
        case (s1, s2) of
          (Done x, Done y) => (acts, Done (x, y))
        | _ =>
          (acts, Pending (fn w =>
             case w of (rdy, t, res) =>
               let
                 val k = List.length acts1
                 val c1' = Async.poll c1 (rdy, t, List.take res k)
                 val c2' = Async.poll c2 (rdy, t, List.drop res k)
               in async_both c1' c2' end))
      end;

  fun async_map f c = Async.bind c (fn x => Async.return (f x));
End

(* Build a value made of nested constructors, e.g. ([], Done x) *)
val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

Theorem LIST_TYPE_NIL[local,simp]:
  LIST_TYPE A [] v ⇔ v = Conv (SOME (TypeStamp «[]» 1)) []
Proof
  simp[LIST_TYPE_def]
QED

(* Polling consumes one level of depth *)
Theorem Async_poll_spec_d:
  COMPd p ACT RES WORLD (SUC n) m cv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) Async_poll_v [cv; wv] emp
    (POSTv v. &COMPd p ACT RES WORLD n (suspended m [w]) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "asyncM3Prog" "Async_poll_v_def") >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ _ _’ mp_tac >> simp[STEPAd_def] >> rw[]
  >- (xmatch >> xmatch >> xcons >>
      simp[COMPd_def, POLL_RESULT_def, suspended_finished_one, STEPAd_Done] >>
      conj_tac >- simp[finished_def, LIST_TYPE_def] >> metis_tac[])
  >- (xmatch >> xmatch >> first_x_assum drule >>
      rw[returns_def, GSYM COMPd_def] >> xapp >> simp[COMPd_def])
QED

Theorem Async_skip_spec_d:
  STEPAd p ACT RES (SNAPSHOT READY (R : 'r -> v -> bool)) n g sv ∧ NUM k kv ⇒
  app (p:'ffi ffi_proj) Async_skip_v [kv; sv] emp
    (POSTv v. &STEPAd p ACT RES (SNAPSHOT READY R) n (skipping k g) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "asyncM3Prog" "Async_skip_v_def") >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ _ sv’ mp_tac >>
  Cases_on ‘n’ >> simp[STEPAd_def] >> strip_tac >> gvs[] >>
  TRY (xmatch >> xvar >> xsimpl >> simp[skipping_finished] >> metis_tac[] >>
       NO_TAC) >>
  TRY (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >> fs[] >> NO_TAC) >>
  (xmatch >> xfun ‘k2’ >> xcon >> xsimpl >>
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
Theorem Async_bind_Done_spec_d:
  STEPAd p ACT A (SNAPSHOT READY R) k m (DoneV xv) ∧
  LIST_TYPE (ACT : 'act -> v -> bool) (m []).actions av ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
  app (p:'ffi ffi_proj) Async_bind_v [Conv NONE [av; DoneV xv]; gv] emp
    (POSTv v. &COMPd p ACT B (SNAPSHOT READY R) n (bind m g) v)
Proof
  rw[STEPAd_Done] >> rename1 ‘finished As x’ >>
  gvs[finished_def] >>
  xcf_with_def (fetch "asyncM3Prog" "Async_bind_v_def") >> xmatch >> xmatch >>
  xlet ‘POSTv r. &COMPd p ACT B (SNAPSHOT READY R) n (g x) r’
  >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
  gvs[COMPd_def, POLL_RESULT_def] >> xmatch >>
  rename1 ‘LIST_TYPE ACT (g x []).actions av2’ >>
  xlet ‘POSTv nv. &NUM (LENGTH As) nv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'act”] ListProgTheory.length_v_thm) >>
      xsimpl >> metis_tac[]) >>
  xlet ‘POSTv sv2. &STEPAd p ACT B (SNAPSHOT READY R) n
                      (skipping (LENGTH As) (g x)) sv2’
  >- (xapp_spec Async_skip_spec_d >> simp[] >> metis_tac[]) >>
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
Theorem Async_bind_spec_d:
  ∀n m mv.
    wf m ∧ COMPd p ACT A (SNAPSHOT READY R) n m mv ∧
    (∀x xv. A x xv ⇒
       returns p gv [xv]
         (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
    app (p:'ffi ffi_proj) Async_bind_v [mv; gv] emp
      (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) n
                  (bind m g) v)
Proof
  Induct >> rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ m mv’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[] >>
  qpat_x_assum ‘STEPAd _ _ _ _ _ m sv’ mp_tac >>
  simp[Once STEPAd_def] >> rw[]
  >- (irule Async_bind_Done_spec_d >> simp[STEPAd_Done] >> metis_tac[])
  >- (xcf_with_def (fetch "asyncM3Prog" "Async_bind_v_def") >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
      simp[COMPd_def, POLL_RESULT_def, bind_NIL_running, STEPAd_def])
  >- (irule Async_bind_Done_spec_d >> simp[STEPAd_Done] >> metis_tac[])
  >- (xcf_with_def (fetch "asyncM3Prog" "Async_bind_v_def") >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
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
Theorem Async_bind_guarded_spec_0:
  (m []).result = NONE ∧ COMPd p ACT A (SNAPSHOT READY R) 0 m mv ⇒
  app (p:'ffi ffi_proj) Async_bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B
                (SNAPSHOT READY (R : 'r -> v -> bool)) 0 (bind m g) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ m mv’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[STEPAd_def, finished_def] >>
  xcf_with_def (fetch "asyncM3Prog" "Async_bind_v_def") >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
  simp[COMPd_def, POLL_RESULT_def, bind_NIL_running, STEPAd_def]
QED

(* MAIN (helper): a guarded bind gains one level of depth: if the first
   part has not finished in its first round, continuations up to depth n
   give bind m g up to depth n+1.  This is where recursion through a
   continuation makes progress. *)
Theorem Async_bind_guarded_spec_d:
  wf m ∧ (m []).result = NONE ∧ COMPd p ACT A (SNAPSHOT READY R) (SUC n) m mv ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) n (g x))) ⇒
  app (p:'ffi ffi_proj) Async_bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) (SUC n)
                (bind m g) v)
Proof
  rpt strip_tac >>
  qpat_x_assum ‘COMPd _ _ _ _ _ m mv’
    (strip_assume_tac o REWRITE_RULE[COMPd_def, POLL_RESULT_def]) >>
  gvs[STEPAd_def, finished_def] >>
  xcf_with_def (fetch "asyncM3Prog" "Async_bind_v_def") >> xmatch >> xmatch >> xfun ‘k2’ >> xcons >>
  simp[COMPd_def, POLL_RESULT_def, bind_NIL_running, STEPAd_def,
       suspended_bind] >>
  rpt strip_tac >> simp[returns_def] >>
  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv r. &COMPd p ACT A (SNAPSHOT READY R) n (suspended m [w]) r’
  >- (first_x_assum drule >> rw[returns_def, GSYM COMPd_def] >> xapp) >>
  ‘app p Async_bind_v [r; gv] emp
     (POSTv v. &COMPd p ACT B (SNAPSHOT READY R) n (bind (suspended m [w]) g) v)’
    by (irule Async_bind_spec_d >> simp[wf_suspended] >> metis_tac[]) >>
  gvs[COMPd_def] >> qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
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
  xcf_with_def (fetch "-" "async_both_v_def") >> xmatch >> xmatch >>
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
          assume_tac (MATCH_MP Async_poll_spec_d (CONJ th1 th2)))) >>
      qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
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
          assume_tac (MATCH_MP Async_poll_spec_d (CONJ th1 th2)))) >>
      qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  first_x_assum (qspecl_then [‘suspended ^M1 [take_snap kk w]’,
                              ‘suspended ^M2 [skip_snap kk w]’, ‘c1'’, ‘c2'’]
                   mp_tac) >>
  simp[wf_suspended] >> strip_tac >> xapp)) g
  end;

(* MAIN (helper): both up to depth n.  If both sides are implemented up to
   depth n, so is both m1 m2. *)
Theorem async_both_spec_d:
  ∀n m1 m2 c1 c2.
    wf m1 ∧ wf m2 ∧
    COMPd p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) n m1 c1 ∧
    COMPd p ACT B (SNAPSHOT READY R) n m2 c2 ⇒
    app (p:'ffi ffi_proj) async_both_v [c1; c2] emp
      (POSTv v. &COMPd p (ACT : 'act -> v -> bool) (PAIR_TYPE A B)
                  (SNAPSHOT READY R) n (both m1 m2) v)
Proof
  Induct
  >- (both_prelude >> FIRST [both_done_tac, both_pending_tac false])
  >- (both_prelude >> FIRST [both_done_tac, both_pending_tac true])
QED

(* map f c implements the model's map f m, up to any depth n *)
Theorem async_map_spec_d:
  wf m ∧ COMPd p ACT A (SNAPSHOT READY R) n m mv ∧
  (∀x xv. A x xv ⇒ returns p fv [xv] (B (f x))) ⇒
  app (p:'ffi ffi_proj) async_map_v [fv; mv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B
                (SNAPSHOT READY (R : 'r -> v -> bool)) n (map f m) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "async_map_v_def") >> xfun ‘g’ >>
  ‘∀x xv. A x xv ⇒
     returns p g [xv] (COMPd p ACT B (SNAPSHOT READY R) n (return (f x)))’
    by (rpt strip_tac >> simp[returns_def] >>
        qpat_x_assum ‘curried _ _ g ∧ _’ (irule o CONJUNCT2) >>
        xlet ‘POSTv yv. &B (f x) yv’
        >- (first_x_assum drule >> rw[returns_def] >> xapp) >>
        ‘app p Async_return_v [yv] emp
           (POSTv v. &COMP p ACT B (SNAPSHOT READY R) (return (f x)) v)’
          by (irule Async_return_spec >> simp[]) >>
        qpat_x_assum ‘app _ Async_return_v _ _ _’ xapp_spec >> xsimpl >>
        simp[COMP_IMP_COMPd]) >>
  ‘app p Async_bind_v [mv; g] emp
     (POSTv v. &COMPd p ACT B (SNAPSHOT READY R) n
                 (bind m (λx. return (f x))) v)’
    by (irule Async_bind_spec_d >> simp[] >> metis_tac[]) >>
  simp[map_as_bind] >> qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED
