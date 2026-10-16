(*
  both in the actions/responses CF layer: two computations side by side.

      both (acts1, s1) (acts2, s2)
        = (acts1 @ acts2, Done (x, y))          if s1 = Done x, s2 = Done y
        = (acts1 @ acts2, Pending k)            otherwise, where k w polls
          each side with its share of w's responses (the left side gets the
          first LENGTH acts1) and continues with both.

  This is the model's both (async/model), with its positional routing
  (par_views) reduced, for one snapshot, to TAKE/DROP at LENGTH acts1
  (libBothModel).
*)
Theory libBoth
Ancestors
  asyncCore asyncLevel1 asyncChoose libModel libBothModel
  libProg libSpec ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "libProg"

Quote add_cakeml:
  fun both c1 c2 =
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
                 val c1' = poll c1 (rdy, t, List.take res k)
                 val c2' = poll c2 (rdy, t, List.drop res k)
               in both c1' c2' end))
      end;
End

val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

(* The common start of both cases of both_spec_n: take the two pairs apart,
   compute acts1 @ acts2, and split on whether each side is Done. *)
val both_prelude =
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ m1 _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  qpat_assum ‘COMP _ _ _ _ m2 _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >>
  xcf_with_def (fetch "-" "both_v_def") >> xmatch >> xmatch >>
  xlet ‘POSTv av. &LIST_TYPE ACT ((m1 []).actions ++ (m2 []).actions) av’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  qpat_x_assum ‘STEPA _ _ _ _ m1 _’ mp_tac >> simp[Once STEPA_cases] >>
  qpat_x_assum ‘STEPA _ _ _ _ m2 _’ mp_tac >> simp[Once STEPA_cases] >>
  rw[] >>
  (xlet_auto >- (xcon >> xsimpl));

(* Both sides Done: both returns (acts, Done (x, y)) *)
val both_done_tac =
  qmatch_goalsub_rename_tac ‘both (finished A1 x1) (finished A2 x2)’ >>
  xmatch >> xcons >>
  simp[POLL_RESULT_def, both_finished_finished] >>
  gvs[finished_def] >>
  simp[STEPAn_def] >> irule_at Any EQ_REFL >> simp[PAIR_TYPE_def];

(* Otherwise: both returns (acts, Pending k).  The closure k polls each
   side with its share of the responses, and continues with both (by the
   induction hypothesis, when there is one).  The two sides M1 and M2 are
   read off the goal (rw may have replaced m1 or m2 by finished A x). *)
fun both_sides w =
  let
    val t = find_term (fn t => (same_const (rator (rator t)) “both”
                                handle HOL_ERR _ => false)) w
  in (rand (rator t), rand t) end;

fun both_pending_tac (n_is_suc : bool) (g as (_, w)) =
  let val (M1, M2) = both_sides w in
  (xmatch >> xfun ‘k’ >> xcons >>
  simp[POLL_RESULT_def, both_NIL_poll] >>
  (if not n_is_suc then ALL_TAC else
  simp[STEPAn_def, suspended_both] >>
  conj_tac >- simp[both_NIL_poll, finished_def] >>
  rpt strip_tac >> simp[returns_def] >>
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
  xlet ‘POSTv c1'. &COMP p ACT A (SNAPSHOT READY R)
                        (suspended ^M1 [take_snap kk w]) c1'’
  >- (‘SNAPSHOT READY R (take_snap kk w) w1’
        by simp[SNAPSHOT_def, take_snap_def] >>
      qpat_assum ‘COMP _ _ A _ _ _’ (fn th1 =>
        qpat_assum ‘SNAPSHOT _ _ (take_snap _ _) _’ (fn th2 =>
          assume_tac (MATCH_MP poll_spec (CONJ th1 th2)))) >>
      qpat_x_assum ‘app _ poll_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv dv. &LIST_TYPE R (DROP kk w.results) dv’
  >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.drop_v_thm) >>
      xsimpl >> simp[mllistTheory.drop_def] >> metis_tac[]) >>
  xlet ‘POSTv w2. &(w2 = Conv NONE [rv; nv; dv])’ >- (xcon >> xsimpl) >>
  xlet ‘POSTv c2'. &COMP p ACT B (SNAPSHOT READY R)
                        (suspended ^M2 [skip_snap kk w]) c2'’
  >- (‘SNAPSHOT READY R (skip_snap kk w) w2’
        by simp[SNAPSHOT_def, skip_snap_def] >>
      qpat_assum ‘COMP _ _ B _ _ _’ (fn th1 =>
        qpat_assum ‘SNAPSHOT _ _ (skip_snap _ _) _’ (fn th2 =>
          assume_tac (MATCH_MP poll_spec (CONJ th1 th2)))) >>
      qpat_x_assum ‘app _ poll_v _ _ _’ xapp_spec >> xsimpl) >>
  first_x_assum (qspecl_then [‘suspended ^M1 [take_snap kk w]’,
                              ‘suspended ^M2 [skip_snap kk w]’, ‘c1'’, ‘c2'’]
                   mp_tac) >>
  simp[wf_suspended] >> strip_tac >> xapp)) g
  end;

Theorem both_spec_n:
  ∀n m1 m2 c1 c2.
    wf m1 ∧ wf m2 ∧
    COMP p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) m1 c1 ∧
    COMP p ACT B (SNAPSHOT READY R) m2 c2 ⇒
    app (p:'ffi ffi_proj) both_v [c1; c2] emp
      (POSTv v. &POLL_RESULT (ACT : 'act -> v -> bool)
                  (STEPAn p ACT (PAIR_TYPE A B) (SNAPSHOT READY R) n)
                  (both m1 m2) v)
Proof
  Induct
  >- (both_prelude >> FIRST [both_done_tac, both_pending_tac false])
  >- (both_prelude >> FIRST [both_done_tac, both_pending_tac true])
QED

(* MAIN: both c1 c2 implements the model's both m1 m2: in each round it
   emits the left side's actions then the right side's, routes each side its
   own responses, and finishes with the pair of results once both have
   finished.  Needs both sides well-formed. *)
Theorem both_spec:
  wf m1 ∧ wf m2 ∧
  COMP p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) m1 c1 ∧
  COMP p ACT B (SNAPSHOT READY R) m2 c2 ⇒
  app (p:'ffi ffi_proj) both_v [c1; c2] emp
    (POSTv v. &COMP p (ACT : 'act -> v -> bool) (PAIR_TYPE A B)
                (SNAPSHOT READY R) (both m1 m2) v)
Proof
  rpt strip_tac >> irule app_COMP_of_approx >> simp[] >>
  metis_tac[both_spec_n]
QED
