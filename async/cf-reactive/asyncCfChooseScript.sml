(*
  choose in the actions/responses CF layer: race two computations, and
  return the winner's result together with the loser, still running.

      choose (acts1, s1) (acts2, s2) =
        s1 = Done x            : (acts1, Done (Inl (x, (acts2, s2))))
                                  m1 wins at once; m2 is not polled, so
                                  its actions acts2 are not emitted: the
                                  loser value still carries them.
        s2 = Done y, acts1 = []: (acts2, Done (Inr ((acts1, s1), y)))
        s2 = Done y, acts1 ≠ []: (acts1 @ acts2, Pending k), where k w
                                  returns ([], Done (Inr (poll c1 w1, y))):
                                  wait one round for the responses to
                                  acts1, deliver them to the loser.
        otherwise              : (acts1 @ acts2, Pending k), where k w
                                  polls both sides with their shares of
                                  w and continues with choose.

  The loser is an ordinary computation value (a pair), so the result
  relation of choose holds COMP for it.  This is the model's choose
  (async/model/asyncChooseScript.sml), via the one-poll lemmas of
  asyncCfChooseModel.
*)
Theory asyncCfChoose
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActBothModel
  asyncCfChooseModel asyncCfActProg asyncCfActSpec ml_translator ListProg
  std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfActProg"

Quote add_cakeml:
  fun choose c1 c2 =
    case c1 of (acts1, s1) =>
    case c2 of (acts2, s2) =>
    let val acts = acts1 @ acts2 in
      case s1 of
        Done x => (acts1, Done (Inl (x, c2)))
      | Pending k1 =>
        (case s2 of
           Done y =>
             (case acts1 of
                [] => (acts2, Done (Inr (c1, y)))
              | a :: rest =>
                  (acts, Pending (fn w =>
                     case w of (rdy, t, res) =>
                       let
                         val k = List.length acts1
                         val c1' = poll c1 (rdy, t, List.take res k)
                       in ([], Done (Inr (c1', y))) end)))
         | Pending k2 =>
             (acts, Pending (fn w =>
                case w of (rdy, t, res) =>
                  let
                    val k = List.length acts1
                    val c1' = poll c1 (rdy, t, List.take res k)
                    val c2' = poll c2 (rdy, t, List.drop res k)
                  in choose c1' c2' end)))
    end;
End

val xcons = rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl;

(* The result of choose: the winner's result with the loser, which is a
   computation value implementing the model's loser. *)
Definition CHOOSE_RES_def:
  CHOOSE_RES p ACT A B WORLD =
    SUM_TYPE (PAIR_TYPE A (COMP p ACT B WORLD))
             (PAIR_TYPE (COMP p ACT A WORLD) B)
End

(* A finished computation satisfies every approximation, given its result *)
Theorem STEPAn_finished[local]:
  RES x xv ⇒ STEPAn p ACT RES WORLD n (finished A x) (DoneV xv)
Proof
  Cases_on ‘n’ >> simp[STEPAn_def] >> metis_tac[]
QED

(* The common start: take the two pairs apart and split on whether each
   side is Done. *)
val choose_prelude =
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ A _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  qpat_assum ‘COMP _ _ B _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >>
  xcf_with_def (fetch "-" "choose_v_def") >> xmatch >> xmatch >>
  xlet ‘POSTv av. &LIST_TYPE ACT ((m1 []).actions ++ (m2 []).actions) av’
  >- (xapp >> xsimpl >> metis_tac[]) >>
  qpat_x_assum ‘STEPA _ _ A _ _ _’ mp_tac >> simp[Once STEPA_cases] >>
  qpat_x_assum ‘STEPA _ _ B _ _ _’ mp_tac >> simp[Once STEPA_cases] >>
  rw[];

(* Reduce a call of the closure k (from xfun) to its body; the closure's
   spec is either still a conjunction with `curried`, or already split. *)
val use_closure_spec =
  qpat_x_assum ‘curried _ _ k ∧ _’ (irule o CONJUNCT2) ORELSE
  qpat_x_assum ‘∀H Q h. _ ⇒ app _ k _ H Q’ irule;

(* The two sides, read off the goal's  choose M1 M2 *)
fun choose_sides w =
  let
    val t = find_term (fn t => (same_const (rator (rator t)) “choose”
                                handle HOL_ERR _ => false)) w
  in (rand (rator t), rand t) end;

fun is_finished t =
  same_const (fst (strip_comb t)) “finished” handle HOL_ERR _ => false;

(* m1 Done: choose returns (acts1, Done (Inl (x, c2))) *)
val left_done_tac =
  xmatch >> xcons >>
  gvs[POLL_RESULT_def, choose_finished_left, finished_def] >>
  irule STEPAn_finished >>
  simp[CHOOSE_RES_def, SUM_TYPE_def, PAIR_TYPE_def];

(* m1 Pending, m2 Done *)
fun right_done_tac (n_is_suc : bool) (g as (_, w)) =
  let val (M1, M2) = choose_sides w in
  (xmatch >> xmatch >>
   Cases_on ‘(^M1 []).actions’ >> gvs[LIST_TYPE_def] >> xmatch
   >- ((* m1 emitted nothing: m2 wins at once *)
       xcons >>
       gvs[POLL_RESULT_def, choose_finished_right_quiet, finished_def] >>
       irule STEPAn_finished >>
       simp[CHOOSE_RES_def, SUM_TYPE_def, PAIR_TYPE_def])
   >- ((* m1 has requests in flight: wait one round for their responses *)
       xfun ‘k’ >> xcons >>
       gvs[POLL_RESULT_def, choose_finished_right_waits, finished_def,
           LIST_TYPE_def] >>
       (if not n_is_suc then ALL_TAC else
        simp[STEPAn_def, choose_finished_right_waits, finished_def] >>
       rpt strip_tac >> simp[returns_def] >>
       use_closure_spec >>
       gvs[SNAPSHOT_def] >> xmatch >>
       xlet ‘POSTv kv. &NUM (LENGTH (^M1 []).actions) kv’
       >- (xapp_spec (INST_TYPE [alpha |-> “:'act”]
                        ListProgTheory.length_v_thm) >>
           xsimpl >>
           ‘LIST_TYPE ACT (h::t) (Conv (SOME (TypeStamp «::» 1)) [v2_1; v2_2])’
             by simp[LIST_TYPE_def] >>
           metis_tac[]) >>
        xlet ‘POSTv tv. &LIST_TYPE R
                (TAKE (LENGTH (^M1 []).actions) w.results) tv’
        >- (xapp_spec (INST_TYPE [alpha |-> “:'r”] ListProgTheory.take_v_thm) >>
            xsimpl >> simp[mllistTheory.take_def] >>
            qexistsl [‘LENGTH (^M1 []).actions’, ‘w.results’, ‘R’] >> simp[]) >>
        xlet ‘POSTv w1. &(w1 = Conv NONE [rv; nv; tv])’ >- (xcon >> xsimpl) >>
        xlet ‘POSTv c1'. &COMP p ACT A (SNAPSHOT READY R)
               (suspended ^M1 [take_snap (LENGTH (^M1 []).actions) w]) c1'’
        >- (‘SNAPSHOT READY R (take_snap (LENGTH (^M1 []).actions) w) w1’
              by gvs[SNAPSHOT_def, take_snap_def] >>
            qpat_assum ‘COMP _ _ A _ _ _’ (fn th1 =>
              qpat_assum ‘SNAPSHOT _ _ (take_snap _ _) _’ (fn th2 =>
                assume_tac (MATCH_MP poll_spec (CONJ th1 th2)))) >>
            qpat_x_assum ‘app _ poll_v _ _ _’ xapp_spec >> xsimpl) >>
        xcons >> simp[POLL_RESULT_def] >>
        conj_tac >- simp[finished_def, LIST_TYPE_def] >>
        irule STEPAn_finished >>
        gvs[CHOOSE_RES_def, SUM_TYPE_def, PAIR_TYPE_def]))) g
  end;

fun pending_tac (n_is_suc : bool) (g as (_, w)) =
  let val (M1, M2) = choose_sides w in
  (xmatch >> xmatch >> xfun ‘k’ >> xcons >>
  simp[POLL_RESULT_def, choose_NIL_running] >>
  (if not n_is_suc then ALL_TAC else
  simp[STEPAn_def, suspended_choose] >>
  conj_tac >- simp[choose_NIL_running] >>
  rpt strip_tac >> simp[returns_def] >>
  use_closure_spec >>
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

fun choose_case_tac n_is_suc (g as (_, w)) =
  let val (M1, M2) = choose_sides w in
    if is_finished M1 then left_done_tac g
    else if is_finished M2 then right_done_tac n_is_suc g
    else pending_tac n_is_suc g
  end;

Theorem choose_spec_n:
  ∀n m1 m2 c1 c2.
    wf m1 ∧ wf m2 ∧
    COMP p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) m1 c1 ∧
    COMP p ACT B (SNAPSHOT READY R) m2 c2 ⇒
    app (p:'ffi ffi_proj) choose_v [c1; c2] emp
      (POSTv v. &POLL_RESULT (ACT : 'act -> v -> bool)
                  (STEPAn p ACT (CHOOSE_RES p ACT A B (SNAPSHOT READY R))
                     (SNAPSHOT READY R) n)
                  (choose m1 m2) v)
Proof
  Induct
  >- (choose_prelude >> choose_case_tac false)
  >- (choose_prelude >> choose_case_tac true)
QED

(* MAIN: choose c1 c2 implements the model's choose m1 m2 (Async-style:
   the result is the winner's result with the loser still running, as a
   computation value implementing the model's loser; ties go left; if the
   right side wins while the left has requests in flight, choose waits one
   round so that the loser gets their responses).  Needs both sides
   well-formed. *)
Theorem choose_spec:
  wf m1 ∧ wf m2 ∧
  COMP p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) m1 c1 ∧
  COMP p ACT B (SNAPSHOT READY R) m2 c2 ⇒
  app (p:'ffi ffi_proj) choose_v [c1; c2] emp
    (POSTv v. &COMP p (ACT : 'act -> v -> bool)
                (CHOOSE_RES p ACT A B (SNAPSHOT READY R))
                (SNAPSHOT READY R) (choose m1 m2) v)
Proof
  rpt strip_tac >> irule app_COMP_of_approx >> simp[] >>
  metis_tac[choose_spec_n]
QED
