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
