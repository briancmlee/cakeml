(*
  Smoke test for the shared-base build recipe: opens the CF libraries and
  the basis program from the base checkout and proves a trivial spec.
*)
Theory smoke
Ancestors
  ml_translator basisProg[qualified]
Libs
  preamble ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "basisProg"

Quote add_cakeml:
  fun smoke_id x = x
End

Theorem smoke_id_spec:
  !xv. app (p:'ffi ffi_proj) smoke_id_v [xv]
         emp (POSTv v. &(v = xv))
Proof
  strip_tac \\ xcf_with_def (fetch "-" "smoke_id_v_def") \\ xret \\ xsimpl
QED
