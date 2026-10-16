(*
  Pure subterms through the standard translator: a variant of the echo
  server that answers each chunk d with d followed by "!", but only for
  chunks of fewer than 100 bytes (longer ones are dropped).  d ++ "!" and
  LENGTH d < 100 are not constructors over variables: the translator lifts
  each to an auxiliary definition, translates it (ml_translatorLib), calls
  it from the generated code, and proves the call with the translator's
  certificate (xapp).
*)
Theory asyncTranslatePure
Ancestors
  asyncCore asyncLevel1 asyncServer asyncCfActModel asyncCfActProg
  asyncCfActSpec asyncCfActBoth asyncM4Approx asyncM4ServerProg
  asyncTranslate asyncTranslateEcho ml_translator ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib
  asyncTranslateLib

val _ = translation_extends "asyncTranslateEcho"

Overload ACTION = “ASYNCSERVER_ACTION_TYPE”
Overload SNAP = “SNAPSHOT EVENTS ASYNCSERVER_RESPONSE_TYPE”

val prims : prim list = [
  {const = “asyncLevel1$return”, name = "return", spec = return_spec,
   guard = NONE, wf = wf_return},
  {const = “asyncLevel1$emit”, name = "emit", spec = emit_spec,
   guard = SOME emit_needs_snapshot, wf = wf_emit},
  {const = “asyncServer$readable”, name = "readable", spec = readable_spec,
   guard = SOME readable_NIL, wf = wf_readable}]

val wfs = [wf_return, wf_emit, wf_readable, wf_bind, wf_map, wf_both]
val guards = [readable_NIL, emit_needs_snapshot]

val bang = define_async "bang" 0
  ‘bang fd =
     bind (readable fd) (λu.
     bind (emit (Read fd)) (λres.
       case res of
         Data d =>
           if LENGTH d < 100
           then bind (emit (Write fd (d ++ "!"))) (λw. bang fd)
           else bang fd
       | Eof => return ()
       | _ => bang fd))’ guards wfs

val bang_g = translate_async {
  name = "bang_g", unfold = #unfold bang, prims = prims,
  wfs = #wf bang :: wfs, act = “ACTION”, snap = “SNAP”, guard = NONE,
  vocab = echo_vocab, pre = [], defs = []}
