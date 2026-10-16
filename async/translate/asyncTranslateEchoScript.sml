(*
  The echo prototype of the async translator: the concurrent echo
  server's CakeML code and CF theorems, generated from the model
  (async/model/asyncServerScript.sml) by asyncTranslateLib, with no
  hand-written CakeML and no hand-written proof.

     handler_g_spec : NUM fd fdv ⇒
       app p handler_g_v [fdv] emp
         (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (handler fd) v)
     server_g_spec  : NUM lfd lfdv ⇒
       app p server_g_v [lfdv] emp
         (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (server lfd) v)

  These are the statements of the hand-written handler_spec / server_spec
  (m4-server/asyncM4ServerSpecScript.sml).  Second part: the same server
  written once, as recursive equations; define_async makes the model
  (echo_unfold, wf_echo, ...) and translate_async the code and
  echo_g_spec / echo_server_g_spec; echo_is_handler checks the model.  The library (bind, emit,
  return, readable, map, both) and the registered datatypes come from
  asyncM4ServerProg.
*)
Theory asyncTranslateEcho
Ancestors
  asyncCore asyncLevel1 asyncServer asyncCfActModel asyncCfActProg
  asyncCfActSpec asyncCfActBoth asyncM4Approx asyncM4ServerProg
  asyncTranslate ml_translator
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib
  asyncTranslateLib

val _ = translation_extends "asyncM4ServerProg"

Overload ACTION = “ASYNCSERVER_ACTION_TYPE”
Overload SNAP = “SNAPSHOT EVENTS ASYNCSERVER_RESPONSE_TYPE”

(* The primitives: model constant, CakeML name, spec, guard, wf *)
val prims : prim list = [
  {const = “asyncLevel1$return”, name = "return", spec = return_spec,
   guard = NONE, wf = wf_return},
  {const = “asyncLevel1$emit”, name = "emit", spec = emit_spec,
   guard = SOME emit_needs_snapshot, wf = wf_emit},
  {const = “asyncServer$readable”, name = "readable", spec = readable_spec,
   guard = SOME readable_NIL, wf = wf_readable}]

val wfs = [wf_return, wf_emit, wf_readable, wf_bind, wf_map, wf_both,
           wf_handler, wf_server]

(* The model, as written once: handler_body's equation *)
val handler_eq = REWRITE_RULE [handler_body_def] handler_unfold |> BETA_RULE

val handler_g = translate_async {
  name = "handler_g", unfold = GEN_ALL handler_eq, prims = prims, wfs = wfs,
  act = “ACTION”, snap = “SNAP”, guard = NONE}

val server_g = translate_async {
  name = "server_g", unfold = GEN_ALL server_unfold,
  prims = handler_g :: prims, wfs = wfs,
  act = “ACTION”, snap = “SNAP”, guard = NONE}

(* ------------------------------------------------------------------------
   Written once: the same echo server, from its recursive equations alone.
   define_async makes the model (fix, contractiveness, unfolding, wf);
   translate_async makes the code and the CF theorems.
   ------------------------------------------------------------------------ *)

val guards = [readable_NIL, emit_needs_snapshot]

val echo = define_async "echo"
  ‘echo fd =
     bind (readable fd) (λu.
     bind (emit (Read fd)) (λres.
       case res of
         Data d => bind (emit (Write fd d)) (λw. echo fd)
       | Eof => return ()
       | _ => echo fd))’ guards wfs

val echo_g = translate_async {
  name = "echo_g", unfold = #unfold echo, prims = prims,
  wfs = #wf echo :: wfs, act = “ACTION”, snap = “SNAP”, guard = NONE}

val echo_server = define_async "echo_server"
  ‘echo_server lfd =
     bind (readable lfd) (λu.
     bind (emit (Accept lfd)) (λres.
       case res of
         Accepted fd => map (λp. ()) (both (echo fd) (echo_server lfd))
       | _ => echo_server lfd))’ guards (#wf echo :: wfs)

val echo_server_g = translate_async {
  name = "echo_server_g", unfold = #unfold echo_server, prims = echo_g :: prims,
  wfs = #wf echo :: #wf echo_server :: wfs, act = “ACTION”, snap = “SNAP”,
  guard = NONE}

(* The generated model is the hand-written one *)
Theorem echo_is_handler:
  echo = handler
Proof
  simp[#def echo, handler_def] >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, DB.fetch "-" "echo_body_def", handler_body_def]
QED
