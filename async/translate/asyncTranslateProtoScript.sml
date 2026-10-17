(*
  The generic proto handler (http-proto), written once as a recursive
  equation in the socket library's vocabulary and translated: no
  hand-written CakeML for the handler, no hand-written CF proof.

  gproto_handler_spec has the statement of the hand-written
  sproto_handler_spec (asyncProtoSockSpec) for the generated code: it
  implements srelabel (proto_handler P resp (fd, buf)) given PROTO_IMPL.
  The bridge gproto_eq (the generated model is the hand-written one, by
  uniqueness of fixpoints) is model-level glue, as is the server, which
  plugs the handler into the chain's sserver_with (a Tcp.serve-style
  library primitive whose spec takes the handler's spec as a hypothesis).
*)
Theory asyncTranslateProto
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM4Approx
  asyncM3World asyncM3Prog asyncM3Loop asyncM4Relabel asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncServerWith asyncHttpSockSpec
  asyncProto asyncProtoServer asyncProtoSockModel asyncProtoProg
  asyncProtoSockSpec asyncTranslateSock ml_translator mlstring std_prelude
  ListProg asyncM4GRounds asyncM4Loop asyncServerWithUses asyncRunOkGen
  asyncHttpSockProg ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv
  ffiSpikeDivMain EchoSpec HttpSpec asyncProtoSafe asyncProtoLive
  asyncProtoMain asyncHeadline cfDiv ml_prog llist
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib
  cfDivLib asyncTranslateLib

val _ = translation_extends "asyncTranslateSock"

val sock_vocab : vocab =
  {bind = "Async.bind", map = "async_map", both = "async_both",
   bind_guarded = Async_bind_guarded_any, bind_d = Async_bind_spec_d,
   map_d = async_map_spec_d, both_d = async_both_spec_d}

val prims : prim list = [
  {const = “asyncLevel1$return”, name = "Async.return",
   spec = Async_return_spec, guard = NONE, wf = asyncLevel1Theory.wf_return},
  {const = “asyncM4SockModel$sreadable”, name = "sreadable",
   spec = sreadable_spec, guard = SOME sreadable_NIL, wf = wf_sreadable},
  {const = “asyncTranslateSock$swrite”, name = "swrite",
   spec = swrite_spec, guard = SOME swrite_NIL, wf = wf_swrite},
  {const = “asyncTranslateSock$sread”, name = "sread",
   spec = sread_spec, guard = SOME sread_NIL, wf = wf_sread}]

val wfs = [asyncLevel1Theory.wf_return, wf_sreadable, wf_swrite, wf_sread, asyncLevel1Theory.wf_bind, asyncLevel1Theory.wf_map,
           asyncLevel1Theory.wf_both]
val guards = [sreadable_NIL, swrite_NIL, sread_NIL]

(* The handler, written once: answer each complete request, else read *)
val gproto = define_async "gproto" 2
  ‘gproto prs resp fd buf =
     case prs buf of
       PComplete req rest =>
         bind (swrite fd (resp req)) (λw. gproto prs resp fd rest)
     | PIncomplete =>
         bind (sreadable fd) (λu.
         bind (sread fd) (λro.
           case ro of
             SOME s => if s = [] then return () else gproto prs resp fd (buf ++ s)
           | NONE => gproto prs resp fd buf))
     | PInvalid => return ()’ guards wfs

val gproto_g = translate_async {
  name = "gproto_g", unfold = #unfold gproto, prims = prims,
  wfs = #wf gproto :: wfs, act = “SACT”, snap = “SSNAP”, guard = NONE,
  vocab = sock_vocab, pre = [“fd < dimword(:64)”], defs = []}

