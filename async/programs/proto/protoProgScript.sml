(*
  protoProg: the server skeleton and the generic protocol handler in
  CakeML, in M3's program (extending echoSockServer, whose sreadable
  it reuses).  design/32 §2.4, phase 4.

  The skeleton mirrors protoSockModel's sserver_with_unfold:

     fun sserver_with h lfd =
       Async.bind (sreadable lfd) (fn u =>
       Async.bind (Async.emit (Accept lfd)) (fn r =>
         case r of
           Accepted (Some c) =>
             async_map (fn p => ()) (async_both (h c) (sserver_with h lfd))
         | _ => sserver_with h lfd));


  The handler is higher-order in the protocol: parse is the CakeML parser
  (a function from a char list to a presult, whose constructors the
  translator names Pcomplete, Pincomplete, Pinvalid) and respond computes
  a response's characters.  The code mirrors protoSockModel's
  sproto_handler_unfold:

     fun proto_handler parse respond fd buf =
       case parse buf of
         Pcomplete r rest =>
           Async.bind (Async.emit (Write fd (String.implode (respond r))))
                      (fn w => proto_handler parse respond fd rest)
       | Pincomplete =>
           Async.bind (sreadable fd) (fn u =>
           Async.bind (Async.emit (Read fd 4096)) (fn r =>
             case r of
               Got (Some s) =>
                 if s = "" then Async.return ()
                 else proto_handler parse respond fd (buf @ String.explode s)
             | _ => proto_handler parse respond fd buf))
       | Pinvalid => Async.return ();

     fun proto_server parse respond lfd =
       sserver_with (fn fd => proto_handler parse respond fd []) lfd;

  and the event loop on it, for the listener fd 3 (created by the C side):

     fun proto_main parse respond u = run_i ([3], proto_server parse respond 3);
*)
Theory protoProg
Ancestors
  asyncCore asyncLevel1 asyncChoose echoServer libModel
  libProg libApprox loopPollWorld loopPollProg loopPoll
  relabel relabelDist echoSockModel libSockApprox
  echoSockServer protoInterface ml_translator mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "echoSockServer"

val _ = register_type “:'a protoInterface$presult”;

Quote add_cakeml:
  fun sserver_with h lfd =
    Async.bind (sreadable lfd) (fn u =>
    Async.bind (Async.emit (Accept lfd)) (fn r =>
      case r of
        Accepted (Some c) =>
          async_map (fn p => ()) (async_both (h c) (sserver_with h lfd))
      | _ => sserver_with h lfd));

  fun proto_handler parse respond fd buf =
    case parse buf of
      Pcomplete r rest =>
        Async.bind (Async.emit (Write fd (String.implode (respond r))))
                   (fn w => proto_handler parse respond fd rest)
    | Pincomplete =>
        Async.bind (sreadable fd) (fn u =>
        Async.bind (Async.emit (Read fd 4096)) (fn r =>
          case r of
            Got (Some s) =>
              if s = "" then Async.return ()
              else proto_handler parse respond fd (buf @ String.explode s)
          | _ => proto_handler parse respond fd buf))
    | Pinvalid => Async.return ();

  fun proto_server parse respond lfd =
    sserver_with (fn fd => proto_handler parse respond fd []) lfd;

  fun proto_main parse respond u = run_i ([3], proto_server parse respond 3);
End
