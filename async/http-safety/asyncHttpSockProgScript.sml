(*
  The HTTP server in CakeML, in the socket vocabulary of M3's event loop
  (the program of asyncM4SockServer, extended).

  The pure functions (parse_request and its helpers, respond) are
  translated again in this translation chain (asyncHttpImplProg translated
  them in the cf-actions chain, which is a different CakeML program).
  The code mirrors asyncHttpSockModel's unfolding equations:

     fun sserver_with h lfd =
       Async.bind (sreadable lfd) (fn u =>
       Async.bind (Async.emit (Accept lfd)) (fn r =>
         case r of
           Accepted (Some c) =>
             async_map (fn p => ()) (async_both (h c) (sserver_with h lfd))
         | _ => sserver_with h lfd));

     fun http_handler files fd buf =
       case parse_request buf of
         Complete (Get p) rest =>
           Async.bind (Async.emit (Write fd (String.implode (respond files p))))
                      (fn w => http_handler files fd rest)
       | Incomplete =>
           Async.bind (sreadable fd) (fn u =>
           Async.bind (Async.emit (Read fd 4096)) (fn r =>
             case r of
               Got (Some s) =>
                 if s = "" then Async.return ()
                 else http_handler files fd (buf @ String.explode s)
             | _ => http_handler files fd buf))
       | Invalid => Async.return ();

     fun http_server files lfd = sserver_with (fn fd => http_handler files fd []) lfd;
*)
Theory asyncHttpSockProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer HttpSpec asyncHttpParse asyncHttpImplProg
  ml_translator mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM4SockServer"

val _ = register_type “:HttpSpec$request”;
val _ = register_type “:asyncHttpParse$parse_result”;

val r = translate split_path_def;
val r = translate get_sp_def;
val r = translate after_path_def;
val r = translate (parse_request_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate respond_def;

Quote add_cakeml:
  fun sserver_with h lfd =
    Async.bind (sreadable lfd) (fn u =>
    Async.bind (Async.emit (Accept lfd)) (fn r =>
      case r of
        Accepted (Some c) =>
          async_map (fn p => ()) (async_both (h c) (sserver_with h lfd))
      | _ => sserver_with h lfd));

  fun http_handler files fd buf =
    case parse_request buf of
      Complete (Get p) rest =>
        Async.bind (Async.emit (Write fd (String.implode (respond files p))))
                   (fn w => http_handler files fd rest)
    | Incomplete =>
        Async.bind (sreadable fd) (fn u =>
        Async.bind (Async.emit (Read fd 4096)) (fn r =>
          case r of
            Got (Some s) =>
              if s = "" then Async.return ()
              else http_handler files fd (buf @ String.explode s)
          | _ => http_handler files fd buf))
    | Invalid => Async.return ();

  fun http_server files lfd = sserver_with (fn fd => http_handler files fd []) lfd;
End
