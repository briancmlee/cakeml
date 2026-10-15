(*
  The HTTP server in CakeML: the pure HTTP functions, translated.

  parse_request (asyncHttpParse) and the response for a path are pure
  functions; the translator turns them into CakeML with certificates, so
  their correctness is inherited from the HOL definitions (and from the
  parser's proofs against HttpSpec's printer).

  respond files p is print_response (handle files (Get p)), written without
  HttpSpec's response datatype (respond_thm), so that only the request and
  parse-result types are needed in CakeML.
*)
Theory asyncHttpImplProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActBothModel asyncCfActProg asyncCfActSpec asyncCfActBoth
  asyncM4Approx asyncM4ServerProg HttpSpec asyncHttpParse asyncHttpServer
  ml_translator ListProg mlint
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM4ServerProg"

(* The response to a request for path p *)
Definition respond_def:
  respond files p =
    case ALOOKUP files p of
      SOME body =>
        "HTTP/1.0 200 OK\r\nContent-Length: " ++
        explode (num_to_str (LENGTH body)) ++ "\r\n\r\n" ++ body
    | NONE => "HTTP/1.0 404 Not Found\r\nContent-Length: 0\r\n\r\n"
End

Theorem respond_thm:
  respond files p = print_response (handle files (Get p))
Proof
  simp[respond_def, handle_def, num_to_str_def] >> CASE_TAC >>
  simp[print_response_def, mlintTheory.toString_thm]
QED

val _ = register_type “:HttpSpec$request”;
val _ = register_type “:asyncHttpParse$parse_result”;

val r = translate split_path_def;
val r = translate get_sp_def;
val r = translate after_path_def;
val r = translate (parse_request_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate respond_def;

(* ------------------------------------------------------------------------
   The CakeML code: the generic server skeleton, the HTTP handler and server
   (mirroring asyncServerWith$server_with_unfold and
   asyncHttpServer$http_handler_unfold)
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun server_with h lfd =
    bind (readable lfd) (fn u =>
    bind (emit (Accept lfd)) (fn res =>
      case res of
        Accepted fd => map (fn p => ()) (both (h fd) (server_with h lfd))
      | _ => server_with h lfd));

  fun http_handler files fd buf =
    case parse_request buf of
      Complete (Get p) rest =>
        bind (emit (Write fd (respond files p))) (fn w =>
          http_handler files fd rest)
    | Incomplete =>
        bind (readable fd) (fn u =>
        bind (emit (Read fd)) (fn res =>
          case res of
            Data d => http_handler files fd (buf @ d)
          | Eof => return ()
          | _ => http_handler files fd buf))
    | Invalid => return ();

  fun http_server files lfd = server_with (fn fd => http_handler files fd []) lfd;
End
