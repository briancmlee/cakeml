(*
  The header-tolerant HTTP server in CakeML, in M3's program (extending
  asyncHttpSockProg, whose sserver_with, sreadable and respond it reuses).

  The header-tolerant parser (asyncHttpParseH) is translated (the
  translator names the CakeML constructors Hcomplete, Hincomplete,
  Hinvalid, Geth); the code mirrors asyncHttpSockModelH's unfolding
  equation:

     fun http_handler_h files fd buf =
       case parse_hrequest buf of
         Hcomplete (Geth p v hs) rest =>
           Async.bind (Async.emit (Write fd (String.implode (respond files p))))
                      (fn w => http_handler_h files fd rest)
       | Hincomplete =>
           Async.bind (sreadable fd) (fn u =>
           Async.bind (Async.emit (Read fd 4096)) (fn r =>
             case r of
               Got (Some s) =>
                 if s = "" then Async.return ()
                 else http_handler_h files fd (buf @ String.explode s)
             | _ => http_handler_h files fd buf))
       | Hinvalid => Async.return ();

     fun http_server_h files lfd =
       sserver_with (fn fd => http_handler_h files fd []) lfd;
*)
Theory asyncHttpSockProgH
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer HttpSpec HttpSpecHeaders asyncHttpParse asyncHttpParseH
  asyncHttpImplProg asyncHttpSockProg ml_translator mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncHttpSockProg"

val _ = register_type “:HttpSpecHeaders$hrequest”;
val _ = register_type “:asyncHttpParseH$headers_result”;
val _ = register_type “:asyncHttpParseH$hparse_result”;

val r = translate split_at_def;
val r = translate crlf_def;
val r = translate colon_sp_def;
val r = translate sp_http10_def;
val r = translate sp_http11_def;
val r = translate stringTheory.isUpper_def;
val r = translate stringTheory.toLower_def;

(* toLower's CHR (ORD c + 32) is applied only to upper-case letters *)
Triviality tolower_side_proof:
  tolower_side c ⇔ T
Proof
  simp[fetch "-" "tolower_side_def", stringTheory.isUpper_def]
QED

val _ = tolower_side_proof |> update_precondition;
val r = translate body_header_def;
val r = translate_no_ind (parse_headers_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);

(* The translator's induction obligation for parse_headers *)
Triviality parse_headers_ind_proof:
  parse_headers_ind
Proof
  once_rewrite_tac [fetch "-" "parse_headers_ind_def"] >>
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  match_mp_tac (latest_ind ()) >> rpt strip_tac >>
  last_x_assum match_mp_tac >> rpt strip_tac >>
  gvs[FORALL_PROD, mllistTheory.drop_def]
QED

val _ = parse_headers_ind_proof |> update_precondition;
val r = translate hfinish_def;


val r = translate (parse_hrequest_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);



Quote add_cakeml:
  fun http_handler_h files fd buf =
    case parse_hrequest buf of
      Hcomplete (Geth p v hs) rest =>
        Async.bind (Async.emit (Write fd (String.implode (respond files p))))
                   (fn w => http_handler_h files fd rest)
    | Hincomplete =>
        Async.bind (sreadable fd) (fn u =>
        Async.bind (Async.emit (Read fd 4096)) (fn r =>
          case r of
            Got (Some s) =>
              if s = "" then Async.return ()
              else http_handler_h files fd (buf @ String.explode s)
          | _ => http_handler_h files fd buf))
    | Hinvalid => Async.return ();

  fun http_server_h files lfd =
    sserver_with (fn fd => http_handler_h files fd []) lfd;
End
