(*
  The bodies HTTP server in CakeML, in M3's program (extending
  asyncHttpSockProgH, whose parse_headers, respond and sserver_with it
  reuses).

  brespond computes the response string from the request's method, path
  and body (brespond_thm: it is  print_response (bhandle files r)).  The
  bodies parser is translated (the translator names the CakeML
  constructors Bcomplete, Bincomplete, Binvalid); the code mirrors
  asyncHttpSockModelB's unfolding equation:

     fun http_handler_b files fd buf =
       case parse_brequest buf of
         Bcomplete (Req m p v hs b) rest =>
           Async.bind (Async.emit (Write fd (String.implode (brespond files m p b))))
                      (fn w => http_handler_b files fd rest)
       | Bincomplete => (wait until readable, read, continue)
       | Binvalid => Async.return ();

     fun http_server_b files lfd =
       sserver_with (fn fd => http_handler_b files fd []) lfd;
*)
Theory asyncHttpSockProgB
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer HttpSpec HttpSpecHeaders HttpSpecBodies asyncHttpParse
  asyncHttpParseH asyncHttpParseB asyncHttpImplProg asyncHttpSockProg
  asyncHttpSockProgH ml_translator mlstring mlint std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncHttpSockProgH"

Theorem toString_num_to_str[local]:
  toString n = explode (num_to_str n)
Proof
  simp[num_to_str_def, mlintTheory.toString_thm]
QED

(* The response to a request with method m, path p and body b *)
Definition brespond_def:
  brespond files m p b =
    if m = "POST" then
      (if p = "/echo" then
         "HTTP/1.0 200 OK\r\nContent-Length: " ++
         explode (num_to_str (LENGTH b)) ++ "\r\n\r\n" ++ b
       else "HTTP/1.0 404 Not Found\r\nContent-Length: 0\r\n\r\n")
    else respond files p
End

Theorem brespond_thm:
  brespond files m p b = print_response (bhandle files (Req m p ver hs b))
Proof
  rw[brespond_def, bhandle_def, respond_thm, print_response_def,
     GSYM toString_num_to_str]
QED

val _ = register_type “:HttpSpecBodies$brequest”;
val _ = register_type “:asyncHttpParseB$bparse_result”;

val r = translate stringTheory.toLower_def;

Theorem tolower_side_thm[local]:
  tolower_side c
Proof
  simp[fetch "-" "tolower_side_def", stringTheory.isUpper_def]
QED

val _ = update_precondition tolower_side_thm;

val r = translate is_cl_def;
val r = translate is_te_def;
val r = translate post_sp_def;
(* dec_fold, with explicit recursion for the translator *)
Definition dec_acc_def:
  dec_acc n [] = n ∧
  dec_acc n (c :: cs) =
    dec_acc (10 * n + (if 48 ≤ ORD c then ORD c - 48 else 0)) cs
End

Theorem dec_fold_acc[local]:
  dec_fold s = dec_acc 0 s
Proof
  ‘∀s n. FOLDL (λn c. 10 * n + (ORD c - 48)) n s = dec_acc n s’
    by (Induct >> simp[dec_acc_def] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >>
        ‘ORD h - 48 = 0’ by simp[] >> simp[]) >>
  simp[dec_fold_def]
QED

val r = translate dec_acc_def;
val r = translate dec_fold_acc;
val r = translate (bbody_def |> REWRITE_RULE [toString_num_to_str,
                                               GSYM mllistTheory.take_def,
                                               GSYM mllistTheory.drop_def]);
val r = translate bfinish_def;
val r = translate (bline_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate (parse_brequest_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate brespond_def;

Quote add_cakeml:
  fun http_handler_b files fd buf =
    case parse_brequest buf of
      Bcomplete (Req m p v hs b) rest =>
        Async.bind (Async.emit (Write fd (String.implode (brespond files m p b))))
                   (fn w => http_handler_b files fd rest)
    | Bincomplete =>
        Async.bind (sreadable fd) (fn u =>
        Async.bind (Async.emit (Read fd 4096)) (fn r =>
          case r of
            Got (Some s) =>
              if s = "" then Async.return ()
              else http_handler_b files fd (buf @ String.explode s)
          | _ => http_handler_b files fd buf))
    | Binvalid => Async.return ();

  fun http_server_b files lfd =
    sserver_with (fn fd => http_handler_b files fd []) lfd;
End
