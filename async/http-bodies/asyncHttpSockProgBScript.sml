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

(* ------------------------------------------------------------------------
   Linear-time splitting for the translation.  split_at and split_path
   (asyncHttpParseH, asyncHttpParse) compute their recursive call twice
   (FST and SND of it), so evaluating them takes time exponential in the
   distance to the separator: a 33-character header value already takes
   2^33 steps.  The proofs are unaffected (they are about values), but the
   program must not use them.  split_at2, split_path2 and parse_headers2
   share the recursive call; they are proved equal to the originals, and
   parse_brequest is translated through them (bline2), so every theorem
   about parse_brequest is unchanged.
   ------------------------------------------------------------------------ *)

Definition split_at2_def:
  split_at2 c [] = ([], []) ∧
  split_at2 c (d :: cs) =
    if d = c then ([], d :: cs)
    else case split_at2 c cs of (p, u) => (d :: p, u)
End

Theorem split_at2_eq[local]:
  ∀s. split_at2 c s = split_at c s
Proof
  Induct >> rw[split_at2_def, split_at_def] >>
  Cases_on ‘split_at c s’ >> simp[]
QED

Definition split_path2_def:
  split_path2 [] = ([], []) ∧
  split_path2 (c :: cs) =
    if c = #" " then ([], c :: cs)
    else case split_path2 cs of (p, u) => (c :: p, u)
End

Theorem split_path2_eq[local]:
  ∀s. split_path2 s = split_path s
Proof
  Induct >> rw[split_path2_def, split_path_def] >>
  Cases_on ‘split_path s’ >> simp[]
QED

Theorem split_at2_LENGTH[local]:
  ∀s. LENGTH (SND (split_at2 c s)) ≤ LENGTH s
Proof
  Induct >> rw[split_at2_def] >> Cases_on ‘split_at2 c s’ >> fs[]
QED

Theorem split_at2_SND_LENGTH[local]:
  split_at2 c s = (p, u) ⇒ LENGTH u ≤ LENGTH s
Proof
  metis_tac[split_at2_LENGTH, SND]
QED

Definition parse_headers2_def:
  parse_headers2 s =
    if crlf ≼ s then HDone [] (DROP 2 s)
    else if s ≼ crlf then HMore
    else
      case split_at2 #":" s of
        (n, u) =>
          if EXISTS (λc. c = #" " ∨ c = #"\r" ∨ c = #"\n") n then HBad
          else if u = [] then HMore
          else if n = [] then HBad
          else if ¬(colon_sp ≼ u) then (if u ≼ colon_sp then HMore else HBad)
          else
            case split_at2 #"\r" (DROP 2 u) of
              (v, w) =>
                if EXISTS (λc. c = #"\n") v then HBad
                else if w = [] then HMore
                else if ¬(crlf ≼ w) then (if w ≼ crlf then HMore else HBad)
                else
                  case parse_headers2 (DROP 2 w) of
                    HDone hs r => HDone ((n, v) :: hs) r
                  | HMore => HMore
                  | HBad => HBad
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rw[] >>
  imp_res_tac split_at2_SND_LENGTH >>
  gvs[IS_PREFIX_APPEND, colon_sp_def]
End

Theorem parse_headers2_eq[local]:
  ∀s. parse_headers2 s = parse_headers s
Proof
  recInduct parse_headers2_ind >> rw[] >>
  ONCE_REWRITE_TAC[parse_headers2_def, parse_headers_def] >>
  simp[split_at2_eq] >>
  Cases_on ‘split_at #":" s’ >> simp[] >>
  Cases_on ‘split_at #"\r" (DROP 2 r)’ >> simp[] >>
  rw[] >> gvs[split_at2_eq]
QED

Definition bline2_def:
  bline2 m t =
    case split_path2 t of
      (p, u) =>
        if EXISTS (λc. c = #"\r" ∨ c = #"\n") p then BInvalid
        else if u = [] then BIncomplete
        else if p = [] then BInvalid
        else if sp_http10 ≼ u then bfinish m p "1.0" (parse_headers2 (DROP 11 u))
        else if sp_http11 ≼ u then bfinish m p "1.1" (parse_headers2 (DROP 11 u))
        else if u ≼ sp_http10 ∨ u ≼ sp_http11 then BIncomplete
        else BInvalid
End

Theorem bline2_eq[local]:
  bline2 m t = bline m t
Proof
  simp[bline2_def, bline_def, split_path2_eq, parse_headers2_eq] >>
  Cases_on ‘split_path t’ >> simp[]
QED

(* parse_brequest, through bline2 *)
Theorem parse_brequest_lin[local] =
  parse_brequest_def |> REWRITE_RULE [GSYM bline2_eq];

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
val r = translate split_at2_def;
val r = translate split_path2_def;
val r = translate_no_ind (parse_headers2_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);

Triviality parse_headers2_ind_proof:
  parse_headers2_ind
Proof
  once_rewrite_tac [fetch "-" "parse_headers2_ind_def"] >>
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  match_mp_tac (latest_ind ()) >> rpt strip_tac >>
  last_x_assum match_mp_tac >> rpt strip_tac >>
  gvs[FORALL_PROD, mllistTheory.drop_def]
QED

val _ = parse_headers2_ind_proof |> update_precondition;

val r = translate (bline2_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate (parse_brequest_lin |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
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
