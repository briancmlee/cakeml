(*
  httpProg: the bodies HTTP server as an instance of the generic
  CakeML program (protoProg), design/32 phase 4.

  The program is protoProg's (the basis, Socket, the Async library,
  run_i, the generic handler, server and main) plus the bodies parser and
  responder, translated into the interface's types:

     b_parse s    = the bodies parser's result as a presult  (= P_b.parse)
     bresp files r = the response to request r               (= print_response o bhandle files)

  and the program's main:

     fun main u = proto_main b_parse bresp_demo u;

  The parser is translated through linear-time versions of its splitting
  functions (split_at2, split_path2, parse_bheaders2, bline2), each proved
  EQUAL to the original, so every theorem about the parser is unchanged.
  The demo's file map (demo_files) is defined here.
*)
Theory httpProg
Ancestors
  asyncCore asyncLevel1 asyncChoose echoServer libModel
  libProg libApprox loopPollWorld loopPollProg loopPoll
  relabel relabelDist echoSockModel libSockApprox
  echoSockServer HttpGetSpec HttpHeadersSpec HttpSpec httpGetParse
  httpHeadersParse httpParse
  protoInterface httpProto protoProg protoSockSpec
  ml_translator mlstring mlint std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "protoProg"

val _ = register_type “:httpHeadersParse$headers_result”;
val _ = register_type “:HttpSpec$brequest”;
val _ = register_type “:httpParse$bparse_result”;

(* The files the demo server serves *)
Definition demo_files_def:
  demo_files =
    [("/", "Hello from a verified CakeML HTTP server!\n");
     ("/index.html",
      "<html><body><h1>Verified CakeML</h1><p>Served by http_server, " ++
      "whose socket trace is proved to satisfy HttpSpec's http_safe.</p>" ++
      "</body></html>\n");
     ("/about", "HttpSpec subset: GET <path> HTTP/1.0, then a blank line.\n")]
End

Theorem toString_num_to_str[local]:
  toString n = explode (num_to_str n)
Proof
  simp[num_to_str_def, mlintTheory.toString_thm]
QED

(* The response to a GET of path p (HttpGetSpec's handle, printed, written
   without HttpGetSpec's response datatype for the translator) *)
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

(* ------------------------------------------------------------------------
   Linear-time parsing for the translation.  split_at and split_path, as
   defined, make their recursive call twice per level
   (d :: FST (split_at c cs), SND (split_at c cs)), so the code the
   translator generates from them runs in exponential time in the distance
   to the separator (a ~30-character header value pins the server).
   split_at2 and split_path2 share the call and are EQUAL to the originals;
   parse_bheaders2 and bline2 are the header-line and request-line parsers
   written with them, proved equal to parse_bheaders and bline, and
   parse_brequest is translated through bline2.
   ------------------------------------------------------------------------ *)

Definition split_path2_def:
  split_path2 [] = ([], []) ∧
  split_path2 (c :: cs) =
    if c = #" " then ([], c :: cs)
    else let (p, u) = split_path2 cs in (c :: p, u)
End

Theorem split_path2_eq:
  ∀cs. split_path2 cs = split_path cs
Proof
  Induct >> rw[split_path2_def, split_path_def] >> pairarg_tac >> gvs[]
QED

Definition split_at2_def:
  split_at2 c [] = ([], []) ∧
  split_at2 c (d :: cs) =
    if d = c then ([], d :: cs)
    else let (p, u) = split_at2 c cs in (d :: p, u)
End

Theorem split_at2_eq:
  ∀cs. split_at2 c cs = split_at c cs
Proof
  Induct >> rw[split_at2_def, split_at_def] >> pairarg_tac >> gvs[]
QED

Theorem split_at2_LENGTH[local]:
  ∀s. LENGTH (SND (split_at2 c s)) ≤ LENGTH s
Proof
  simp[split_at2_eq] >> Induct >> rw[split_at_def]
QED

Theorem split_at2_SND_LENGTH[local]:
  split_at2 c s = (p, u) ⇒ LENGTH u ≤ LENGTH s
Proof
  metis_tac[split_at2_LENGTH, SND]
QED

Definition parse_bheaders2_def:
  parse_bheaders2 s =
    if crlf ≼ s then HDone [] (DROP 2 s)
    else if s ≼ crlf then HMore
    else
      case split_at2 #":" s of
        (n, u) =>
          if EXISTS (λc. ¬tchar c) n then HBad
          else if u = [] then HMore
          else if n = [] then HBad
          else if ¬(colon_sp ≼ u) then (if u ≼ colon_sp then HMore else HBad)
          else
            case split_at2 #"\r" (DROP 2 u) of
              (v, w) =>
                if EXISTS (λc. ¬field_char c) v then HBad
                else if w = [] then HMore
                else if ¬(crlf ≼ w) then (if w ≼ crlf then HMore else HBad)
                else
                  case parse_bheaders2 (DROP 2 w) of
                    HDone hs r => HDone ((n, v) :: hs) r
                  | HMore => HMore
                  | HBad => HBad
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rw[] >>
  imp_res_tac split_at2_SND_LENGTH >>
  gvs[IS_PREFIX_APPEND, colon_sp_def]
End

Definition bline2_def:
  bline2 m t =
    case split_path2 t of
      (p, u) =>
        if EXISTS (λc. ¬uri_char c) p then BInvalid
        else if u = [] then BIncomplete
        else if p = [] then BInvalid
        else if sp_http10 ≼ u then bfinish m p "1.0" (parse_bheaders2 (DROP 11 u))
        else if sp_http11 ≼ u then bfinish m p "1.1" (parse_bheaders2 (DROP 11 u))
        else if u ≼ sp_http10 ∨ u ≼ sp_http11 then BIncomplete
        else BInvalid
End

(* dec_fold, with explicit recursion for the translator *)
Definition dec_acc_def:
  dec_acc n [] = n ∧
  dec_acc n (c :: cs) =
    dec_acc (10 * n + (if 48 ≤ ORD c then ORD c - 48 else 0)) cs
End


Theorem parse_bheaders2_eq[local]:
  ∀s. parse_bheaders2 s = parse_bheaders s
Proof
  recInduct parse_bheaders2_ind >> rw[] >>
  ONCE_REWRITE_TAC[parse_bheaders2_def, parse_bheaders_def] >>
  simp[split_at2_eq] >>
  Cases_on ‘split_at #":" s’ >> simp[] >>
  Cases_on ‘split_at #"\r" (DROP 2 r)’ >> simp[] >>
  rw[] >> gvs[split_at2_eq]
QED

Theorem bline2_eq[local]:
  bline2 m t = bline m t
Proof
  simp[bline2_def, bline_def, split_path2_eq, parse_bheaders2_eq] >>
  Cases_on ‘split_path t’ >> simp[]
QED

Theorem parse_brequest_lin[local] =
  parse_brequest_def |> REWRITE_RULE [GSYM bline2_eq];


Theorem dec_fold_acc[local]:
  dec_fold s = dec_acc 0 s
Proof
  ‘∀s n. FOLDL (λn c. 10 * n + (ORD c - 48)) n s = dec_acc n s’
    by (Induct >> simp[dec_acc_def] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >>
        ‘ORD h - 48 = 0’ by simp[] >> simp[]) >>
  simp[dec_fold_def]
QED

val r = translate split_path2_def;
val r = translate get_sp_def;
val r = translate after_path_def;
val r = translate respond_def;
val r = translate split_at2_def;
val r = translate crlf_def;
val r = translate colon_sp_def;
val r = translate sp_http10_def;
val r = translate sp_http11_def;
val r = translate stringTheory.isUpper_def;
val r = translate stringTheory.toLower_def;

Triviality tolower_side_proof:
  tolower_side c ⇔ T
Proof
  simp[fetch "-" "tolower_side_def", stringTheory.isUpper_def]
QED

val _ = tolower_side_proof |> update_precondition;

(* Header-name characters, with ^ and ` as ORD tests for the translator *)
Theorem tchar_ord[local]:
  tchar c ⇔
    isAlpha c ∨ isDigit c ∨ EXISTS (λd. c = d) "!#$%&'*+-._|~" ∨
    ORD c = 94 ∨ ORD c = 96
Proof
  ‘∀n. n < 256 ⇒ (c = CHR n ⇔ ORD c = n)’
    by (rw[] >> eq_tac >> rw[ORD_CHR_RWT] >> metis_tac[CHR_ORD]) >>
  simp[tchar_def]
QED

val r = translate stringTheory.isLower_def;
val r = translate stringTheory.isAlpha_def;
val r = translate stringTheory.isDigit_def;
val r = translate tchar_ord;
val r = translate field_char_def;
val r = translate uri_char_def;
val r = translate is_cl_def;
val r = translate is_te_def;
val r = translate post_sp_def;
val r = translate dec_acc_def;
val r = translate dec_fold_acc;
val r = translate (bbody_def |> REWRITE_RULE [toString_num_to_str,
                                               GSYM mllistTheory.take_def,
                                               GSYM mllistTheory.drop_def]);
val r = translate bfinish_def;
val r = translate_no_ind (parse_bheaders2_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);

Triviality parse_bheaders2_ind_proof:
  parse_bheaders2_ind
Proof
  once_rewrite_tac [fetch "-" "parse_bheaders2_ind_def"] >>
  rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  match_mp_tac (latest_ind ()) >> rpt strip_tac >>
  last_x_assum match_mp_tac >> rpt strip_tac >>
  gvs[FORALL_PROD, mllistTheory.drop_def]
QED

val _ = parse_bheaders2_ind_proof |> update_precondition;

val r = translate (bline2_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate (parse_brequest_lin |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate brespond_def;

(* ------------------------------------------------------------------------
   The interface's parser and responder
   ------------------------------------------------------------------------ *)

Definition b_parse_def:
  b_parse s =
    case parse_brequest s of
      BComplete r rest => PComplete r rest
    | BIncomplete => PIncomplete
    | BInvalid => PInvalid
End

Definition bresp_def:
  bresp files r = case r of Req m p v hs b => brespond files m p b
End

Theorem b_parse_P_b:
  b_parse = P_b.parse
Proof
  simp[FUN_EQ_THM, b_parse_def, P_b_def] >> gen_tac >>
  CASE_TAC >> simp[b_presult_def]
QED

Theorem bresp_eq:
  bresp files = print_response o bhandle files
Proof
  simp[FUN_EQ_THM] >> Cases >> simp[bresp_def, brespond_thm]
QED

val r = translate b_parse_def;
val r = translate bresp_def;

val r = translate demo_files_def;

(* The responder for the demo's files, as a translated function value *)
Definition bresp_demo_def:
  bresp_demo r = bresp demo_files r
End

Theorem bresp_demo_eq:
  bresp_demo = print_response o bhandle demo_files
Proof
  simp[FUN_EQ_THM, bresp_demo_def, bresp_eq]
QED

val r = translate bresp_demo_def;

Quote add_cakeml:
  fun main u = proto_main b_parse bresp_demo u;
End
