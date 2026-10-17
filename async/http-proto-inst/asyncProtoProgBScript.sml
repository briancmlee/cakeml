(*
  asyncProtoProgB: the bodies HTTP server as an instance of the generic
  CakeML program (asyncProtoProg), design/32 phase 4.

  The program is asyncProtoProg's (the basis, Socket, the Async library,
  run_i, the generic handler, server and main) plus the bodies parser and
  responder, translated into the interface's types:

     b_parse s    = the bodies parser's result as a presult  (= P_b.parse)
     bresp files r = the response to request r               (= print_response o bhandle files)

  and the program's main:

     fun main u = proto_main b_parse bresp_demo u;

  The parser is translated through its linear-time versions (split_at2,
  split_path2, parse_bheaders2, bline2), as in asyncHttpSockProgB; the
  existing program (http_prog_b) is untouched.
*)
Theory asyncProtoProgB
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer HttpSpec HttpSpecHeaders HttpSpecBodies asyncHttpParse
  asyncHttpParseH asyncHttpParseB asyncHttpImplProg asyncHttpSockProg
  asyncHttpSockProgH asyncHttpSockProgB asyncHttpMain
  asyncProto asyncProtoB asyncProtoProg asyncProtoSockSpec
  ml_translator mlstring mlint std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncProtoProg"

val _ = register_type “:asyncHttpParseH$headers_result”;
val _ = register_type “:HttpSpecBodies$brequest”;
val _ = register_type “:asyncHttpParseB$bparse_result”;

(* ------------------------------------------------------------------------
   The bodies parser, translated through its linear-time versions
   (asyncHttpSockProgB's proofs, repeated: they are local there)
   ------------------------------------------------------------------------ *)

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

Theorem toString_num_to_str[local]:
  toString n = explode (num_to_str n)
Proof
  simp[num_to_str_def, mlintTheory.toString_thm]
QED

Theorem dec_fold_acc[local]:
  dec_fold s = dec_acc 0 s
Proof
  ‘∀s n. FOLDL (λn c. 10 * n + (ORD c - 48)) n s = dec_acc n s’
    by (Induct >> simp[dec_acc_def] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >>
        ‘ORD h - 48 = 0’ by simp[] >> simp[]) >>
  simp[dec_fold_def]
QED

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

(* Header-name characters, with ^ and ` as ORD tests for the translator
   (as in asyncHttpSockProgB, where this is local) *)
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

(* demo_files (asyncHttpMain's definition) is translated again in this program *)
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
