(*
  The key-value server in CakeML, in M3's program (extending
  asyncProtoProg, whose sreadable and Async library it reuses; the bodies
  parser's translations are repeated from asyncProtoProgB).

  - with_store (generic in the store and its step function delta): the
    pure effect handler of asyncWithStore.  The store is an argument of the
    residual's closure, passed on round by round; no refs:

       fun ws_res delta st acts s =
         case s of
           Done x => Done x
         | Pending k => Pending (fn (rdy, t, rs) =>
             case ws_run delta st acts of (bs, st2) =>      (* answer the queries *)
             case k (rdy, t, ws_merge acts rs bs) of (acts2, s2) =>
               (ws_socks acts2, ws_res delta st2 acts2 s2));
       fun with_store delta st (acts, s) = (ws_socks acts, ws_res delta st acts s);

  - the store: an association list, kv_delta_al (translated), which
    implements HttpKvSpec's kv_step (kv_delta_al_thm);
  - the skeleton and the handler, mirroring asyncKvSockModel's unfolding
    equations, in the vocabulary Sock sact | Kv (fd, request).
*)
Theory asyncKvProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer HttpSpec HttpSpecHeaders HttpSpecBodies HttpKvSpec
  asyncHttpParse asyncHttpParseH asyncHttpParseB asyncProto asyncProtoB
  asyncProtoProg asyncProtoProgB asyncWithStore asyncKvModel
  ml_translator mlstring mlint std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncProtoProg"

(* ------------------------------------------------------------------------
   The bodies parser, translated through its linear-time versions
   (asyncProtoProgB's definitions; its translations and local lemmas are
   repeated here, as in asyncOCMainB: a CakeML program is one translation
   chain)
   ------------------------------------------------------------------------ *)

val _ = register_type “:asyncHttpParseH$headers_result”;
val _ = register_type “:HttpSpecBodies$brequest”;
val _ = register_type “:asyncHttpParseB$bparse_result”;

(* ------------------------------------------------------------------------
   The bodies parser, translated through its linear-time versions
   (asyncProtoProgB's local lemmas, repeated)
   ------------------------------------------------------------------------ *)

Theorem toString_num_to_str[local]:
  toString n = explode (num_to_str n)
Proof
  simp[num_to_str_def, mlintTheory.toString_thm]
QED

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
   The store, as an association list
   ------------------------------------------------------------------------ *)

Definition kv_step_al_def:
  kv_step_al (al : (string # string) list) (Req m k ver hs b) =
    if m = "POST" then (Ok "", (k, b) :: FILTER (λp. FST p ≠ k) al)
    else ((case ALOOKUP al k of SOME v => Ok v | NONE => NotFound), al)
End

Definition kv_delta_al_def:
  kv_delta_al al (q : num # brequest) = kv_step_al al (SND q)
End

(* The association list al represents the store st *)
Definition al_store_def:
  al_store (st : store) al ⇔ ∀k. st k = ALOOKUP al k
End

Theorem ALOOKUP_FILTER_key[local]:
  ∀al. ALOOKUP (FILTER (λp. FST p ≠ k) al) k' =
       if k' = k then NONE else ALOOKUP al k'
Proof
  Induct >> simp[] >> PairCases >> rw[] >> gvs[]
QED

(* MAIN: the association list implements kv_step *)
Theorem kv_delta_al_thm:
  al_store st al ⇒
  FST (kv_delta_al al q) = FST (kv_delta st q) ∧
  al_store (SND (kv_delta st q)) (SND (kv_delta_al al q))
Proof
  PairCases_on ‘q’ >> Cases_on ‘q1’ >>
  rw[kv_delta_al_def, kv_delta_def, kv_step_al_def, kv_step_def, al_store_def,
     combinTheory.UPDATE_def, ALOOKUP_FILTER_key] >>
  rw[] >> gvs[]
QED


(* The printed response *)
Definition sprint_response_def:
  sprint_response a =
    case a of
      Ok body => "HTTP/1.0 200 OK\r\nContent-Length: " ++
                 explode (num_to_str (LENGTH body)) ++ "\r\n\r\n" ++ body
    | NotFound => "HTTP/1.0 404 Not Found\r\nContent-Length: 0\r\n\r\n"
End

Theorem sprint_response_thm:
  sprint_response a = print_response a
Proof
  Cases_on ‘a’ >> simp[sprint_response_def, print_response_def, toString_num_to_str]
QED

val _ = register_type “:HttpSpec$response”;
val r = translate kv_step_al_def;
val r = translate kv_delta_al_def;
val r = translate sprint_response_def;

(* ------------------------------------------------------------------------
   with_store
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  datatype ('a, 'q) kact = Sock 'a | Kv 'q;
  datatype ('r, 'b) kres = Sockr 'r | Kvr 'b;

  fun ws_run delta st acts =
    case acts of
      [] => ([], st)
    | a :: rest =>
        (case a of
           Sock x => ws_run delta st rest
         | Kv q =>
             (case delta st q of
                (b, st1) =>
                  (case ws_run delta st1 rest of (bs, st2) => (b :: bs, st2))));

  fun ws_merge acts rs ans =
    case acts of
      [] => []
    | a :: rest =>
        (case a of
           Sock x =>
             (case rs of [] => [] | r :: rs1 => Sockr r :: ws_merge rest rs1 ans)
         | Kv q =>
             (case ans of [] => [] | b :: ans1 => Kvr b :: ws_merge rest rs ans1));

  fun ws_socks acts =
    case acts of
      [] => []
    | a :: rest =>
        (case a of Sock x => x :: ws_socks rest | Kv q => ws_socks rest);

  fun ws_res delta st acts s =
    case s of
      Done x => Done x
    | Pending k =>
        Pending (fn w =>
          case w of
            (rdy, t, rs) =>
              (case ws_run delta st acts of
                 (bs, st2) =>
                   (case k (rdy, t, ws_merge acts rs bs) of
                      (acts2, s2) => (ws_socks acts2, ws_res delta st2 acts2 s2))));

  fun with_store delta st c =
    case c of (acts, s) => (ws_socks acts, ws_res delta st acts s);
End

(* ------------------------------------------------------------------------
   The server
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun sserver_with_k h lfd =
    Async.bind (sreadable lfd) (fn u =>
    Async.bind (Async.emit (Sock (Accept lfd))) (fn r =>
      case r of
        Sockr (Accepted (Some c)) =>
          async_map (fn p => ()) (async_both (h c) (sserver_with_k h lfd))
      | _ => sserver_with_k h lfd));

  fun kv_handler fd buf =
    case parse_brequest buf of
      Bcomplete req rest =>
        Async.bind (Async.emit (Kv (fd, req))) (fn a =>
          case a of
            Kvr ans =>
              Async.bind (Async.emit (Sock (Write fd (String.implode (sprint_response ans)))))
                         (fn w => kv_handler fd rest)
          | _ => Async.return ())
    | Bincomplete =>
        Async.bind (sreadable fd) (fn u =>
        Async.bind (Async.emit (Sock (Read fd 4096))) (fn r =>
          case r of
            Sockr (Got (Some s)) =>
              if s = "" then Async.return ()
              else kv_handler fd (buf @ String.explode s)
          | _ => kv_handler fd buf))
    | Binvalid => Async.return ();

  fun kv_inner lfd = sserver_with_k (fn fd => kv_handler fd []) lfd;

  fun kv_server lfd = with_store kv_delta_al [] (kv_inner lfd);
End
