(*
  The HTTP server in the async model, against the bodies spec
  (spec/HttpSpecBodies): asyncHttpServerH with the bodies parser
  (asyncHttpParseB).  Requests may carry a body framed by Content-Length;
  the response is  print_response (bhandle files r).

  Everything else is asyncHttpServer's, verbatim up to names (_b):
  the handler (fix of a contractive body), wf, settled, the server as
  server_with of the handler, http_handler_serves_b, http_server_safety_b,
  http_server_safety_brequests.
*)
Theory asyncHttpServerB
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncServerWith HttpSpec HttpSpecHeaders HttpSpecBodies
  asyncHttpParse asyncHttpParseH asyncHttpParseB
Libs
  BasicProvers

Definition http_body_b_def:
  http_body_b files r p =
    case p of
      (fd, buf) =>
        case parse_brequest buf of
          BComplete req rest =>
            bind (emit (Write fd (print_response (bhandle files req))))
                 (λw. r (fd, rest))
        | BIncomplete =>
            bind (readable fd) (λu.
            bind (emit (Read fd)) (λres.
              case res of
                Data d => r (fd, buf ++ d)
              | Eof => return ()
              | _ => r (fd, buf)))
        | BInvalid => return ()
End

Theorem http_body_b_contractive:
  contractive (http_body_b files)
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[http_body_b_def] >>
  Cases_on ‘parse_brequest p1’ >> simp[guarded_const]
  >- (ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot, nonexpansive_call])
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call, nonexpansive_const]
QED

Definition http_handler_b_def:
  http_handler_b files = fix (http_body_b files)
End

(* MAIN: the handler satisfies its recursive equation *)
Theorem http_handler_b_unfold:
  http_handler_b files (fd, buf) =
    case parse_brequest buf of
      BComplete req rest =>
        bind (emit (Write fd (print_response (bhandle files req))))
             (λw. http_handler_b files (fd, rest))
    | BIncomplete =>
        bind (readable fd) (λu.
        bind (emit (Read fd)) (λres.
          case res of
            Data d => http_handler_b files (fd, buf ++ d)
          | Eof => return ()
          | _ => http_handler_b files (fd, buf)))
    | BInvalid => return ()
Proof
  simp[http_handler_b_def, Once (MATCH_MP fix_unfold http_body_b_contractive)]
  >> simp[http_body_b_def]
QED

Theorem wf_http_handler_b:
  wf (http_handler_b files p)
Proof
  simp[http_handler_b_def] >> irule wf_fix >> simp[http_body_b_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[http_body_b_def] >> CASE_TAC >> simp[wf_return]
  >- (irule wf_bind >> simp[wf_emit])
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases >> simp[wf_return]
QED

Theorem settled_http_handler_b:
  settled (http_handler_b files p)
Proof
  simp[http_handler_b_def] >> irule settled_fix >> simp[http_body_b_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[http_body_b_def] >> CASE_TAC
  >> simp[settled_return]
  >- (irule settled_bind >> simp[wf_emit, settled_emit])
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases
  >> simp[settled_return]
QED

(* The HTTP server: the echo server's skeleton with the HTTP handler *)
Definition http_server_b_def:
  http_server_b files lfd = server_with (λfd. http_handler_b files (fd, "")) lfd
End

Theorem wf_http_server_b:
  wf (http_server_b files lfd)
Proof
  simp[http_server_b_def] >> irule wf_server_with >> simp[wf_http_handler_b]
QED

Theorem settled_http_server_b:
  settled (http_server_b files lfd)
Proof
  simp[http_server_b_def] >> irule settled_server_with >>
  simp[wf_http_handler_b, settled_http_handler_b]
QED

(* ------------------------------------------------------------------------
   Safety
   ------------------------------------------------------------------------ *)

(* The intended responses to the complete requests at the front of s *)
Overload responses_to_b = “λfiles s. MAP (print_response o bhandle files) (parse_all_b s)”

(* MAIN: one connection.  The handler only reads and writes its own fd, and
   what it has written is a prefix of the responses to the complete requests
   in its buffer followed by everything it has read. *)
Theorem http_handler_serves_b:
  ∀hh buf.
    EVERY (on_fd fd) (trans (http_handler_b files (fd, buf)) hh) ∧
    written fd (trans (http_handler_b files (fd, buf)) hh) ≼
    responses_to_b files (buf ++ CONCAT (read fd (trans (http_handler_b files (fd, buf)) hh)))
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[http_handler_b_unfold] >>
  Cases_on ‘parse_brequest buf’ >> simp[]
  >- ((* a complete request: write its response, continue with the rest *)
      rename1 ‘BComplete req rest’ >>
      qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Write fd resp)) K0) hh’ >>
      qspecl_then [‘emit (Write fd resp)’, ‘K0’, ‘hh’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
      simp[wf_emit, settled_emit] >> strip_tac
      >- (simp[trans_emit] >> drule parse_all_b_Complete >> simp[Abbr ‘resp’])
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K0’] >>
      first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >>
      disch_then (qspec_then ‘rest’ strip_assume_tac) >> simp[] >>
      drule parse_bextend >>
      disch_then (qspec_then ‘CONCAT (read fd (trans (http_handler_b files (fd, rest)) h2))’ assume_tac) >>
      drule parse_all_b_Complete >> simp[])
  (* incomplete: wait until fd is readable, read, continue *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) hh’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Read fd)) K1) h2’
  >> qspecl_then [‘emit (Read fd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit] >> Cases_on ‘h2’ >> simp[]
      >> first_x_assum (qspec_then ‘1’ mp_tac) >> simp[emit_def]
      >> Cases_on ‘oHD h.results’ >> simp[])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> Cases_on ‘res’ >> simp[]
  (* data d: continue with buf ++ d *)
  >> TRY (rename1 ‘Data d’ >>
          first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >>
          disch_then (qspec_then ‘buf ++ d’ strip_assume_tac) >> simp[] >>
          fs[GSYM APPEND_ASSOC] >> NO_TAC)
  (* would block, or a stray response: continue with buf *)
  >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[]
QED

(* MAIN: the HTTP analogue of echo_server_safety.  If the connections the
   world hands out are distinct, then on every connection fd, the strings
   the server has written to fd are a prefix of the printed responses to
   the complete requests it has read from fd so far, in order. *)
Theorem http_server_safety_b:
  fresh (trans (http_server_b files lfd) hh) ⇒
  ∀fd. written fd (trans (http_server_b files lfd) hh) ≼
       responses_to_b files (CONCAT (read fd (trans (http_server_b files lfd) hh)))
Proof
  rw[http_server_b_def] >>
  mp_tac (server_with_isolates
          |> INST_TYPE [alpha |-> “:unit”]
          |> INST [mk_var ("h", “:num -> (event, asyncServer$response) snapshot list ->
                                 (action, unit option) asyncCore$outcome”) |->
                   “λfd. http_handler_b files (fd, "")”]
          |> BETA_RULE) >>
  impl_tac >- simp[http_handler_serves_b] >>
  disch_then drule >> strip_tac >>
  qpat_x_assum ‘∀fd. FILTER _ _ = _ ∨ _’ (qspec_then ‘fd’ strip_assume_tac) >>
  ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER] >> simp[]
  >> qspecl_then [‘L’, ‘""’] mp_tac http_handler_serves_b
  >> simp[]
QED

(* MAIN: the same in HttpSpec's terms.  If what the server has read from fd
   is printed valid requests rs followed by a rest that does not start with
   a printed valid request, then what it has written to fd is a prefix of
   the printed responses to rs. *)
Theorem http_server_safety_brequests:
  fresh (trans (http_server_b files lfd) hh) ∧
  CONCAT (read fd (trans (http_server_b files lfd) hh)) =
    FLAT (MAP print_brequest rs) ++ rest ∧
  EVERY valid_brequest rs ∧
  (∀r more. valid_brequest r ⇒ rest ≠ print_brequest r ++ more) ⇒
  written fd (trans (http_server_b files lfd) hh) ≼
  MAP (print_response o bhandle files) rs
Proof
  strip_tac >> drule http_server_safety_b >>
  disch_then (qspec_then ‘fd’ mp_tac) >> simp[parse_all_brequests]
QED

