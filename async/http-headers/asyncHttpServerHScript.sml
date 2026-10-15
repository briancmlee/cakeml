(*
  The HTTP server in the async model, against the header-tolerant spec
  (spec/HttpSpecHeaders): asyncHttpServer with the header-tolerant parser
  (asyncHttpParseH).  Requests may carry any well-formed headers, which
  are ignored: the response is  print_response (handle files (hpath r)).

  Everything else is asyncHttpServer's, verbatim up to names (_h):
  the handler (fix of a contractive body), wf, settled, the server as
  server_with of the handler, http_handler_serves_h, http_server_safety_h,
  http_server_safety_hrequests.
*)
Theory asyncHttpServerH
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncServerWith HttpSpec HttpSpecHeaders asyncHttpParse
  asyncHttpParseH
Libs
  BasicProvers

Definition http_body_h_def:
  http_body_h files r p =
    case p of
      (fd, buf) =>
        case parse_hrequest buf of
          HComplete req rest =>
            bind (emit (Write fd (print_response (handle files (hpath req)))))
                 (λw. r (fd, rest))
        | HIncomplete =>
            bind (readable fd) (λu.
            bind (emit (Read fd)) (λres.
              case res of
                Data d => r (fd, buf ++ d)
              | Eof => return ()
              | _ => r (fd, buf)))
        | HInvalid => return ()
End

Theorem http_body_h_contractive:
  contractive (http_body_h files)
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[http_body_h_def] >>
  Cases_on ‘parse_hrequest p1’ >> simp[guarded_const]
  >- (ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot, nonexpansive_call])
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call, nonexpansive_const]
QED

Definition http_handler_h_def:
  http_handler_h files = fix (http_body_h files)
End

(* MAIN: the handler satisfies its recursive equation *)
Theorem http_handler_h_unfold:
  http_handler_h files (fd, buf) =
    case parse_hrequest buf of
      HComplete req rest =>
        bind (emit (Write fd (print_response (handle files (hpath req)))))
             (λw. http_handler_h files (fd, rest))
    | HIncomplete =>
        bind (readable fd) (λu.
        bind (emit (Read fd)) (λres.
          case res of
            Data d => http_handler_h files (fd, buf ++ d)
          | Eof => return ()
          | _ => http_handler_h files (fd, buf)))
    | HInvalid => return ()
Proof
  simp[http_handler_h_def, Once (MATCH_MP fix_unfold http_body_h_contractive)]
  >> simp[http_body_h_def]
QED

Theorem wf_http_handler_h:
  wf (http_handler_h files p)
Proof
  simp[http_handler_h_def] >> irule wf_fix >> simp[http_body_h_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[http_body_h_def] >> CASE_TAC >> simp[wf_return]
  >- (irule wf_bind >> simp[wf_emit])
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases >> simp[wf_return]
QED

Theorem settled_http_handler_h:
  settled (http_handler_h files p)
Proof
  simp[http_handler_h_def] >> irule settled_fix >> simp[http_body_h_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[http_body_h_def] >> CASE_TAC
  >> simp[settled_return]
  >- (irule settled_bind >> simp[wf_emit, settled_emit])
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases
  >> simp[settled_return]
QED

(* The HTTP server: the echo server's skeleton with the HTTP handler *)
Definition http_server_h_def:
  http_server_h files lfd = server_with (λfd. http_handler_h files (fd, "")) lfd
End

Theorem wf_http_server_h:
  wf (http_server_h files lfd)
Proof
  simp[http_server_h_def] >> irule wf_server_with >> simp[wf_http_handler_h]
QED

Theorem settled_http_server_h:
  settled (http_server_h files lfd)
Proof
  simp[http_server_h_def] >> irule settled_server_with >>
  simp[wf_http_handler_h, settled_http_handler_h]
QED

(* ------------------------------------------------------------------------
   Safety
   ------------------------------------------------------------------------ *)

(* The intended responses to the complete requests at the front of s *)
Overload responses_to_h = “λfiles s. MAP (print_response o handle files o hpath) (parse_all_h s)”

(* MAIN: one connection.  The handler only reads and writes its own fd, and
   what it has written is a prefix of the responses to the complete requests
   in its buffer followed by everything it has read. *)
Theorem http_handler_serves_h:
  ∀hh buf.
    EVERY (on_fd fd) (trans (http_handler_h files (fd, buf)) hh) ∧
    written fd (trans (http_handler_h files (fd, buf)) hh) ≼
    responses_to_h files (buf ++ CONCAT (read fd (trans (http_handler_h files (fd, buf)) hh)))
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[http_handler_h_unfold] >>
  Cases_on ‘parse_hrequest buf’ >> simp[]
  >- ((* a complete request: write its response, continue with the rest *)
      rename1 ‘HComplete req rest’ >>
      qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Write fd resp)) K0) hh’ >>
      qspecl_then [‘emit (Write fd resp)’, ‘K0’, ‘hh’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
      simp[wf_emit, settled_emit] >> strip_tac
      >- (simp[trans_emit] >> drule parse_all_h_Complete >> simp[Abbr ‘resp’])
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K0’] >>
      first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >>
      disch_then (qspec_then ‘rest’ strip_assume_tac) >> simp[] >>
      drule parse_hextend >>
      disch_then (qspec_then ‘CONCAT (read fd (trans (http_handler_h files (fd, rest)) h2))’ assume_tac) >>
      drule parse_all_h_Complete >> simp[])
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
Theorem http_server_safety_h:
  fresh (trans (http_server_h files lfd) hh) ⇒
  ∀fd. written fd (trans (http_server_h files lfd) hh) ≼
       responses_to_h files (CONCAT (read fd (trans (http_server_h files lfd) hh)))
Proof
  rw[http_server_h_def] >>
  mp_tac (server_with_isolates
          |> INST_TYPE [alpha |-> “:unit”]
          |> INST [mk_var ("h", “:num -> (event, asyncServer$response) snapshot list ->
                                 (action, unit option) asyncCore$outcome”) |->
                   “λfd. http_handler_h files (fd, "")”]
          |> BETA_RULE) >>
  impl_tac >- simp[http_handler_serves_h] >>
  disch_then drule >> strip_tac >>
  qpat_x_assum ‘∀fd. FILTER _ _ = _ ∨ _’ (qspec_then ‘fd’ strip_assume_tac) >>
  ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER] >> simp[]
  >> qspecl_then [‘L’, ‘""’] mp_tac http_handler_serves_h
  >> simp[]
QED

(* MAIN: the same in HttpSpec's terms.  If what the server has read from fd
   is printed valid requests rs followed by a rest that does not start with
   a printed valid request, then what it has written to fd is a prefix of
   the printed responses to rs. *)
Theorem http_server_safety_hrequests:
  fresh (trans (http_server_h files lfd) hh) ∧
  CONCAT (read fd (trans (http_server_h files lfd) hh)) =
    FLAT (MAP print_hrequest rs) ++ rest ∧
  EVERY valid_hrequest rs ∧
  (∀r more. valid_hrequest r ⇒ rest ≠ print_hrequest r ++ more) ⇒
  written fd (trans (http_server_h files lfd) hh) ≼
  MAP (print_response o handle files o hpath) rs
Proof
  strip_tac >> drule http_server_safety_h >>
  disch_then (qspec_then ‘fd’ mp_tac) >> simp[parse_all_hrequests]
QED

