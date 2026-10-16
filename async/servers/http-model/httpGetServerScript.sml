(*
  The HTTP server in the async model.

  One connection (http_handler files (fd, buf), with buf the bytes read but
  not yet consumed):

     if buf starts with a complete request r:
          write print_response (handle files r), continue with the rest
     if buf is an incomplete request:
          wait until fd is readable; read; on Data d continue with buf ++ d,
          on Eof stop, otherwise continue with buf
     if buf is invalid: stop

  defined with the recursion rule (fix; every recursive call comes after an
  emit or a wait), well-formed and settled.

  The server is the echo server's skeleton with this handler:
     http_server files lfd = server_with (λfd. http_handler files (fd, "")) lfd

  Safety (http_server_safety): if the connections the world hands out are
  distinct, then on every connection fd the strings written to fd are a
  prefix of the printed responses to the complete requests read from fd so
  far.  http_server_safety_requests restates it in HttpGetSpec's terms
  (requests rs ++ rest).
*)
Theory httpGetServer
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript echoServer
  echoServerSafety skeleton HttpGetSpec httpGetParse
Libs
  BasicProvers

Definition http_body_def:
  http_body files r p =
    case p of
      (fd, buf) =>
        case parse_request buf of
          Complete req rest =>
            bind (emit (Write fd (print_response (handle files req))))
                 (λw. r (fd, rest))
        | Incomplete =>
            bind (readable fd) (λu.
            bind (emit (Read fd)) (λres.
              case res of
                Data d => r (fd, buf ++ d)
              | Eof => return ()
              | _ => r (fd, buf)))
        | Invalid => return ()
End

Theorem http_body_contractive:
  contractive (http_body files)
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[http_body_def] >>
  Cases_on ‘parse_request p1’ >> simp[guarded_const]
  >- (ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot, nonexpansive_call])
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call, nonexpansive_const]
QED

Definition http_handler_def:
  http_handler files = fix (http_body files)
End

(* MAIN: the handler satisfies its recursive equation *)
Theorem http_handler_unfold:
  http_handler files (fd, buf) =
    case parse_request buf of
      Complete req rest =>
        bind (emit (Write fd (print_response (handle files req))))
             (λw. http_handler files (fd, rest))
    | Incomplete =>
        bind (readable fd) (λu.
        bind (emit (Read fd)) (λres.
          case res of
            Data d => http_handler files (fd, buf ++ d)
          | Eof => return ()
          | _ => http_handler files (fd, buf)))
    | Invalid => return ()
Proof
  simp[http_handler_def, Once (MATCH_MP fix_unfold http_body_contractive)]
  >> simp[http_body_def]
QED

Theorem wf_http_handler:
  wf (http_handler files p)
Proof
  simp[http_handler_def] >> irule wf_fix >> simp[http_body_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[http_body_def] >> CASE_TAC >> simp[wf_return]
  >- (irule wf_bind >> simp[wf_emit])
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases >> simp[wf_return]
QED

Theorem settled_http_handler:
  settled (http_handler files p)
Proof
  simp[http_handler_def] >> irule settled_fix >> simp[http_body_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[http_body_def] >> CASE_TAC
  >> simp[settled_return]
  >- (irule settled_bind >> simp[wf_emit, settled_emit])
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases
  >> simp[settled_return]
QED

(* The HTTP server: the echo server's skeleton with the HTTP handler *)
Definition http_server_def:
  http_server files lfd = server_with (λfd. http_handler files (fd, "")) lfd
End

Theorem wf_http_server:
  wf (http_server files lfd)
Proof
  simp[http_server_def] >> irule wf_server_with >> simp[wf_http_handler]
QED

Theorem settled_http_server:
  settled (http_server files lfd)
Proof
  simp[http_server_def] >> irule settled_server_with >>
  simp[wf_http_handler, settled_http_handler]
QED

(* ------------------------------------------------------------------------
   Safety
   ------------------------------------------------------------------------ *)

(* The intended responses to the complete requests at the front of s *)
Overload responses_to = “λfiles s. MAP (print_response o handle files) (parse_all s)”

(* MAIN: one connection.  The handler only reads and writes its own fd, and
   what it has written is a prefix of the responses to the complete requests
   in its buffer followed by everything it has read. *)
Theorem http_handler_serves:
  ∀hh buf.
    EVERY (on_fd fd) (trans (http_handler files (fd, buf)) hh) ∧
    written fd (trans (http_handler files (fd, buf)) hh) ≼
    responses_to files (buf ++ CONCAT (read fd (trans (http_handler files (fd, buf)) hh)))
Proof
  gen_tac >> measureInduct_on ‘LENGTH hh’ >> gen_tac >>
  ONCE_REWRITE_TAC[http_handler_unfold] >>
  Cases_on ‘parse_request buf’ >> simp[]
  >- ((* a complete request: write its response, continue with the rest *)
      rename1 ‘Complete req rest’ >>
      qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Write fd resp)) K0) hh’ >>
      qspecl_then [‘emit (Write fd resp)’, ‘K0’, ‘hh’] mp_tac
        (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases) >>
      simp[wf_emit, settled_emit] >> strip_tac
      >- (simp[trans_emit] >> drule parse_all_Complete >> simp[Abbr ‘resp’])
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, Abbr ‘K0’] >>
      first_x_assum (qspec_then ‘h2’ mp_tac) >> simp[] >>
      disch_then (qspec_then ‘rest’ strip_assume_tac) >> simp[] >>
      drule parse_extend >>
      disch_then (qspec_then ‘CONCAT (read fd (trans (http_handler files (fd, rest)) h2))’ assume_tac) >>
      drule parse_all_Complete >> simp[])
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
Theorem http_server_safety:
  fresh (trans (http_server files lfd) hh) ⇒
  ∀fd. written fd (trans (http_server files lfd) hh) ≼
       responses_to files (CONCAT (read fd (trans (http_server files lfd) hh)))
Proof
  rw[http_server_def] >>
  mp_tac (server_with_isolates
          |> INST_TYPE [alpha |-> “:unit”]
          |> INST [mk_var ("h", “:num -> (event, echoServer$response) snapshot list ->
                                 (action, unit option) asyncCore$outcome”) |->
                   “λfd. http_handler files (fd, "")”]
          |> BETA_RULE) >>
  impl_tac >- simp[http_handler_serves] >>
  disch_then drule >> strip_tac >>
  qpat_x_assum ‘∀fd. FILTER _ _ = _ ∨ _’ (qspec_then ‘fd’ strip_assume_tac) >>
  ONCE_REWRITE_TAC[GSYM written_FILTER, GSYM read_FILTER] >> simp[]
  >> qspecl_then [‘L’, ‘""’] mp_tac http_handler_serves
  >> simp[]
QED

(* MAIN: the same in HttpGetSpec's terms.  If what the server has read from fd
   is printed valid requests rs followed by a rest that does not start with
   a printed valid request, then what it has written to fd is a prefix of
   the printed responses to rs. *)
Theorem http_server_safety_requests:
  fresh (trans (http_server files lfd) hh) ∧
  CONCAT (read fd (trans (http_server files lfd) hh)) =
    FLAT (MAP print_request rs) ++ rest ∧
  EVERY valid_request rs ∧
  (∀r more. valid_request r ⇒ rest ≠ print_request r ++ more) ⇒
  written fd (trans (http_server files lfd) hh) ≼
  MAP (print_response o handle files) rs
Proof
  strip_tac >> drule http_server_safety >>
  disch_then (qspec_then ‘fd’ mp_tac) >> simp[parse_all_requests]
QED

(* ------------------------------------------------------------------------
   Sanity checks (EVAL)
   ------------------------------------------------------------------------ *)

Theorem example_parse_complete:
  parse_request "GET /a HTTP/1.0\r\n\r\nGET /b" = Complete (Get "/a") "GET /b"
Proof
  EVAL_TAC
QED

Theorem example_parse_incomplete:
  parse_request "GET /a HTTP/1.0\r\n" = Incomplete
Proof
  EVAL_TAC
QED

Theorem example_parse_invalid:
  parse_request "POST /a HTTP/1.0\r\n\r\n" = Invalid
Proof
  EVAL_TAC
QED

Definition hsnap_def:
  hsnap rdy res = <| ready := rdy; now := 0; results := res |>
End

(* A request arriving in two pieces: the handler reads twice, then writes
   the response to GET /a once the request is complete *)
Theorem example_two_piece_request:
  trans (http_handler [("/a", "hi")] (4, ""))
        [hsnap {Readable 4} []; hsnap {} [Data "GET /a HTTP/1.0\r\n"];
         hsnap {Readable 4} []; hsnap {} [Data "\r\n"]] =
  [(Read 4, SOME (Data "GET /a HTTP/1.0\r\n")); (Read 4, SOME (Data "\r\n"));
   (Write 4 "HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nhi", NONE)]
Proof
  EVAL_TAC
QED
