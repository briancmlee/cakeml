(*
  HttpSpecHeaders bites: the header-tolerant variant rules out plausible
  bugs, its assumptions are satisfiable, and it extends HttpSpec.
  Everything here is proved.  DRAFT, for the user's decision.

  - Backward compatibility: HttpSpec's requests are the requests with no
    headers and version 1.0 (same bytes, same responses).
  - Real clients are in: the request curl sends by default is a printed
    valid request.
  - Requests read back uniquely (print_hrequest_unique), so a run's
    reads decompose into requests in at most one way.
  - Broken servers: letting a header change the response, answering
    before the blank line that ends the headers, answering a request that
    carries a body-framing header (Content-Length; there are no request
    bodies in this subset), and never answering each violate the spec.
  - Non-vacuity: in the fair world where one client sends a request with a
    header, the ideal trace (read it, write its response) is safe and live.
*)
Theory HttpSpecHeadersBite
Ancestors
  HttpSpecHeaders HttpSpec HttpSpecBite EchoSpec EchoSpecBite
  ffiSpikeSocketFFI ffiSpikeSocketFair llist alist Marshalling ASCIInumbers
Libs
  preamble

Overload site = “[("/a", "hi")] : (string # string) list”
(* a request for /a with one header, and one for /b *)
Overload ra = “GetH "/a" "1.1" [("Host", "x")]”
Overload rb = “GetH "/b" "1.1" [("Host", "x")]”

(* ------------------------------------------------------------------------
   HttpSpec is the special case of no headers, version 1.0
   ------------------------------------------------------------------------ *)

Definition plain_def:
  plain (Get p) = GetH p "1.0" []
End

(* MAIN (backward compatibility): an HttpSpec request is a header-tolerant
   request with no headers and version 1.0: same validity, same bytes,
   same responses *)
Theorem plain_requests:
  (valid_hrequest (plain r) ⇔ valid_request r) ∧
  hrequests (MAP plain rs) = requests rs ∧
  hresponses files (MAP plain rs) = responses files rs
Proof
  rpt conj_tac
  >- (Cases_on ‘r’ >> simp[plain_def, valid_hrequest_def, valid_request_def,
                           valid_version_def])
  >- (simp[hrequests_def, requests_def] >> AP_TERM_TAC >>
      Induct_on ‘rs’ >> simp[] >> Cases >>
      simp[plain_def, print_hrequest_def, print_request_def])
  >> simp[hresponses_def, responses_def] >> AP_TERM_TAC >>
  Induct_on ‘rs’ >> simp[] >> Cases >> simp[plain_def, hpath_def]
QED

(* MAIN (real clients are in): the request curl 8 sends by default *)
Theorem curl_request:
  let r = GetH "/" "1.1" [("Host", "localhost:7777");
                          ("User-Agent", "curl/8.7.1"); ("Accept", "*/*")] in
  valid_hrequest r ∧
  print_hrequest r =
    "GET / HTTP/1.1\r\nHost: localhost:7777\r\nUser-Agent: curl/8.7.1\r\nAccept: */*\r\n\r\n"
Proof
  EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Requests read back uniquely
   ------------------------------------------------------------------------ *)

(* Splitting at the first occurrence of a character *)
Theorem split_char[local]:
  ∀a b s t. ¬MEM c a ∧ ¬MEM c b ∧ a ++ c :: s = b ++ c :: t ⇒ a = b ∧ s = t
Proof
  Induct >> Cases_on ‘b’ >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem headers_unique[local]:
  ∀hs1 hs2 x y.
    EVERY valid_header hs1 ∧ EVERY valid_header hs2 ∧
    FLAT (MAP print_header hs1) ++ "\r\n" ++ x =
    FLAT (MAP print_header hs2) ++ "\r\n" ++ y ⇒
    hs1 = hs2 ∧ x = y
Proof
  Induct
  >- (Cases >> simp[] >> PairCases_on ‘h’ >>
      simp[print_header_def, valid_header_def] >> Cases_on ‘h0’ >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  PairCases >> Cases >> simp[]
  >- (simp[print_header_def, valid_header_def] >> Cases_on ‘h0’ >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  PairCases_on ‘h’ >> simp[print_header_def, valid_header_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘_ = _’ mp_tac >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> strip_tac >>
  ‘h0 = h0' ∧ " " ++ h1 ++ "\r\n" ++ FLAT (MAP print_header hs1) ++ "\r\n" ++ x =
              " " ++ h1' ++ "\r\n" ++ FLAT (MAP print_header t) ++ "\r\n" ++ y’
    by (irule split_char >> qexists_tac ‘#":"’ >> fs[EVERY_MEM] >>
        rpt strip_tac >> res_tac >> fs[] >>
        qpat_x_assum ‘_ = _’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
        simp[]) >>
  gvs[] >>
  qpat_x_assum ‘_ = _’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  strip_tac >>
  ‘h1 = h1' ∧ "\n" ++ FLAT (MAP print_header hs1) ++ "\r\n" ++ x =
              "\n" ++ FLAT (MAP print_header t) ++ "\r\n" ++ y’
    by (irule split_char >> qexists_tac ‘#"\r"’ >> fs[EVERY_MEM] >>
        rpt strip_tac >> res_tac >> fs[] >>
        qpat_x_assum ‘_ = _’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
        simp[]) >>
  gvs[] >> first_x_assum irule >> simp[]
QED

(* MAIN (helper): a printed valid request followed by anything determines
   the request and the rest *)
Theorem print_hrequest_unique:
  valid_hrequest q1 ∧ valid_hrequest q2 ∧
  print_hrequest q1 ++ x = print_hrequest q2 ++ y ⇒ q1 = q2 ∧ x = y
Proof
  Cases_on ‘q1’ >> Cases_on ‘q2’ >>
  REWRITE_TAC[valid_hrequest_def, valid_path_def, print_hrequest_def] >>
  strip_tac >>
  rename1 ‘GetH p1 v1 hs1 = GetH p2 v2 hs2’ >>
  ‘p1 = p2 ∧ "HTTP/" ++ v1 ++ "\r\n" ++ FLAT (MAP print_header hs1) ++ "\r\n" ++ x =
             "HTTP/" ++ v2 ++ "\r\n" ++ FLAT (MAP print_header hs2) ++ "\r\n" ++ y’
    by (irule split_char >> qexists_tac ‘#" "’ >> rpt conj_tac
        >- (fs[EVERY_MEM] >> metis_tac[])
        >- (fs[EVERY_MEM] >> metis_tac[]) >>
        qpat_x_assum ‘_ = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, CONS_11]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ‘v1 = v2 ∧ FLAT (MAP print_header hs1) ++ "\r\n" ++ x =
             FLAT (MAP print_header hs2) ++ "\r\n" ++ y’
    by (qpat_x_assum ‘valid_version v1’ mp_tac >>
        qpat_x_assum ‘valid_version v2’ mp_tac >>
        rw[valid_version_def] >>
        qpat_x_assum ‘_ = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, CONS_11] >> simp[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule_all headers_unique >> simp[]
QED

(* ------------------------------------------------------------------------
   Bytes
   ------------------------------------------------------------------------ *)

Theorem bytes_11[local]:
  ∀s t. bytes s = bytes t ⇔ s = t
Proof
  simp[bytes_def] >> Induct >> Cases_on ‘t’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> simp[ORD_11]
QED

Theorem bytes_split[local]:
  ∀s p rest. bytes p ++ rest = bytes s ⇒ ∃s'. s = p ++ s' ∧ rest = bytes s'
Proof
  simp[bytes_def] >> Induct_on ‘p’ >> rw[] >>
  Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem hrequests_CONS[local]:
  hrequests [] = [] ∧
  hrequests (r :: rs) = bytes (print_hrequest r) ++ hrequests rs
Proof
  simp[hrequests_def, bytes_def]
QED

Theorem print_hrequest_NIL[local]:
  print_hrequest r ≠ []
Proof
  Cases_on ‘r’ >> simp[print_hrequest_def]
QED

Theorem hrequests_NIL[local]:
  hrequests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[hrequests_CONS, bytes_def, print_hrequest_NIL]
QED

Theorem no_full_hrequest_NIL[local]:
  no_full_hrequest []
Proof
  rw[no_full_hrequest_def, hrequests_NIL]
QED

(* The only valid request list whose bytes, followed by a rest, are the
   bytes of r is [r] with an empty rest (or []) *)
Theorem hrequests_of_one[local]:
  valid_hrequest r ∧ EVERY valid_hrequest rs ∧
  hrequests rs ++ rest = hrequests [r] ⇒
  rs = [] ∨ (rs = [r] ∧ rest = [])
Proof
  Cases_on ‘rs’ >> rw[] >> fs[hrequests_CONS] >>
  ‘bytes (print_hrequest h) ++ (hrequests t ++ rest) = bytes (print_hrequest r)’
    by fs[] >>
  drule bytes_split >> strip_tac >>
  ‘h = r ∧ s' = []’
    by (irule print_hrequest_unique >> fs[]) >>
  qpat_x_assum ‘print_hrequest r = _’ kall_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[bytes_def, APPEND_eq_NIL, hrequests_NIL]
QED

(* ------------------------------------------------------------------------
   Broken servers violate the spec
   ------------------------------------------------------------------------ *)

(* MAIN (bite): a server that lets a header change the response (here,
   answers a request for the missing /b with /a's file) violates safety *)
Theorem broken_header_changes_response:
  starts_with [rd c1 (hrequests [rb]) 100;
               wr c1 (bytes (print_response (Ok "hi")))] io ⇒
  ¬http_safe_h site io
Proof
  rw[http_safe_h_def] >>
  qexistsl [‘[rd c1 (hrequests [rb]) 100; wr c1 (bytes (print_response (Ok "hi")))]’,
            ‘c1’, ‘[rb]’, ‘[]’] >>
  simp[no_full_hrequest_NIL] >> EVAL_TAC
QED

(* A request whose headers have not been ended by a blank line yet *)
Overload partial_h = “bytes "GET /a HTTP/1.1\r\nHost: x\r\n"”

Theorem no_full_hrequest_partial[local]:
  no_full_hrequest partial_h
Proof
  rw[no_full_hrequest_def, IS_PREFIX_APPEND] >> strip_tac >>
  fs[hrequests_CONS] >>
  drule bytes_split >> strip_tac >>
  ‘print_hrequest r ++ (s' ++ "\r\n") = print_hrequest ra ++ []’
    by (gvs[] >> EVAL_TAC >> simp[]) >>
  ‘valid_hrequest ra’ by EVAL_TAC >>
  drule_all print_hrequest_unique >> simp[]
QED

(* MAIN (bite): a server that answers before the blank line ending the
   headers has arrived violates safety *)
Theorem broken_answers_before_blank_line:
  starts_with [rd c1 partial_h 100; wr c1 (hresponses site [ra])] io ⇒
  ¬http_safe_h site io
Proof
  rw[http_safe_h_def] >>
  qexistsl [‘[rd c1 partial_h 100; wr c1 (hresponses site [ra])]’,
            ‘c1’, ‘[]’, ‘partial_h’] >>
  simp[no_full_hrequest_partial] >> EVAL_TAC
QED

Theorem sent_upto_one_client[local]:
  sent_upto c n (one_client bs) = if n = 0 ∨ c ≠ 4w then [] else bs
Proof
  Cases_on ‘n’ >> simp[sent_upto_def, arrivals_upto_def, one_client_def] >>
  Cases_on ‘n'’ >> simp[arrivals_upto_def] >> rw[]
QED

(* MAIN (bite): a server that never answers a client sending a request
   with a header violates liveness *)
Theorem broken_never_answers_h:
  (∀evs. starts_with evs io ⇒ bytes_written_to 4w evs = []) ⇒
  ¬http_live_h site (one_client (hrequests [ra])) io
Proof
  rw[http_live_h_def] >> qexistsl [‘4w’, ‘1’, ‘[ra]’] >>
  simp[sent_upto_one_client] >> conj_tac >- EVAL_TAC >>
  rw[] >> Cases_on ‘LPREFIX (fromList evs) io’ >> simp[] >> res_tac >>
  simp[] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   No request bodies
   ------------------------------------------------------------------------ *)

(* MAIN (no bodies): body-framing headers are not valid header lines, in
   any letter case; ordinary headers are *)
Theorem body_headers_invalid:
  ¬valid_header ("Content-Length", "0") ∧
  ¬valid_header ("content-length", "0") ∧
  ¬valid_header ("Transfer-Encoding", "chunked") ∧
  ¬valid_header ("TRANSFER-ENCODING", "chunked") ∧
  valid_header ("Host", "x") ∧ valid_header ("Content-Type", "text/plain")
Proof
  EVAL_TAC
QED

(* a GET carrying Content-Length (with an empty body) *)
Overload rcl = “GetH "/a" "1.1" [("Content-Length", "0")]”

(* No valid request is a prefix of it: the only header name it could
   start with is Content-Length *)
Theorem no_valid_prefix_rcl[local]:
  valid_hrequest r ∧ print_hrequest r ++ x = print_hrequest rcl ⇒ F
Proof
  Cases_on ‘r’ >> rename1 ‘GetH p v hs’ >>
  REWRITE_TAC[valid_hrequest_def, valid_path_def, print_hrequest_def] >>
  strip_tac >>
  ‘p = "/a" ∧ "HTTP/" ++ v ++ "\r\n" ++ FLAT (MAP print_header hs) ++ "\r\n" ++ x =
              "HTTP/1.1\r\nContent-Length: 0\r\n\r\n"’
    by (irule split_char >> qexists_tac ‘#" "’ >>
        conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
        conj_tac >- EVAL_TAC >>
        qpat_x_assum ‘_ = _’ mp_tac >> simp[print_header_def]) >>
  ‘FLAT (MAP print_header hs) ++ "\r\n" ++ x = "Content-Length: 0\r\n\r\n"’
    by (qpat_x_assum ‘valid_version v’ mp_tac >> rw[valid_version_def] >>
        qpat_x_assum ‘_ = "HTTP/1.1\r\nContent-Length: 0\r\n\r\n"’ mp_tac >>
        simp[]) >>
  Cases_on ‘hs’ >> fs[] >>
  PairCases_on ‘h’ >> fs[print_header_def, valid_header_def] >>
  ‘h0 = "Content-Length"’
    by (qspecl_then [‘h0’, ‘"Content-Length"’] mp_tac
          (INST_TYPE [alpha |-> “:char”] split_char |> Q.INST [‘c’ |-> ‘#":"’]) >>
        disch_then (qspecl_then
          [‘" " ++ h1 ++ "\r\n" ++ FLAT (MAP print_header t) ++ "\r\n" ++ x’,
           ‘" 0\r\n\r\n"’] mp_tac) >>
        impl_tac
        >- (rpt conj_tac
            >- (fs[EVERY_MEM] >> strip_tac >> res_tac >> fs[])
            >- EVAL_TAC >>
            qpat_x_assum ‘_ = "Content-Length: 0\r\n\r\n"’ mp_tac >> simp[]) >>
        simp[]) >>
  qpat_x_assum ‘¬body_header _’ mp_tac >> simp[] >> EVAL_TAC
QED

Theorem no_full_hrequest_rcl[local]:
  no_full_hrequest (hrequests [rcl])
Proof
  rw[no_full_hrequest_def, IS_PREFIX_APPEND] >> strip_tac >>
  fs[hrequests_CONS] >> drule bytes_split >> strip_tac >>
  metis_tac[no_valid_prefix_rcl]
QED

(* MAIN (bite): a server that answers a GET carrying a body-framing header
   (here Content-Length) violates safety: the subset has no request
   bodies, so such a request is never answered *)
Theorem broken_answers_body_request:
  starts_with [rd c1 (hrequests [rcl]) 100;
               wr c1 (bytes (print_response (Ok "hi")))] io ⇒
  ¬http_safe_h site io
Proof
  rw[http_safe_h_def] >>
  qexistsl [‘[rd c1 (hrequests [rcl]) 100; wr c1 (bytes (print_response (Ok "hi")))]’,
            ‘c1’, ‘[]’, ‘hrequests [rcl]’] >>
  simp[no_full_hrequest_rcl] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Non-vacuity
   ------------------------------------------------------------------------ *)

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

Theorem prefix_two[local]:
  evs ≼ [x; y] ⇔ evs = [] ∨ evs = [x] ∨ evs = [x; y]
Proof
  Cases_on ‘evs’ >> simp[] >> Cases_on ‘t’ >> simp[] >>
  Cases_on ‘t'’ >> simp[]
QED

Overload ideal_h = “[rd c1 (hrequests [ra]) 100; wr c1 (hresponses site [ra])]”

Theorem ideal_events_h[local]:
  event_read c (rd c1 (hrequests [ra]) 100) =
    (if c = c1 then hrequests [ra] else []) ∧
  event_written c (rd c1 (hrequests [ra]) 100) = [] ∧
  event_read c (wr c1 (hresponses site [ra])) = [] ∧
  event_written c (wr c1 (hresponses site [ra])) =
    (if c = c1 then hresponses site [ra] else [])
Proof
  rw[] >> EVAL_TAC >> rw[] >> fs[]
QED

Theorem ideal_h_safe:
  http_safe_h site (fromList ideal_h)
Proof
  rw[http_safe_h_def, LPREFIX_fromList_fromList, prefix_two] >>
  gvs[bytes_read_from_def, bytes_written_to_def, ideal_events_h] >>
  Cases_on ‘c = c1’ >> gvs[] >>
  TRY (gvs[hrequests_NIL, APPEND_eq_NIL, hresponses_def] >> NO_TAC) >>
  ‘valid_hrequest ra’ by EVAL_TAC >>
  ‘hrequests rs ++ rest = hrequests [ra]’ by simp[] >>
  drule_all hrequests_of_one >> rw[] >> gvs[] >>
  fs[no_full_hrequest_def] >>
  first_x_assum (qspec_then ‘ra’ mp_tac) >> fs[hrequests_CONS]
QED

Theorem ideal_h_live:
  http_live_h site (one_client (hrequests [ra])) (fromList ideal_h)
Proof
  rw[http_live_h_def, sent_upto_one_client] >>
  ‘valid_hrequest ra’ by EVAL_TAC >>
  Cases_on ‘c = 4w ∧ n ≠ 0’ >> gvs[]
  >- (fs[IS_PREFIX_APPEND] >> drule_all hrequests_of_one >> rw[]
      >- (qexists_tac ‘[]’ >> simp[hresponses_def, bytes_def, bytes_written_to_def])
      >- (qexists_tac ‘ideal_h’ >>
          simp[LPREFIX_fromList_fromList, bytes_written_to_def, ideal_events_h])) >>
  gvs[hrequests_NIL] >> qexists_tac ‘[]’ >>
  simp[hresponses_def, bytes_def, bytes_written_to_def]
QED

(* MAIN (non-vacuity): a fair world in which one client sends a request
   with a header exists, and the ideal trace in it is safe and live *)
Theorem ideal_h_trace_safe_and_live:
  server_world 3w (one_client (hrequests [ra])) ∧
  http_safe_h site (fromList ideal_h) ∧
  http_live_h site (one_client (hrequests [ra])) (fromList ideal_h)
Proof
  simp[server_world_one_client, ideal_h_safe, ideal_h_live]
QED
