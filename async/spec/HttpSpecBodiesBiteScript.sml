(*
  HttpSpecBodies bites: the bodies variant rules out plausible bugs, its
  assumptions are satisfiable, and it extends HttpSpecHeaders.  Everything
  here is proved.  DRAFT, for the user's decision.

  - Framing is unique (print_brequest_unique): a printed valid request
    followed by anything determines the request, hence where its body ends.
    So the Content-Length framing is the only reading the spec accepts.
  - Bodiless GET requests without Content-Length / Transfer-Encoding are
    exactly HttpSpecHeaders' requests (same validity, bytes, responses).
  - Real clients are in: the request `curl -d hello .../echo` sends.
  - Broken servers: treating body bytes as the next request, answering
    before the whole body has arrived, and never answering each violate
    the spec.
  - Non-vacuity: in the fair world where one client sends a POST /echo
    whose body looks like a request, the ideal trace is safe and live.
*)
Theory HttpSpecBodiesBite
Ancestors
  HttpSpecBodies HttpSpecHeaders HttpSpec HttpSpecBite EchoSpec EchoSpecBite
  ffiSpikeSocketFFI ffiSpikeSocketFair llist alist Marshalling ASCIInumbers
Libs
  preamble

Overload site = “[("/a", "hi")] : (string # string) list”

(* A POST /echo whose 19-byte body is itself a printed request *)
Overload looks_like_request = “"GET /a HTTP/1.0\r\n\r\n"”
Overload rp = “Req "POST" "/echo" "1.1" [("Content-Length", "19")] looks_like_request”

(* ------------------------------------------------------------------------
   HttpSpecHeaders is the bodiless case
   ------------------------------------------------------------------------ *)

(* HttpSpecHeaders' header lines are valid here *)
Theorem valid_header_bheader:
  valid_header h ⇒ valid_bheader h
Proof
  PairCases_on ‘h’ >> simp[valid_header_def, valid_bheader_def]
QED

(* MAIN (compatibility): a request of HttpSpecHeaders without
   Content-Length or Transfer-Encoding headers is a bodiless GET request
   here, with the same bytes and the same response *)
Theorem bodiless_requests:
  valid_hrequest (GetH p ver hs) ∧ ¬EXISTS is_cl hs ∧ ¬EXISTS is_te hs ⇒
  valid_brequest (Req "GET" p ver hs "") ∧
  print_brequest (Req "GET" p ver hs "") = print_hrequest (GetH p ver hs) ∧
  bhandle files (Req "GET" p ver hs "") = handle files (hpath (GetH p ver hs))
Proof
  rw[valid_brequest_def, valid_hrequest_def, valid_method_def, framed_def,
     print_brequest_def, print_hrequest_def, bhandle_def, hpath_def]
  >- (fs[EVERY_MEM] >> metis_tac[valid_header_bheader]) >>
  ‘FILTER is_cl hs = []’ by (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  simp[]
QED

(* MAIN (real clients are in): curl -d hello http://localhost:7777/echo *)
Theorem curl_post_request:
  let r = Req "POST" "/echo" "1.1"
            [("Host", "localhost:7777"); ("User-Agent", "curl/8.7.1");
             ("Accept", "*/*"); ("Content-Length", "5");
             ("Content-Type", "application/x-www-form-urlencoded")] "hello" in
  valid_brequest r ∧
  print_brequest r =
    "POST /echo HTTP/1.1\r\nHost: localhost:7777\r\nUser-Agent: curl/8.7.1\r\n" ++
    "Accept: */*\r\nContent-Length: 5\r\n" ++
    "Content-Type: application/x-www-form-urlencoded\r\n\r\nhello" ∧
  bhandle site r = Ok "hello"
Proof
  EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Framing is unique
   ------------------------------------------------------------------------ *)

Theorem split_char[local]:
  ∀a b s t. ¬MEM c a ∧ ¬MEM c b ∧ a ++ c :: s = b ++ c :: t ⇒ a = b ∧ s = t
Proof
  Induct >> Cases_on ‘b’ >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem headers_unique[local]:
  ∀hs1 hs2 x y.
    EVERY valid_bheader hs1 ∧ EVERY valid_bheader hs2 ∧
    FLAT (MAP print_header hs1) ++ "\r\n" ++ x =
    FLAT (MAP print_header hs2) ++ "\r\n" ++ y ⇒
    hs1 = hs2 ∧ x = y
Proof
  Induct
  >- (Cases >> simp[] >> PairCases_on ‘h’ >>
      simp[print_header_def, valid_bheader_def] >> Cases_on ‘h0’ >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  PairCases >> Cases >> simp[]
  >- (simp[print_header_def, valid_bheader_def] >> Cases_on ‘h0’ >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  PairCases_on ‘h’ >> simp[print_header_def, valid_bheader_def] >>
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

Theorem framed_length[local]:
  framed hs b1 ∧ framed hs b2 ⇒ LENGTH b1 = LENGTH b2
Proof
  rw[framed_def] >> Cases_on ‘FILTER is_cl hs’ >> gvs[] >>
  Cases_on ‘t’ >> gvs[] >> PairCases_on ‘h’ >> gvs[toString_11]
QED

Theorem method_unique[local]:
  valid_method m1 ∧ valid_method m2 ∧
  m1 ++ #" " :: x = m2 ++ #" " :: y ⇒ m1 = m2 ∧ x = y
Proof
  rw[valid_method_def] >> gvs[]
QED

(* MAIN (framing): a printed valid request followed by anything determines
   the request and the rest; in particular where the body ends *)
Theorem print_brequest_unique:
  valid_brequest q1 ∧ valid_brequest q2 ∧
  print_brequest q1 ++ x = print_brequest q2 ++ y ⇒ q1 = q2 ∧ x = y
Proof
  Cases_on ‘q1’ >> Cases_on ‘q2’ >>
  REWRITE_TAC[valid_brequest_def, valid_path_def, print_brequest_def] >>
  strip_tac >>
  rename1 ‘Req m1 p1 v1 hs1 b1 = Req m2 p2 v2 hs2 b2’ >>
  ‘m1 = m2 ∧ p1 ++ " HTTP/" ++ v1 ++ "\r\n" ++ FLAT (MAP print_header hs1) ++
             "\r\n" ++ b1 ++ x =
             p2 ++ " HTTP/" ++ v2 ++ "\r\n" ++ FLAT (MAP print_header hs2) ++
             "\r\n" ++ b2 ++ y’
    by (irule method_unique >> simp[] >>
        qpat_x_assum ‘_ = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ‘p1 = p2 ∧ "HTTP/" ++ v1 ++ "\r\n" ++ FLAT (MAP print_header hs1) ++ "\r\n" ++ b1 ++ x =
             "HTTP/" ++ v2 ++ "\r\n" ++ FLAT (MAP print_header hs2) ++ "\r\n" ++ b2 ++ y’
    by (irule split_char >> qexists_tac ‘#" "’ >> rpt conj_tac
        >- (fs[EVERY_MEM] >> metis_tac[])
        >- (fs[EVERY_MEM] >> metis_tac[]) >>
        qpat_x_assum ‘_ = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, CONS_11]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ‘v1 = v2 ∧ FLAT (MAP print_header hs1) ++ "\r\n" ++ (b1 ++ x) =
             FLAT (MAP print_header hs2) ++ "\r\n" ++ (b2 ++ y)’
    by (qpat_x_assum ‘valid_version v1’ mp_tac >>
        qpat_x_assum ‘valid_version v2’ mp_tac >>
        rw[valid_version_def] >>
        qpat_x_assum ‘_ = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, CONS_11] >> simp[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule_all headers_unique >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  ‘LENGTH b1 = LENGTH b2’ by metis_tac[framed_length] >>
  ‘b1 ++ x = b2 ++ y’ by fs[] >>
  ‘TAKE (LENGTH b1) (b1 ++ x) = TAKE (LENGTH b2) (b2 ++ y) ∧
   DROP (LENGTH b1) (b1 ++ x) = DROP (LENGTH b2) (b2 ++ y)’ by metis_tac[] >>
  fs[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

(* ------------------------------------------------------------------------
   Bytes
   ------------------------------------------------------------------------ *)

Theorem bytes_split[local]:
  ∀s p rest. bytes p ++ rest = bytes s ⇒ ∃s'. s = p ++ s' ∧ rest = bytes s'
Proof
  simp[bytes_def] >> Induct_on ‘p’ >> rw[] >>
  Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem brequests_CONS[local]:
  brequests [] = [] ∧
  brequests (r :: rs) = bytes (print_brequest r) ++ brequests rs
Proof
  simp[brequests_def, bytes_def]
QED

Theorem print_brequest_NIL[local]:
  print_brequest r ≠ []
Proof
  Cases_on ‘r’ >> simp[print_brequest_def]
QED

Theorem brequests_NIL[local]:
  brequests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[brequests_CONS, bytes_def, print_brequest_NIL]
QED

Theorem no_full_brequest_NIL[local]:
  no_full_brequest []
Proof
  rw[no_full_brequest_def, brequests_NIL]
QED

(* The only valid request list whose bytes, followed by a rest, are the
   bytes of r is [r] with an empty rest (or []) *)
Theorem brequests_of_one[local]:
  valid_brequest r ∧ EVERY valid_brequest rs ∧
  brequests rs ++ rest = brequests [r] ⇒
  rs = [] ∨ (rs = [r] ∧ rest = [])
Proof
  Cases_on ‘rs’ >> rw[] >> fs[brequests_CONS] >>
  ‘bytes (print_brequest h) ++ (brequests t ++ rest) = bytes (print_brequest r)’
    by fs[] >>
  drule bytes_split >> strip_tac >>
  ‘h = r ∧ s' = []’
    by (irule print_brequest_unique >> fs[]) >>
  qpat_x_assum ‘print_brequest r = _’ kall_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[bytes_def, APPEND_eq_NIL, brequests_NIL]
QED

(* ------------------------------------------------------------------------
   Broken servers violate the spec
   ------------------------------------------------------------------------ *)

(* MAIN (framing bite): a server that treats the body bytes as the next
   request (here: answers the request-looking body GET /a with /a's file)
   violates safety.  The client sent exactly one request, rp. *)
Theorem broken_body_as_request:
  starts_with [rd c1 (brequests [rp]) 100;
               wr c1 (bytes (print_response (Ok "hi")))] io ⇒
  ¬http_safe_b site io
Proof
  rw[http_safe_b_def] >>
  qexistsl [‘[rd c1 (brequests [rp]) 100; wr c1 (bytes (print_response (Ok "hi")))]’,
            ‘c1’, ‘[rp]’, ‘[]’] >>
  simp[no_full_brequest_NIL] >> EVAL_TAC
QED

(* rp with the last byte of its body missing *)
Overload partial_b = “bytes (FRONT (print_brequest rp))”

Theorem no_full_brequest_partial[local]:
  no_full_brequest partial_b
Proof
  rw[no_full_brequest_def, IS_PREFIX_APPEND] >> strip_tac >>
  fs[brequests_CONS] >>
  drule bytes_split >> strip_tac >>
  ‘print_brequest r ++ (s' ++ "\n") = print_brequest rp ++ []’
    by (qpat_x_assum ‘FRONT _ = _’ (mp_tac o SYM) >> EVAL_TAC >> simp[]) >>
  ‘valid_brequest rp’ by EVAL_TAC >>
  drule_all print_brequest_unique >> simp[]
QED

(* MAIN (bite): a server that answers before the whole body has arrived
   violates safety *)
Theorem broken_answers_before_body:
  starts_with [rd c1 partial_b 100; wr c1 (bresponses site [rp])] io ⇒
  ¬http_safe_b site io
Proof
  rw[http_safe_b_def] >>
  qexistsl [‘[rd c1 partial_b 100; wr c1 (bresponses site [rp])]’,
            ‘c1’, ‘[]’, ‘partial_b’] >>
  simp[no_full_brequest_partial] >> EVAL_TAC
QED

Theorem sent_upto_one_client[local]:
  sent_upto c n (one_client bs) = if n = 0 ∨ c ≠ 4w then [] else bs
Proof
  Cases_on ‘n’ >> simp[sent_upto_def, arrivals_upto_def, one_client_def] >>
  Cases_on ‘n'’ >> simp[arrivals_upto_def] >> rw[]
QED

(* MAIN (bite): a server that never answers violates liveness *)
Theorem broken_never_answers_b:
  (∀evs. starts_with evs io ⇒ bytes_written_to 4w evs = []) ⇒
  ¬http_live_b site (one_client (brequests [rp])) io
Proof
  rw[http_live_b_def] >> qexistsl [‘4w’, ‘1’, ‘[rp]’] >>
  simp[sent_upto_one_client] >> conj_tac >- EVAL_TAC >>
  rw[] >> Cases_on ‘LPREFIX (fromList evs) io’ >> simp[] >> res_tac >>
  simp[] >> EVAL_TAC
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

Overload ideal_b = “[rd c1 (brequests [rp]) 100; wr c1 (bresponses site [rp])]”

Theorem ideal_events_b[local]:
  event_read c (rd c1 (brequests [rp]) 100) =
    (if c = c1 then brequests [rp] else []) ∧
  event_written c (rd c1 (brequests [rp]) 100) = [] ∧
  event_read c (wr c1 (bresponses site [rp])) = [] ∧
  event_written c (wr c1 (bresponses site [rp])) =
    (if c = c1 then bresponses site [rp] else [])
Proof
  rw[] >> EVAL_TAC >> rw[] >> fs[]
QED

Theorem ideal_b_safe:
  http_safe_b site (fromList ideal_b)
Proof
  rw[http_safe_b_def, LPREFIX_fromList_fromList, prefix_two] >>
  gvs[bytes_read_from_def, bytes_written_to_def, ideal_events_b] >>
  Cases_on ‘c = c1’ >> gvs[] >>
  TRY (gvs[brequests_NIL, APPEND_eq_NIL, bresponses_def] >> NO_TAC) >>
  ‘valid_brequest rp’ by EVAL_TAC >>
  ‘brequests rs ++ rest = brequests [rp]’ by simp[] >>
  drule_all brequests_of_one >> rw[] >> gvs[] >>
  fs[no_full_brequest_def] >>
  first_x_assum (qspec_then ‘rp’ mp_tac) >> fs[brequests_CONS]
QED

Theorem ideal_b_live:
  http_live_b site (one_client (brequests [rp])) (fromList ideal_b)
Proof
  rw[http_live_b_def, sent_upto_one_client] >>
  ‘valid_brequest rp’ by EVAL_TAC >>
  Cases_on ‘c = 4w ∧ n ≠ 0’ >> gvs[]
  >- (fs[IS_PREFIX_APPEND] >> drule_all brequests_of_one >> rw[]
      >- (qexists_tac ‘[]’ >> simp[bresponses_def, bytes_def, bytes_written_to_def])
      >- (qexists_tac ‘ideal_b’ >>
          simp[LPREFIX_fromList_fromList, bytes_written_to_def, ideal_events_b])) >>
  gvs[brequests_NIL] >> qexists_tac ‘[]’ >>
  simp[bresponses_def, bytes_def, bytes_written_to_def]
QED

(* MAIN (non-vacuity): a fair world in which one client sends a POST /echo
   whose body looks like a request exists, and the ideal trace in it
   (read the request, write the echoed body) is safe and live *)
Theorem ideal_b_trace_safe_and_live:
  server_world 3w (one_client (brequests [rp])) ∧
  http_safe_b site (fromList ideal_b) ∧
  http_live_b site (one_client (brequests [rp])) (fromList ideal_b)
Proof
  simp[server_world_one_client, ideal_b_safe, ideal_b_live]
QED
