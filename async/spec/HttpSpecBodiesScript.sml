(*
  HttpSpecBodies: HttpSpecHeaders with request BODIES, framed by
  Content-Length.  DRAFT, for the user's decision.  HttpSpec and
  HttpSpecHeaders are unchanged; this file reuses their definitions.

  A request is

     <method> <path> HTTP/<1.0|1.1>\r\n      method GET or POST
     <name>: <value>\r\n                     any number of header lines
     \r\n
     <body>                                  exactly n octets

  where n is the value of the request's single Content-Length header (a
  case-insensitive name; the value in decimal, as num_to_dec_string prints
  it), or 0 if there is none.  A request with two Content-Length headers,
  or with any Transfer-Encoding header, is not valid.

  What the server answers:
    GET p             as HttpSpec: the file p, or 404 (headers and body ignored)
    POST /echo        200 with the request's body
    POST p (other)    404

  Header lines have their own validity, valid_bheader: the name is an
  RFC 9110 token (tchar characters only), the value has no CR or LF.  So
  "Content-Length\t: 19" is not a valid header line, and a request
  containing it is not valid (it does not silently become a bodiless
  request followed by its body as a second request).  Everything else is
  HttpSpecHeaders': the printer for header lines, the world, the
  projections, and the shapes of safety, liveness and the statement.

  Paths are made of RFC 3986 characters (uri_char) and header values of
  RFC 9110 field characters (field_char), so every valid request is one
  that an RFC 9112 recipient frames (spec-rfc/: the agreement proof).

  Known limitation: "Expect: 100-continue" is not supported.  Safety
  forbids interim 1xx responses, so a client that sends it (curl, for
  large bodies) waits about a second and then sends the body anyway.
*)
Theory HttpSpecBodies
Ancestors
  EchoSpec HttpSpec HttpSpecHeaders
Libs
  preamble

(* ------------------------------------------------------------------------
   Requests with bodies
   ------------------------------------------------------------------------ *)

Datatype:
  brequest = Req string string string ((string # string) list) string
                              (* method, path, version, headers, body *)
End

(* RFC 9110 token characters (tchar): letters, digits, and
   ! # $ % & ' * + - . ^ _ ` | ~   (^ and ` are CHR 94 and CHR 96) *)
Definition tchar_def:
  tchar c ⇔
    isAlpha c ∨ isDigit c ∨ EXISTS (λd. c = d) "!#$%&'*+-._|~" ∨
    c = CHR 94 ∨ c = CHR 96
End

(* RFC 9110 §5.5 field-value characters: VCHAR (%x21-7E), obs-text
   (%x80-FF), SP and HTAB; no other control characters (no CR, LF, NUL) *)
Definition field_char_def:
  field_char c ⇔
    (33 ≤ ORD c ∧ ORD c ≤ 126) ∨ 128 ≤ ORD c ∨ c = #" " ∨ c = #"\t"
End

(* RFC 3986 §2 characters of a request target: unreserved, reserved and
   "%" (no "#", no space, no control characters) *)
Definition uri_char_def:
  uri_char c ⇔
    isAlpha c ∨ isDigit c ∨ EXISTS (λd. c = d) "-._~:/?[]@!$&'()*+,;=%"
End

(* Header lines: the name is a token (non-empty, tchar only); the value is
   made of field characters (so, in particular, no CR or LF: a request is
   unambiguous) *)
Definition valid_bheader_def:
  valid_bheader (n, v) ⇔ n ≠ [] ∧ EVERY tchar n ∧ EVERY field_char v
End

(* Token characters exclude the separators the framing relies on *)
Theorem tchar_not_sep:
  tchar c ⇒ c ≠ #":" ∧ c ≠ #" " ∧ c ≠ #"\t" ∧ c ≠ #"\r" ∧ c ≠ #"\n"
Proof
  rw[tchar_def] >> fs[stringTheory.isAlpha_def, stringTheory.isLower_def,
                      stringTheory.isUpper_def, stringTheory.isDigit_def] >>
  rpt strip_tac >> gvs[]
QED

(* So a valid header line has the character properties of the earlier
   definition (name without colon, space, CR or LF) *)
Theorem valid_bheader_chars:
  valid_bheader (n, v) ⇒
  n ≠ [] ∧ EVERY (λc. c ≠ #":" ∧ c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") n ∧
  EVERY (λc. c ≠ #"\r" ∧ c ≠ #"\n") v
Proof
  rw[valid_bheader_def] >> irule EVERY_MONOTONIC
  >- (qexists_tac ‘tchar’ >> simp[] >> metis_tac[tchar_not_sep])
  >> qexists_tac ‘field_char’ >> rw[field_char_def] >> rpt strip_tac >> gvs[]
QED

Definition valid_method_def:
  valid_method m ⇔ m = "GET" ∨ m = "POST"
End

(* Header names compared case-insensitively *)
Definition is_cl_def:
  is_cl (n, v:string) ⇔ MAP toLower n = "content-length"
End

Definition is_te_def:
  is_te (n, v:string) ⇔ MAP toLower n = "transfer-encoding"
End

(* The body's framing: no Content-Length header and an empty body, or
   exactly one, whose value is the body's length in decimal *)
Definition framed_def:
  framed hs b ⇔
    case FILTER is_cl hs of
      [] => b = ""
    | [(n, v)] => v = num_to_dec_string (LENGTH b)
    | _ => F
End

Definition valid_brequest_def:
  valid_brequest (Req m p ver hs b) ⇔
    valid_method m ∧ valid_path p ∧ EVERY uri_char p ∧ valid_version ver ∧
    EVERY valid_bheader hs ∧ ¬EXISTS is_te hs ∧ framed hs b
End

Definition print_brequest_def:
  print_brequest (Req m p ver hs b) =
    m ++ " " ++ p ++ " HTTP/" ++ ver ++ "\r\n" ++
    FLAT (MAP print_header hs) ++ "\r\n" ++ b
End

(* What the server answers *)
Definition bhandle_def:
  bhandle files (Req m p ver hs b) =
    if m = "POST" then (if p = "/echo" then Ok b else NotFound)
    else handle files (Get p)
End

(* The bytes of some requests, and of the responses to them *)
Definition brequests_def:
  brequests rs = bytes (FLAT (MAP print_brequest rs))
End

Definition bresponses_def:
  bresponses files rs = bytes (FLAT (MAP (print_response o bhandle files) rs))
End

(* ------------------------------------------------------------------------
   The specification (HttpSpecHeaders', with brequest for hrequest)
   ------------------------------------------------------------------------ *)

(* rest does not start with a complete valid request *)
Definition no_full_brequest_def:
  no_full_brequest rest ⇔ ∀r. valid_brequest r ⇒ ¬(brequests [r] ≼ rest)
End

(* Safety: at every point of the run, on every connection, if what the
   server has read so far is some complete requests rs followed by a
   partial one, then what it has written is a prefix of the responses to
   rs. *)
Definition http_safe_b_def:
  http_safe_b files io ⇔
    ∀evs c rs rest.
      LPREFIX (fromList evs) io ∧ EVERY valid_brequest rs ∧
      bytes_read_from c evs = brequests rs ++ rest ∧ no_full_brequest rest ⇒
      bytes_written_to c evs ≼ bresponses files rs
End

(* Liveness: if a client has sent the requests rs (within the first n steps
   of the schedule), the server eventually sends all their responses. *)
Definition http_live_b_def:
  http_live_b files sk io ⇔
    ∀c n rs.
      EVERY valid_brequest rs ∧ brequests rs ≼ sent_upto c n sk ⇒
      ∃evs. LPREFIX (fromList evs) io ∧
            bresponses files rs ≼ bytes_written_to c evs
End

(* THE STATEMENT: in every fair world with one listener lfd, the program
   runs forever, and its I/O trace is safe and live on every connection. *)
Definition http_spec_b_def:
  http_spec_b lfd files (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              http_safe_b files io ∧ http_live_b files sk io
End
