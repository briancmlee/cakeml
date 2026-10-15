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

  Everything else is HttpSpecHeaders': the world, the projections, and
  the shapes of safety, liveness and the statement.
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
    valid_method m ∧ valid_path p ∧ valid_version ver ∧
    EVERY valid_header hs ∧ ¬EXISTS is_te hs ∧ framed hs b
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
