(*
  HttpSpecHeaders: a header-tolerant VARIANT of HttpSpec, for the user's
  decision.  DRAFT; HttpSpec itself is unchanged.

  HttpSpec's request subset is exactly  GET <path> HTTP/1.0\r\n\r\n , so
  real clients (curl, browsers), which always send headers, are outside
  it.  Here a request is

     GET <path> HTTP/<version>\r\n
     <name>: <value>\r\n          (any number of header lines)
     \r\n

  with version 1.0 or 1.1 and arbitrary well-formed headers, which the
  server IGNORES: the response depends only on the path, exactly as in
  HttpSpec (same print_response, same handle).  The statement keeps
  HttpSpec's printer-based style: the spec quantifies over printed valid
  requests with ANY header lists, and never mentions a parser.

  Everything else is HttpSpec's: the world (server_world, socket_ffi), the
  per-connection projections (bytes_read_from, bytes_written_to,
  sent_upto), and the shapes of safety, liveness and the statement.
  HttpSpecHeadersBiteScript.sml gives bite lemmas and non-vacuity, and
  proves that HttpSpec's requests are the special case of no headers and
  version 1.0.
*)
Theory HttpSpecHeaders
Ancestors
  EchoSpec HttpSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   Requests with headers
   ------------------------------------------------------------------------ *)

Datatype:
  hrequest = GetH string string ((string # string) list)
                                        (* GET path, version, headers *)
End

(* Versions: HTTP/1.0 or HTTP/1.1 *)
Definition valid_version_def:
  valid_version v ⇔ v = "1.0" ∨ v = "1.1"
End

(* Header lines: a non-empty name without colon, space, CR or LF; a value
   without CR or LF (so a request is unambiguous) *)
Definition valid_header_def:
  valid_header (n, v) ⇔
    n ≠ [] ∧ EVERY (λc. c ≠ #":" ∧ c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") n ∧
    EVERY (λc. c ≠ #"\r" ∧ c ≠ #"\n") v
End

Definition valid_hrequest_def:
  valid_hrequest (GetH p ver hs) ⇔
    valid_path p ∧ valid_version ver ∧ EVERY valid_header hs
End

Definition print_header_def:
  print_header (n, v) = n ++ ": " ++ v ++ "\r\n"
End

Definition print_hrequest_def:
  print_hrequest (GetH p ver hs) =
    "GET " ++ p ++ " HTTP/" ++ ver ++ "\r\n" ++ FLAT (MAP print_header hs) ++ "\r\n"
End

(* What the server answers: the headers and the version are ignored *)
Definition hpath_def:
  hpath (GetH p ver hs) = Get p
End

(* The bytes of some requests, and of the responses to them *)
Definition hrequests_def:
  hrequests rs = bytes (FLAT (MAP print_hrequest rs))
End

Definition hresponses_def:
  hresponses files rs = bytes (FLAT (MAP (print_response o handle files o hpath) rs))
End

(* ------------------------------------------------------------------------
   The specification (HttpSpec's, with hrequest for request)
   ------------------------------------------------------------------------ *)

(* rest does not start with a complete valid request *)
Definition no_full_hrequest_def:
  no_full_hrequest rest ⇔ ∀r. valid_hrequest r ⇒ ¬(hrequests [r] ≼ rest)
End

(* Safety: at every point of the run, on every connection, if what the
   server has read so far is some complete requests rs followed by a
   partial one, then what it has written is a prefix of the responses to
   rs. *)
Definition http_safe_h_def:
  http_safe_h files io ⇔
    ∀evs c rs rest.
      LPREFIX (fromList evs) io ∧ EVERY valid_hrequest rs ∧
      bytes_read_from c evs = hrequests rs ++ rest ∧ no_full_hrequest rest ⇒
      bytes_written_to c evs ≼ hresponses files rs
End

(* Liveness: if a client has sent the requests rs (within the first n steps
   of the schedule), the server eventually sends all their responses. *)
Definition http_live_h_def:
  http_live_h files sk io ⇔
    ∀c n rs.
      EVERY valid_hrequest rs ∧ hrequests rs ≼ sent_upto c n sk ⇒
      ∃evs. LPREFIX (fromList evs) io ∧
            hresponses files rs ≼ bytes_written_to c evs
End

(* THE STATEMENT: in every fair world with one listener lfd, the program
   runs forever, and its I/O trace is safe and live on every connection. *)
Definition http_spec_h_def:
  http_spec_h lfd files (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              http_safe_h files io ∧ http_live_h files sk io
End
