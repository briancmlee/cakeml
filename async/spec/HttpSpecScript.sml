(*
  HttpSpec: the final statement for the HTTP stretch goal, in the
  printer-based style.  TRUSTED SURFACE (with EchoSpec, whose world and
  per-connection projections it reuses); nothing here is proved.

  The trusted HTTP subset is tiny: GET of a path from a fixed map of
  static files; the response carries Content-Length; no chunking, no
  headers in requests, HTTP/1.0 framing.  Requests and responses are
  given by printers, so the statement says: if a client sends
  print_request r1 ++ print_request r2 ++ ... on a connection, the server
  sends back print_response (handle r1) ++ print_response (handle r2) ++ ...
  (a prefix of it at all times, and all of it eventually), for every
  connection at once.

  The theorem to prove is  http_spec 3w files http_prog  for the server's
  program and its file map.
*)
Theory HttpSpec
Ancestors
  EchoSpec ASCIInumbers
Libs
  preamble

(* ------------------------------------------------------------------------
   The HTTP subset
   ------------------------------------------------------------------------ *)

Datatype:
  request = Get string                  (* GET path *)
End

Datatype:
  response = Ok string | NotFound       (* 200 with a body, or 404 *)
End

(* Paths: non-empty, no space, CR or LF (so a request is unambiguous) *)
Definition valid_path_def:
  valid_path p ⇔ p ≠ [] ∧ EVERY (λc. c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") p
End

Definition valid_request_def:
  valid_request (Get p) ⇔ valid_path p
End

Definition print_request_def:
  print_request (Get p) = "GET " ++ p ++ " HTTP/1.0\r\n\r\n"
End

Definition print_response_def:
  print_response (Ok body) =
    "HTTP/1.0 200 OK\r\nContent-Length: " ++ num_to_dec_string (LENGTH body) ++
    "\r\n\r\n" ++ body ∧
  print_response NotFound =
    "HTTP/1.0 404 Not Found\r\nContent-Length: 0\r\n\r\n"
End

(* The server's intended behaviour: serve the file, or 404 *)
Definition handle_def:
  handle files (Get p) =
    case ALOOKUP files p of SOME body => Ok body | NONE => NotFound
End

(* Strings as the bytes on the wire *)
Definition bytes_def:
  bytes (s : string) = MAP (n2w o ORD) s : word8 list
End

Definition requests_def:
  requests rs = bytes (FLAT (MAP print_request rs))
End

Definition responses_def:
  responses files rs = bytes (FLAT (MAP (print_response o handle files) rs))
End

(* ------------------------------------------------------------------------
   The specification
   ------------------------------------------------------------------------ *)

(* rest does not begin with a complete valid request *)
Definition no_full_request_def:
  no_full_request rest ⇔ ∀r. valid_request r ⇒ ¬(requests [r] ≼ rest)
End

(* Safety: at every point of the run, on every connection, if what the
   server has read so far is some complete requests rs followed by a
   partial one, then what it has written is a prefix of the responses to
   rs. *)
Definition http_safe_def:
  http_safe files io ⇔
    ∀evs c rs rest.
      LPREFIX (fromList evs) io ∧ EVERY valid_request rs ∧
      bytes_read_from c evs = requests rs ++ rest ∧ no_full_request rest ⇒
      bytes_written_to c evs ≼ responses files rs
End

(* Liveness: if a client has sent the requests rs (within the first n steps
   of the schedule), the server eventually sends all their responses. *)
Definition http_live_def:
  http_live files sk io ⇔
    ∀c n rs.
      EVERY valid_request rs ∧ requests rs ≼ sent_upto c n sk ⇒
      ∃evs. LPREFIX (fromList evs) io ∧
            responses files rs ≼ bytes_written_to c evs
End

(* THE STATEMENT: in every fair world with one listener lfd, the program
   runs forever, and its I/O trace is safe and live on every connection. *)
Definition http_spec_def:
  http_spec lfd files (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              http_safe files io ∧ http_live files sk io
End
