(*
  HttpSpecBodies2: what the HTTP server (with request bodies) does in a
  world where connections are closed and fds are REUSED.  A companion of
  HttpSpecBodies (unchanged), for the user's review; it is to
  HttpSpecBodies what EchoSpec2 is to EchoSpec.

  To believe a theorem  http_spec_b2 3w files prog, a reader needs this
  file, HttpSpecBodies (the requests, their grammar and printer, and the
  responses: reused unchanged), and EchoSpec2 (the version-2 socket world
  and the per-EPISODE projections: reused unchanged).

  What changes from HttpSpecBodies:
   - The world is version 2's (server_world2): clients numbered in order
     of connection, any allocation policy, «sock_close» frees an fd.
   - Safety and liveness are per episode (EchoSpec2's ep_read,
     ep_written), not per fd: the j-th accepted connection, from its
     accept to its close.  So the responses to a previous connection's
     requests may not appear on a later connection that reuses its fd.
   - Liveness is per client: if client j sends the requests rs, the
     server eventually writes all their responses in episode j.
   - A third clause, http_closes_b2 (EchoSpec2's echo_closes2): once the
     server has read the EOF of an episode's client, it eventually closes
     the episode's fd.  With liveness, it answers every complete request
     first: what is written after the close is not in the episode.
  Not in scope (as in HttpSpecBodies): closing a connection on the
  server's own initiative ("Connection: close", HTTP/1.0, timeouts).

  APPROVED by the user (2026-10-16, PR #105), as drafted: the server
  closes only after the client's EOF (server-initiated close is a later
  design item), and liveness is per client = per episode.

  Nothing here is proved; http_spec_b2 is a definition.
  HttpSpecBodies2BiteScript.sml shows that it rules out plausible bugs,
  including answering a previous connection's request on a reused fd, and
  that it is satisfiable (non-vacuity).
*)
Theory HttpSpecBodies2
Ancestors
  EchoSpec HttpSpec HttpSpecHeaders HttpSpecBodies EchoSpec2
Libs
  preamble

(* Safety: at every point of the run, in every episode, if what the
   server has read so far in it is some complete requests rs followed by
   a partial one, then what it has written in it is a prefix of the
   responses to rs. *)
Definition http_safe_b2_def:
  http_safe_b2 files io ⇔
    ∀evs j rs rest.
      LPREFIX (fromList evs) io ∧ EVERY valid_brequest rs ∧
      ep_read j evs = brequests rs ++ rest ∧ no_full_brequest rest ⇒
      ep_written j evs ≼ bresponses files rs
End

(* Liveness: if client j has sent the requests rs (within the first n
   steps of the schedule), the server eventually writes all their
   responses, in episode j. *)
Definition http_live_b2_def:
  http_live_b2 files sk io ⇔
    ∀j n rs.
      EVERY valid_brequest rs ∧ brequests rs ≼ sent2_upto j n sk ⇒
      ∃evs. LPREFIX (fromList evs) io ∧ bresponses files rs ≼ ep_written j evs
End

(* Closing: once the server has read the EOF of episode j's client, it
   eventually closes episode j's fd (EchoSpec2's clause, unchanged). *)
Definition http_closes_b2_def:
  http_closes_b2 io ⇔ echo_closes2 io
End

(* THE STATEMENT: in every fair version-2 world with one listener lfd,
   the program runs forever, and its I/O trace is safe and live in every
   episode, and closes every episode whose client has closed. *)
Definition http_spec_b2_def:
  http_spec_b2 lfd files (prog : dec list) ⇔
    ∀sk. server_world2 lfd sk ⇒
         ∃io. semantics_prog (init_state (socket2_ffi sk)) init_env prog
                (Diverge io) ∧
              http_safe_b2 files io ∧ http_live_b2 files sk io ∧
              http_closes_b2 io
End
