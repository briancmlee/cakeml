(*
  Clients and proxies in the endpoint world (for the user's review):
  statements showing that the endpoint world can state them.

  - A toy HTTP client: it connects to address a, sends the request r, and
    reads the reply until the server closes; then it closes.
  - A proxy (two roles): for each client it accepts on its listener, it
    connects to the backend address b, forwards what the client sends to
    the backend, and what the backend sends back to the client.
  Both programs run forever (rg_spec asks for divergence): a finished
  client idles.
*)
Theory endpointClients
Ancestors
  llist ffi semantics ffiSpikeSocketFFI EchoSpec EchoSpec2 HttpSpec
  HttpSpecBodies endpointWorld endpointFair endpointSpecForms
Libs
  preamble

(* The address a connect event asked for, and the fd it returned *)
Definition event_connect_def:
  event_connect (IO_event (ExtCall n) conf bytes) =
    (let out = MAP SND bytes in
     if n = «sock_connect» ∧ LENGTH conf = 8 ∧ LENGTH out = 9 ∧ HD out = 1w
     then SOME (w82n conf, bytes_fd (TL out)) else NONE) ∧
  event_connect _ = NONE
End

(* Episode j was opened by a connect to address a *)
Definition ep_connected_to_def:
  ep_connected_to evs j a ⇔
    ∃i. i < LENGTH evs ∧ event_connect (EL i evs) = SOME (a, EL j (opened_fds evs)) ∧
        LENGTH (opened_fds (TAKE i evs)) = j
End

(* Episode j was opened by an accept *)
Definition ep_accepted_def:
  ep_accepted evs j ⇔
    j < LENGTH (opened_fds evs) ∧ ∀a. ¬ep_connected_to evs j a
End

(* The program shut down episode j's sending side (or closed it) *)
Definition ch_shut_def:
  ch_shut j evs ⇔
    ch_closed j evs ∨
    j < LENGTH (opened_fds evs) ∧
    EXISTS (λev. case ev of
                 | IO_event (ExtCall n) conf _ =>
                     n = «sock_shutdown» ∧ conf = fd_bytes (EL j (opened_fds evs))
                 | _ => F) (ch_events j 0 [] evs)
End

(* The program read the EOF of episode j's peer while j was open *)
Definition ch_eof_read_def:
  ch_eof_read j evs ⇔
    j < LENGTH (opened_fds evs) ∧
    EXISTS (λev. event_eof ev = SOME (EL j (opened_fds evs))) (ch_events j 0 [] evs)
End

(* ------------------------------------------------------------------------
   A toy HTTP client
   ------------------------------------------------------------------------ *)

Definition client_guar_def:
  client_guar a r w io ⇔
    (* it opens one channel, to a, and sends a prefix of the request *)
    always (λevs. LENGTH (opened_fds evs) ≤ 1 ∧
                  (0 < LENGTH (opened_fds evs) ⇒ ep_connected_to evs 0 a) ∧
                  ch_sent 0 evs ≼ brequests [r]) io ∧
    (* if the server accepts the connection and reads, it sends all of it *)
    (∀evs c. LPREFIX (fromList evs) io ∧ ep_chan w evs 0 = SOME c ∧ w.accepts a c ∧
             reads_fair w io c ⇒
             eventually (λevs'. ch_sent 0 evs' = brequests [r]) io) ∧
    (* it reads everything the server sends *)
    input_live w io ∧
    (* once it has read the server's EOF, it closes *)
    (∀evs. LPREFIX (fromList evs) io ∧ ch_eof_read 0 evs ⇒
           eventually (λevs'. ch_closed 0 evs') io)
End

Definition http_client_spec_def:
  http_client_spec a r prog ⇔
    valid_brequest r ∧ rg_spec ep_client_world (client_guar a r) prog
End

(* ------------------------------------------------------------------------
   A proxy: two roles
   ------------------------------------------------------------------------ *)

(* pair i: the backend episode serving front episode i *)
Definition proxy_guar_def:
  proxy_guar b w io ⇔
    ∃pair.
      (∀i i'. pair i = pair i' ⇒ i = i') ∧
      (* safety: each side gets a prefix of what the other side sent *)
      always (λevs. ∀i. ep_accepted evs i ⇒
                        (pair i < LENGTH (opened_fds evs) ⇒ ep_connected_to evs (pair i) b) ∧
                        ch_sent (pair i) evs ≼ ch_read i evs ∧
                        ch_sent i evs ≼ ch_read (pair i) evs) io ∧
      (* liveness: what each side has sent reaches the other side, if that
         side's peer reads *)
      (∀evs i c c'. LPREFIX (fromList evs) io ∧ ep_chan w evs i = SOME c ∧
                    ep_chan w evs (pair i) = SOME c' ⇒
                    (reads_fair w io c' ⇒
                     eventually (λevs'. peer_sent_at w evs c ≼ ch_sent (pair i) evs') io) ∧
                    (reads_fair w io c ⇒
                     eventually (λevs'. peer_sent_at w evs c' ≼ ch_sent i evs') io)) ∧
      (* half-close: the client's EOF is passed on to the backend *)
      (∀evs i. LPREFIX (fromList evs) io ∧ ch_eof_read i evs ⇒
               eventually (λevs'. ch_shut (pair i) evs') io) ∧
      input_live w io
End

Definition proxy_spec_def:
  proxy_spec lfd a b prog ⇔ rg_spec (ep_server_world all_calls lfd a) (proxy_guar b) prog
End
