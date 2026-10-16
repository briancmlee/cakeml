(*
  Clients and proxies in the endpoint world (for the user's review):
  statements showing that the endpoint world can state them.

  - A toy HTTP client: it connects to address a, sends the request r, and
    reads the reply until the server closes; then it closes.
  - A proxy (two roles): for each client it accepts on its listener, it
    connects to the backend address b, forwards what the client sends to
    the backend, and what the backend sends back to the client.
  A refused connect is reported by the next read (status 3, code 4) or
  send (code 4) on the channel (endpointWorld).  The client must notice
  it and close, and must not read on to the EOF that follows (taking the
  refusal for an empty answer: refusal_bite); the proxy closes the
  client's episode when its backend refuses.
  Both programs run forever (rg_spec asks for divergence): a finished
  client idles.
*)
Theory endpointClients
Ancestors
  llist ffi semantics ffiSpikeSocketFFI EchoSpec EchoSpec2 HttpSpec
  HttpSpecBodies endpointWorld endpointFair endpointSpecForms Marshalling
Libs
  preamble

(* The address a connect event asked for, and the fd it returned *)
Definition event_connect_def:
  event_connect (IO_event (ExtCall n) conf bytes) =
    (let out = MAP SND bytes in
     if n = «sock_connect» ∧ LENGTH conf = 8 ∧ LENGTH out = 13 ∧ HD out = 3w
     then SOME (w82n conf, bytes_fd (TAKE 8 (TL out))) else NONE) ∧
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

(* The program was told that f's connect was refused: a read returned
   status 3 (error) with code 4 (ECONNREFUSED), or a send code 4 *)
Definition event_refused_def:
  event_refused f (IO_event (ExtCall n) conf bytes) =
    (let out = MAP SND bytes in
       (n = «sock_read» ∧ LENGTH conf = 8 ∧ bytes_fd conf = f ∧
        2 ≤ LENGTH out ∧ HD out = 3w ∧ EL 1 out = 4w) ∨
       (n = «sock_send» ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = f ∧
        LENGTH out = 13 ∧ HD out = 4w)) ∧
  event_refused f _ = F
End

(* ... on episode j, while it was open *)
Definition ch_refused_def:
  ch_refused j evs ⇔
    j < LENGTH (opened_fds evs) ∧
    EXISTS (event_refused (EL j (opened_fds evs))) (ch_events j 0 [] evs)
End

(* ------------------------------------------------------------------------
   A toy HTTP client
   ------------------------------------------------------------------------ *)

(* Channel c reaches status st along the run (a connect settles when the
   environment says, endpointWorld's Settle) *)
Definition ch_reaches_def:
  ch_reaches w io c st ⇔
    eventually (λevs. c < LENGTH (ep_replay w evs).chans ∧
                      (EL c (ep_replay w evs).chans).status = st) io
End

Definition client_guar_def:
  client_guar a r w io ⇔
    (* it opens one channel, to a, and sends a prefix of the request *)
    always (λevs. LENGTH (opened_fds evs) ≤ 1 ∧
                  (0 < LENGTH (opened_fds evs) ⇒ ep_connected_to evs 0 a) ∧
                  ch_sent 0 evs ≼ brequests [r]) io ∧
    (* if the server accepts the connection and reads, it sends all of it *)
    (∀evs c. LPREFIX (fromList evs) io ∧ ep_chan w evs 0 = SOME c ∧ ch_reaches w io c Up ∧
             reads_fair w io c ⇒
             eventually (λevs'. ch_sent 0 evs' = brequests [r]) io) ∧
    (* it reads everything the server sends *)
    input_live w io ∧
    (* once it has read the server's EOF, it closes *)
    (∀evs. LPREFIX (fromList evs) io ∧ ch_eof_read 0 evs ⇒
           eventually (λevs'. ch_closed 0 evs') io) ∧
    (* if the server refuses, the client is told so, and closes *)
    (∀evs c. LPREFIX (fromList evs) io ∧ ep_chan w evs 0 = SOME c ∧ ch_reaches w io c Refused ⇒
             eventually (λevs'. ch_refused 0 evs' ∧ ch_closed 0 evs') io) ∧
    (* and it does not take a refusal for an empty answer: once told, it
       reads no EOF (which a refused channel gives after the error) *)
    always (λevs. ¬(ch_refused 0 evs ∧ ch_eof_read 0 evs)) io
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
      (* a refused backend: the proxy closes the client's episode (our
         choice; answering an error instead would need the protocol) *)
      (∀evs i. LPREFIX (fromList evs) io ∧ ep_accepted evs i ∧ ch_refused (pair i) evs ⇒
               eventually (λevs'. ch_closed i evs') io) ∧
      input_live w io
End

Definition proxy_spec_def:
  proxy_spec lfd a b prog ⇔ rg_spec (ep_server_world all_calls lfd a) (proxy_guar b) prog
End

(* ------------------------------------------------------------------------
   Bite: a client that reads through the refusal to the EOF after it fails
   client_guar, whatever else it does
   ------------------------------------------------------------------------ *)

Definition refused_trace_def:
  refused_trace a (f:word64) =
    [IO_event (ExtCall «sock_connect») (n2w8 a)
              (ZIP (REPLICATE 13 0w, l0_result 3 (w2n f)));
     IO_event (ExtCall «sock_read») (fd_bytes f)
              (ZIP (REPLICATE 10 0w, 3w :: 4w :: REPLICATE 8 0w));
     IO_event (ExtCall «sock_read») (fd_bytes f)
              (ZIP (REPLICATE 10 0w, 2w :: REPLICATE 9 0w))]
End

Theorem refused_trace_bad:
  ch_refused 0 (refused_trace a f) ∧ ch_eof_read 0 (refused_trace a f)
Proof
  simp[refused_trace_def, ch_refused_def, ch_eof_read_def, opened_fds_def,
       ch_events_def, event_opened_def, event_accepted_def, event_closed_def,
       event_refused_def, event_eof_def, l0_result_def, LENGTH_n2w8,
       GSYM fd_bytes_def, MAP_ZIP, TAKE_APPEND1, LENGTH_fd_bytes, TAKE_LENGTH_TOO_LONG]
QED

Theorem refusal_bite:
  ¬client_guar a r w (fromList (refused_trace a f ++ evs))
Proof
  simp[client_guar_def, always_def] >> rpt disj2_tac >>
  qexists_tac ‘refused_trace a f’ >>
  simp[refused_trace_bad, LPREFIX_fromList, from_toList, toList_THM]
QED

(* ------------------------------------------------------------------------
   Bite: a slow handshake is expressible.  The environment settles a
   connect when it chooses (endpointWorld's Settle), so a channel can stay
   Connecting for any number of ticks, as a kernel's can (a SYN to a busy
   host settles after retransmits)
   ------------------------------------------------------------------------ *)

(* A client world whose first connect settles Up at tick k *)
Definition slow_world_def:
  slow_world k =
    <| listening := []; chans := []; open_fds := []; reserved := [];
       alloc := (λj used. 5w); takes := (λj b n. n); calls := all_calls;
       env := (λn h. if n = k then [Settle 0 T] else []); clock := 0; hist := [] |>
End

Theorem slow_ticks[local]:
  ∀n w. n ≤ k ∧ w.env = (slow_world k).env ∧ w.clock + n ≤ k ⇒
        (FUNPOW ep_tick n w).chans = w.chans ∧
        (FUNPOW ep_tick n w).clock = w.clock + n ∧
        (FUNPOW ep_tick n w).env = w.env
Proof
  Induct >> simp[FUNPOW] >> rpt gen_tac >> strip_tac >>
  ‘w.clock ≠ k’ by decide_tac >>
  first_x_assum (qspec_then ‘ep_tick w’ mp_tac) >>
  simp[ep_tick_def, slow_world_def]
QED

(* MAIN: after its connect, the channel is still Connecting after any k
   ticks, and Up after k + 1 *)
Theorem slow_handshake:
  ep_connect a (slow_world k) = (SOME 5w, w) ⇒
  (∀n. n ≤ k ⇒ (EL 0 (FUNPOW ep_tick n w).chans).status = Connecting) ∧
  (EL 0 (FUNPOW ep_tick (SUC k) w).chans).status = Up
Proof
  rw[ep_connect_def, ep_alloc_def, ep_used_def, slow_world_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac ‘FUNPOW ep_tick _ w0’ >>
  ‘w0.env = (slow_world k).env ∧ w0.clock = 0 ∧
   w0.chans = [new_chan (SOME a) Connecting]’ by simp[Abbr ‘w0’, slow_world_def] >>
  TRY (qspecl_then [‘n’, ‘w0’] mp_tac slow_ticks >> simp[new_chan_def] >> NO_TAC) >>
  simp[FUNPOW_SUC] >>
  qspecl_then [‘k’, ‘w0’] mp_tac slow_ticks >> simp[] >>
  strip_tac >> simp[ep_tick_def] >>
  fs[slow_world_def, ep_deliver_def, upd_chan_def, new_chan_def, LUPDATE_def]
QED
