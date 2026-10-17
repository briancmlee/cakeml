(*
  Moonshot step 9 (design/45 §2.4): the proxy's guarantee on its RAW L0
  trace, as a STATEMENT for review (DRAFT).  Nothing here is proved.

  Same form and vocabulary as the echo's R4′ (honestL1BStmts:
  echo_safe_l0, echo_live_l0, ep_timed_out, l0_echo2_claim).  The proxy
  has two kinds of episode: a FRONT (an accepted fd) and its BACKEND (a
  connected fd); an episode is named by the position in the trace of the
  event that opened its fd (accept or connect), so both kinds share one
  vocabulary (the pos_ names).  pr p = SOME q: front p's backend is q.

  OWED, PENDING [R3] (design/45 §2.4; kept out of this draft until the
  user rules on [R3], recommended (a): EClose / EShut in endpointHLModel,
  folded into close-v2's E1 rebase):
   - half-close, front to back: a front's EOF read ⇒ eventually the
     backend is shut;
   - backend EOF or break ⇒ forward the EOF (shut the front), then close
     the front;
   - refused backend ⇒ eventually close the front;
   - closed front ⇒ eventually close the backend.
*)
Theory proxyL0Stmts
Ancestors
  honestL1BStmts honestEchoL0Spec honestL0 honestL0World
Libs
  preamble

(* A port, as the C reads it (honestL1EPModel.port_bytes) *)
Definition pbytes_def:
  pbytes (p : num) : word8 list = [n2w (p DIV 256); n2w p]
End

(* The socket a connect returned (the header's value field; 0: none), and
   the port it connected to *)
Definition l0_event_connected_def:
  l0_event_connected (IO_event (ExtCall n) conf bytes) =
    (if n = «sys_connect» ∧ LENGTH conf = 2 ∧ 13 ≤ LENGTH bytes ∧
        w82n (TAKE 8 (TL (MAP SND bytes))) ≠ 0
     then SOME (n2w (w82n (TAKE 8 (TL (MAP SND bytes)))) : word64)
     else NONE) ∧
  l0_event_connected _ = NONE
End

Definition connect_port_def:
  connect_port (IO_event (ExtCall n) conf bytes) = (if n = «sys_connect» then SOME conf else NONE) ∧
  connect_port _ = NONE
End

(* The fd an event opened (accept or connect) *)
Definition l0_event_opened_def:
  l0_event_opened e =
    case l0_event_accepted e of SOME f => SOME f | NONE => l0_event_connected e
End

(* Episode p: the fd opened by event p of evs, and the events of its
   lifetime (up to a successful close of it, or a later open returning it) *)
Definition pos_fd_def:
  pos_fd p evs = if p < LENGTH evs then l0_event_opened (EL p evs) else NONE
End

Definition pos_ends_def:
  pos_ends f e ⇔ l0_event_closed e = SOME f ∨ l0_event_opened e = SOME f
End

Definition pos_events_def:
  pos_events p evs =
    case pos_fd p evs of
    | NONE => []
    | SOME f => FST (SPLITP (pos_ends f) (DROP (SUC p) evs))
End

Definition pos_open_def:
  pos_open p evs ⇔
    ∃f. pos_fd p evs = SOME f ∧ ¬EXISTS (pos_ends f) (DROP (SUC p) evs)
End

Definition pos_sent_def:
  pos_sent p evs =
    case pos_fd p evs of
    | NONE => []
    | SOME f => FLAT (MAP (l0_event_sent f) (pos_events p evs))
End

Definition pos_read_def:
  pos_read p evs =
    case pos_fd p evs of
    | NONE => []
    | SOME f => FLAT (MAP (l0_event_recv f) (pos_events p evs))
End

Definition is_front_def:
  is_front p evs ⇔ p < LENGTH evs ∧ l0_event_accepted (EL p evs) ≠ NONE
End

(* ------------------------------------------------------------------------
   Safety (every prefix; no fairness)
   ------------------------------------------------------------------------ *)

(* pr: a front's backend.  Relay prefixes both ways; a backend connects to
   b and serves one front; an unpaired front is sent nothing; BOUNDED
   BUFFERING (NEW): neither direction holds more than Bnd bytes read and not
   yet sent on *)
Definition proxy_safe_l0_def:
  proxy_safe_l0 Bnd b (pr : num -> num option) io ⇔
    (∀p p' q. pr p = SOME q ∧ pr p' = SOME q ⇒ p = p') ∧
    ∀evs. LPREFIX (fromList evs) io ⇒
      (∀q. q < LENGTH evs ∧ l0_event_connected (EL q evs) ≠ NONE ⇒
           connect_port (EL q evs) = SOME (pbytes b) ∧
           ∃p. p < q ∧ is_front p evs ∧ pr p = SOME q) ∧
      ∀p. is_front p evs ⇒
        case pr p of
        | NONE => pos_sent p evs = []
        | SOME q =>
            pos_sent q evs ≼ pos_read p evs ∧ pos_sent p evs ≼ pos_read q evs ∧
            LENGTH (pos_read p evs) ≤ LENGTH (pos_sent q evs) + Bnd ∧
            LENGTH (pos_read q evs) ≤ LENGTH (pos_sent p evs) + Bnd
End

(* ------------------------------------------------------------------------
   Liveness, unless an observed excuse (D16, D23)
   ------------------------------------------------------------------------ *)

(* D23's observed excuse, for episode p (ep_timed_out, with episodes named
   by position: for a front p that is the j-th accept, pos_timed_out K p io
   ⇔ ep_timed_out K j io, a lemma to prove) *)
Definition pos_timed_out_def:
  pos_timed_out K p io ⇔
    ∃evs span f.
      LPREFIX (fromList (evs ++ span)) io ∧ pos_open p evs ∧ pos_fd p evs = SOME f ∧
      K ≤ n_out_polls f span ∧
      EVERY (λe. poll_ev e ⇒ out_poll f e) span ∧
      ¬EXISTS (send_took f) span ∧ ¬EXISTS (pos_ends f) span
End

(* D16's observed excuse, by position (ep_hard_err) *)
Definition pos_hard_err_def:
  pos_hard_err p io ⇔
    ∃evs ev f. LPREFIX (fromList (evs ++ [ev])) io ∧ pos_open p evs ∧
               pos_fd p evs = SOME f ∧ hard_err_on f ev
End

Definition pos_excuse_def:
  pos_excuse K p io ⇔ pos_hard_err p io ∨ pos_timed_out K p io
End

(* Per pair (p, q), with the front on channel c and the backend on c′:
   CONDITIONAL on the far side draining, each direction relays what its
   peer has sent so far, UNLESS an observed excuse on either fd.  (Echo's
   peer_eof / close clauses: see the half-close clauses below.) *)
Definition proxy_live_l0_def:
  proxy_live_l0 K pr w0 io ⇔
    ∀evs p q c c' w f g.
      LPREFIX (fromList evs) io ∧ is_front p evs ∧ pr p = SOME q ∧
      pos_open p evs ∧ pos_open q evs ∧ pos_fd p evs = SOME f ∧ pos_fd q evs = SOME g ∧
      world_at w0 evs = SOME w ∧ l0_chan_of w f = SOME c ∧ l0_chan_of w g = SOME c' ⇒
      (* client → KV: needs KV to drain c′ *)
      (drains w0 io c' ⇒
         pos_excuse K p io ∨ pos_excuse K q io ∨
         ∃evs'. LPREFIX (fromList evs') io ∧ (EL c w.chans).peer_sent ≼ pos_sent q evs') ∧
      (* KV → client: needs the client to drain c *)
      (drains w0 io c ⇒
         pos_excuse K p io ∨ pos_excuse K q io ∨
         ∃evs'. LPREFIX (fromList evs') io ∧ (EL c' w.chans).peer_sent ≼ pos_sent p evs')
End

(* Every front gets a backend: a connect to b that is accepted or refused
   is attempted, unless the front ended first.  (Under [F4]; the retry of a
   socketless connect, option (b), is the program's: stated here as
   "eventually paired".) *)
Definition proxy_pairs_l0_def:
  proxy_pairs_l0 pr io ⇔
    ∀evs p. LPREFIX (fromList evs) io ∧ is_front p evs ⇒
      ∃evs'. LPREFIX (fromList evs') io ∧ (pr p ≠ NONE ∨ ¬pos_open p evs')
End

(* R4′ for the proxy: on the honest L0 FFI, K = pf_sendwait (D23),
   Bnd = hw + 3 * pf_chunk (revision 2: L1's inbox of the front, the
   proxy's one round of read-but-not-yet-written bytes, the backend's
   outbox ≤ hw + pf_chunk) *)
Definition l0_proxy_claim_def:
  l0_proxy_claim K Bnd b prog ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃beh. semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
          (listen_failed beh ∨
           ∃io pr. beh = Diverge io ∧ proxy_safe_l0 Bnd b pr io ∧
                   (F1_io io ∧ F2 w0 ∧ accepts_below io ⇒
                    proxy_live_l0 K pr w0 io ∧ proxy_pairs_l0 pr io ∧ conn_live_l0 w0 io))
End
