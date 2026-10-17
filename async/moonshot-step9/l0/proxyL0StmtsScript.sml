(*
  Moonshot step 9 (design/45 §2.4): the proxy's guarantee on its RAW L0
  trace, as a STATEMENT for review (DRAFT).  Nothing here is proved.

  Same form and vocabulary as the echo's R4′ (honestL1BStmts:
  echo_safe_l0, echo_live_l0, ep_timed_out, l0_echo2_claim).  The proxy
  has two kinds of episode: a FRONT (an accepted fd) and its BACKEND (a
  connected fd); an episode is named by the position in the trace of the
  event that opened its fd (accept or connect), so both kinds share one
  vocabulary (the pos_ names).  pr p = SOME q: front p's backend is q.

  REVISION 7 (user rulings):
   - the buffering bound is EXACT, proxy_bnd hw = hw + pf_chunk + pread
     (was hw + 3·pf_chunk), and it holds unless the receiving side has
     timed out (D23; option (a); option (b), the unconditional bound, is
     committed with [R3](a));
   - proxy_pairs_l0: excused if connects return no socket infinitely
     often ([F4] is not assumed);
   - D33: the world no longer reserves fds 0-2 (l0_proxy_world); the
     outcomes add stdio_closed, and the listen failure follows the three
     sys_fdok calls (proxy_listen_failed).

  OWED, PENDING [R3] (design/45 §2.4; kept out of this draft until the
  user rules on [R3], recommended (a): EClose / EShut in endpointHLModel,
  folded into close-v2's E1 rebase):
   - half-close, front to back: a front's EOF read ⇒ eventually the
     backend is shut;
   - backend EOF or break ⇒ forward the EOF (shut the front), then close
     the front;
   - refused backend ⇒ eventually close the front;
   - closed front ⇒ eventually close the backend;
   - (rev 7, user: COMMITTED with [R3](a)) L1 reports a gone handle to
     the program (a write error or a Level marker); the proxy stops
     relaying into it and closes the pair, so the buffering bound holds
     without the timeout excuse.
*)
Theory proxyL0Stmts
Ancestors
  honestL1BStmts honestEchoL0Spec honestL0Outcome honestL0 honestL0World
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

(* Revision 7 (user): the EXACT buffering bound, per direction p → q.
   Read on p and not yet sent on q is at most
     - L1's inbox of p: ≤ pf_chunk (L1 fetches only into an empty inbox,
       one recv of at most pf_chunk), plus
     - the proxy's read not yet written to q, plus L1's outbox of q:
       together ≤ hw + pread (pread = 4096, moonshotProxy).  The credit gate
       reads p in a round only if q's outbox after that round's writes is
       ≤ hw, and the read (≤ pread) is written in full the next round.
   Reached: q's kernel takes nothing, the last read brings q's outbox to
   exactly hw, and L1's fetch then refills p's inbox *)
Definition proxy_bnd_def:
  proxy_bnd (hw : num) = hw + pf_chunk + 4096
End

(* pr: a front's backend.  Every successful listen is on a (rev 5); relay
   prefixes both ways; a backend connects to b and serves one front; a
   front's backend is a connect (rev 5: never another front); an unpaired
   front is sent nothing; BOUNDED BUFFERING: neither direction holds more
   than proxy_bnd hw bytes read and not yet sent on, UNLESS (rev 7, user,
   option (a)) the receiving side has timed out by then (D23: L1 then
   drops that side's output, and the proxy cannot see it; option (b),
   committed with [R3](a), makes the bound unconditional) *)
Definition proxy_safe_l0_def:
  proxy_safe_l0 K hw a b (pr : num -> num option) io ⇔
    (∀p p' q. pr p = SOME q ∧ pr p' = SOME q ⇒ p = p') ∧
    ∀evs. LPREFIX (fromList evs) io ⇒
      (∀conf bs k. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ∧
                   l0_ev_res bs = SOME (Ok k) ⇒ conf = pbytes a) ∧
      (∀q. q < LENGTH evs ∧ l0_event_connected (EL q evs) ≠ NONE ⇒
           connect_port (EL q evs) = SOME (pbytes b) ∧
           ∃p. p < q ∧ is_front p evs ∧ pr p = SOME q) ∧
      (∀p q. pr p = SOME q ∧ q < LENGTH evs ⇒ l0_event_connected (EL q evs) ≠ NONE) ∧
      ∀p. is_front p evs ⇒
        case pr p of
        | NONE => pos_sent p evs = []
        | SOME q =>
            pos_sent q evs ≼ pos_read p evs ∧ pos_sent p evs ≼ pos_read q evs ∧
            (pos_timed_out K q (fromList evs) ∨
             LENGTH (pos_read p evs) ≤ LENGTH (pos_sent q evs) + proxy_bnd hw) ∧
            (pos_timed_out K p (fromList evs) ∨
             LENGTH (pos_read q evs) ≤ LENGTH (pos_sent p evs) + proxy_bnd hw)
End

(* ------------------------------------------------------------------------
   Liveness, unless an observed excuse (D16, D23)
   ------------------------------------------------------------------------ *)

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

(* A connect that returned no socket (the value field 0) *)
Definition l0_nosock_def:
  l0_nosock e ⇔ connect_port e ≠ NONE ∧ l0_event_connected e = NONE
End

(* Every front gets a backend: a connect to b that returned a socket,
   unless an observed excuse on the front (rev 6: closing an unpaired front
   is no way out), or (rev 7, user: [F4] is not assumed) connects return
   no socket infinitely often *)
Definition proxy_pairs_l0_def:
  proxy_pairs_l0 K pr io ⇔
    ∀evs p. LPREFIX (fromList evs) io ∧ is_front p evs ⇒
      pos_excuse K p io ∨
      (∃evs' q. LPREFIX (fromList evs') io ∧ pr p = SOME q ∧ q < LENGTH evs') ∨
      ∀k. ∃evs'. LPREFIX (fromList evs') io ∧ k ≤ LENGTH (FILTER l0_nosock evs')
End

(* Fewer than N accepts on every prefix.  The proxy accepts while it holds
   fewer than cbound / 2 = 2^62 pairs (2 · pairs + 2 ≤ cbound), and its pairs
   never end until closing lands ([R3]); so new connections are owed only
   below 2^62 accepts.  Once [R3] closing lands this becomes an observed
   excuse ("open fronts at the cap") instead of a hypothesis *)
Definition accepts_lt_def:
  accepts_lt N io ⇔ ∀evs. LPREFIX (fromList evs) io ⇒ LENGTH (l0_accepted evs) < N
End

(* The startup contract (D33): l0_server_world without fds 0-2 reserved;
   the program checks them itself (stdio_closed) *)
Definition l0_proxy_world_def:
  l0_proxy_world w0 ⇔
    w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ w0.hist = [] ∧
    fds_lt w0 ∧ l0_rely w0
End

(* D33: the three sys_fdok calls found fds 0-2 open, then the listen
   failed *)
Definition proxy_listen_failed_def:
  proxy_listen_failed b ⇔
    ∃i0 i1 i2 r0 r1 r2 conf bs.
      b = Terminate Success [IO_event (ExtCall «sys_fdok») [0w] [(i0, r0)];
                             IO_event (ExtCall «sys_fdok») [1w] [(i1, r1)];
                             IO_event (ExtCall «sys_fdok») [2w] [(i2, r2)];
                             IO_event (ExtCall «sys_listen») conf bs] ∧
      ¬MEM 0w [r0; r1; r2] ∧ ∀k. l0_ev_res bs ≠ SOME (Ok k)
End

(* R4′ for the proxy: on the honest L0 FFI, K = pf_sendwait (D23); hw the
   proxy's Level threshold (prog is the proxy built with it) *)
Definition l0_proxy_claim_def:
  l0_proxy_claim K hw a b prog ⇔
    ∀w0. l0_proxy_world w0 ⇒
      ∃beh. semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
          (stdio_closed beh ∨ proxy_listen_failed beh ∨
           ∃io pr. beh = Diverge io ∧ proxy_safe_l0 K hw a b pr io ∧
                   (F1_io io ∧ F2 w0 ∧ accepts_below io ⇒
                    proxy_live_l0 K pr w0 io ∧ proxy_pairs_l0 K pr io ∧
                    (accepts_lt (2 ** 62) io ⇒ conn_live_l0 w0 io)))
End
