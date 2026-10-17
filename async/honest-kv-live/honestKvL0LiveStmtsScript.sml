(*
  KV's guarantee of LIVENESS on its RAW L0 trace, as a STATEMENT for review
  (DRAFT).  Nothing here is proved.

  A SEPARATE claim kv_live_claim of the KV program, with the same world
  class (l0_server_world) and outcome shape as honestHttpKvL0Spec's
  kv_l0_claim, and the same hypothesis block as the echo's
  l0_echo2_claim (F1_io, F2, accepts_below).  kv_l0_claim is unchanged.

  Besides the accept clause conn_live_l0 (decision 8), it is what
  moonshot-live's kv_ob (moonshotLiveObs @45bcdb9b0) needs from KV, per accepted episode j on channel c (fd f), on the program's own
  trace (the lift to the system forms is shared work, N1 + N2, as for the
  other programs):
   - K-answers (kv_answers): once c drains, for every list of valid
     requests rqs whose bytes c's peer has sent, KV eventually has
     LENGTH rqs replies taken by the kernel on episode j (count only:
     WHICH replies is kv_safe_l0's);
   - K-asks: once c drains, KV asks on f (a recv on f, or a poll listing f
     for input) infinitely often.

  Vocabulary: the echo's (honestL1BStmts: drains, ep_open, ep_hard_err,
  ep_timed_out, flushed_open, F1_io, F2, accepts_below, world_at) and
  HttpSpecBodies / HttpKvSpec (valid_brequest, brequests, reply_bytes), all
  reused unchanged.  asks_ev / asks_io_on are proxyL0Stmts' in_ask /
  asks_io (rev 9, spike/proxy-asks), and ch_frozen its chan_frozen, copied
  under new names (that branch is not an ancestor here); unify at the merge.

  DECISION RECORD (statement choices; options and what ruled each out)
  1. Shape: a separate claim, like proxy_asks_claim (rev 9), not a change
     to kv_l0_claim: kv_l0_claim is being proved by e1-driver (kv_l0_safe),
     and a separate claim leaves it untouched.
  2. Excuses (X) are only the approved kinds: D16 ep_hard_err, D23
     ep_timed_out (K = pf_sendwait), D28/D32 flushed_open (only for
     K-answers: a request lost when the kernel discards the unread input is
     never answered).  accepts_below is a hypothesis, as in l0_echo2_claim.
     The asks clause also has kv_ob's own escape `ended` (the end is
     frozen: peer EOF, broken or closed), read on the trace as ch_frozen c
     ∨ ep_closed j; this is not an excuse, since kv_ob has it as L = X ∨
     ended.  Needed: after reading EOF, KV drops f from its interest (D26)
     and stops asking.  ep_closed maps to `closed` within `ended`.  For
     asks, flushed_open is not needed: it implies broken, so ch_frozen.
  3. Invalid input.  KV's handler (asyncKvHandler.kv_handler) stops on a
     request that cannot be parsed (BInvalid ⇒ return ()), so after one
     KV never reads f again, L1's inbox of f stays non-empty, and L1 stops
     asking on f.  So K-asks is false without something about the input.
     Options:
      (a) hypothesis peer_valid w0 io c: what c's peer has sent is always
          a prefix of the bytes of some list of valid requests.  CHOSEN.
          It is conditional, like drains, not an excuse.  At system level
          it follows from the client sending brequests rq (C-sends) and the
          proxy relaying prefixes (proxy_safe_l0), i.e. from safety.
      (b) an observed excuse "episode j read bytes that are no prefix of
          valid requests".  Ruled out: a new excuse kind (the approved
          ones are D16, D23, D28/D32 and accepts_below).
      (c) change KV to keep reading after invalid input.  Ruled out: it
          changes a program whose safety is proved and pushed (P4), for
          a case the moonshot never reaches.
     K-answers needs no such hypothesis: rqs are answered before any
     invalid bytes that follow them are reached.
     Challenge round (orchestrator, on 80462395a): (a) accepted.  POST-[R3]
     improvement, not now: a real KV server CLOSES a connection on invalid
     input; once [R3]'s EClose exists, that program change replaces
     peer_valid by the `ended` escape (ep_ended).
  4. Answers: count only (LENGTH ans = LENGTH rqs ∧ reply_bytes ans ≼
     l0_sent j evs′), exactly kv_answers' form, rather than the replies
     themselves.  Ruled out: restating kv_safe_l0's content (which replies),
     since kv_l0_claim already gives it on the same trace.
  5. Arrived bytes are the peer's sent bytes (EL c w.chans).peer_sent, as
     in echo_live_unless (not the kernel's delivered count, which is
     system-level vocabulary): the world ↔ system correspondence for
     peer_sent is the shared N2 lift.
  6. No close-liveness clause (echo's "peer EOF ⇒ a close call").  Ruled
     out for now: kv_ob does not need it; KV's closing is closes_ob's
     ([R3], joint, pending close/shutdown).
  7. No port parameter: nothing in the claim reads it (kv_l0_claim's port
     is for l0_topology, which this claim does not repeat).
  8. Accept clause (orchestrator, from moonshot-live's lift scoping G1):
     every connection queued at KV's listener is eventually accepted or
     breaks, unless accepts keep failing: conn_live_l0, exactly the
     echo's (l0_echo2_claim) and the proxy's, under the same hypotheses
     (F1_io, F2, accepts_below).  No new excuse kind.  Ruled out: a
     KV-specific accept form (moonshot-live's lift reads conn_live_l0).
     Proof plan: honestL1PFConnRun's pf_conn_live with KV's S1 (kv_S1),
     S2 (queue progress for the live interest, from cf-actions' port) and
     F1 (F1_io_F1), as honestEchoL0Live.echo_conn_live(_trace).
*)
Theory honestKvL0LiveStmts
Ancestors
  honestL1BStmts honestHttpKvL0Spec honestEchoL0Spec honestL0 honestL0World

Libs
  preamble

(* The program ASKS on fd f at event ev: a recv on f, or a poll listing f
   for input (bit 0 of its events, read back by pe_fe as in out_poll).
   proxyL0Stmts' in_ask; l0sysFair.asks_in on the program's own trace *)
Definition asks_ev_def:
  asks_ev f ev ⇔
    (∃conf bs. ev = IO_event (ExtCall «sys_recv») conf bs ∧ LENGTH conf = 8 ∧
               bytes_fd conf = f) ∨
    (∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs ∧
               ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e)
End

(* Infinitely often (proxyL0Stmts' asks_io) *)
Definition asks_io_on_def:
  asks_io_on f (io : io_event llist) ⇔ ∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ asks_ev f ev
End

(* Channel c is frozen on some prefix: its peer's EOF has arrived, or it is
   broken or closed (moonshot-live's `ended`; proxyL0Stmts' chan_frozen) *)
Definition ch_frozen_def:
  ch_frozen w0 io c ⇔
    ∃evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧ c < LENGTH w.chans ∧
            ((EL c w.chans).peer_eof ∨ (EL c w.chans).broken ∨ (EL c w.chans).closed)
End

(* Episode j has ended on some prefix (its fd closed, or reused by a later
   accept) *)
Definition ep_ended_def:
  ep_ended j io ⇔ ∃evs. LPREFIX (fromList evs) io ∧ ep_closed j evs
End

(* Decision 3 (a): what c's peer has sent is, at every point, a prefix of
   the bytes of some list of valid requests (a hypothesis, like drains) *)
Definition peer_valid_def:
  peer_valid w0 io c ⇔
    ∀evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧ c < LENGTH w.chans ⇒
            ∃rqs. EVERY valid_brequest rqs ∧ (EL c w.chans).peer_sent ≼ brequests rqs
End

(* KV's raw liveness, per episode j open on channel c (fd f) after evs,
   once c drains:
    - K-answers: every list rqs of valid requests whose bytes c's peer has
      sent by then eventually has LENGTH rqs replies taken by the kernel
      on episode j, unless D16 / D23 / D28-D32 on episode j;
    - K-asks: if c's peer sends only valid requests, KV asks on f
      infinitely often, unless D16 / D23 on episode j, or the end has
      ended (c frozen, or episode j ended).
   Why it should hold (honest L1 with pol_self, D26 live interest): L1
   polls f for input in every round in which f is in the interest (until
   KV reads its EOF), its inbox is empty and its outbox is ≤ hw; KV's
   handler reads f whenever its buffer holds no complete request
   (BIncomplete), and answers each complete one in the round it parses it
   (reply-only writes), so the inbox empties; drains + [F2] bring the
   outbox to ≤ hw infinitely often, unless D23 times f out *)
Definition kv_live_l0_def:
  kv_live_l0 K w0 io ⇔
    ∀evs j c w.
      LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
      l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧ drains w0 io c ⇒
      (* K-answers *)
      (∀rqs. EVERY valid_brequest rqs ∧ brequests rqs ≼ (EL c w.chans).peer_sent ⇒
             ep_hard_err j io ∨ ep_timed_out K j io ∨ flushed_open w0 io j c ∨
             ∃evs' ans. LPREFIX (fromList evs') io ∧ LENGTH ans = LENGTH rqs ∧
                        reply_bytes ans ≼ l0_sent j evs') ∧
      (* K-asks *)
      (peer_valid w0 io c ⇒
         ep_hard_err j io ∨ ep_timed_out K j io ∨ ch_frozen w0 io c ∨ ep_ended j io ∨
         asks_io_on (EL j (l0_accepted evs)) io)
End

(* The claim: KV on the honest L0 FFI, K = L1's write timeout pf_sendwait
   (D23); same world class and outcome shape as kv_l0_claim; with the
   echo's accept clause conn_live_l0 (decision 8) *)
Definition kv_live_claim_def:
  kv_live_claim K (prog : dec list) ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃io. (semantics_prog (init_state (l0_ffi w0)) init_env prog (Diverge io) ∧
            (F1_io io ∧ F2 w0 ∧ accepts_below io ⇒ kv_live_l0 K w0 io ∧ conn_live_l0 w0 io)) ∨
           (∃pre ev. stdio_open (fromList pre) ∧ LENGTH pre = 3 ∧ l0_listen_failed_ev ev ∧
                     io = fromList (pre ++ [ev]) ∧
                     semantics_prog (init_state (l0_ffi w0)) init_env prog
                       (Terminate Success (pre ++ [ev]))) ∨
           (∃evs. stdio_closed (Terminate Success evs) ∧ io = fromList evs ∧
                  semantics_prog (init_state (l0_ffi w0)) init_env prog
                    (Terminate Success evs))
End
