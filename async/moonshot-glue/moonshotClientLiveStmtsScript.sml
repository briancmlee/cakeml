(*
  Moonshot liveness, the CLIENT's promise on its RAW L0 trace, as a
  STATEMENT for review (DRAFT, close-v2).  Nothing here is proved.

  A SEPARATE claim client_live_claim of the same program as the approved
  l0_client_claim (moonshotClientL0Stmts): same world class, same early
  outcomes, same safety part (client_safe_l0 with the same lc).
  l0_client_claim is unchanged.  This is the per-process form that
  moonshot-live's client obligations (moonshotLiveObs @ 3fd01a615:
  client_open, client_conn_ob) are lifted from, as the proxy's
  proxy_asks_claim (step 9 rev 9) is for proxy_pair_ob.

  ep i: the episode (l0sysEpisodes' number) that serves logical connection
  i, injective, with lc (ep i) = i, so client_safe_l0 already gives
  client_conn_ob's "never more than rq" clause.

  Per connection i < N, on ep i's channel c (fd f), unless an excuse:
   - OPEN: ep i is a connect to a;                     (client_open)
   - C-asks: the client asks on f infinitely often;     (client_conn_ob 1)
   - C-sends: if c drains, all of brequests (rqs i) is eventually taken
     by the kernel on ep i;                             (client_conn_ob 2)
   - C-reads: what has arrived on c is eventually returned by ep i's
     recvs.                                             (client_conn_ob 4)
  EXCUSES.  client_excuse (the whole run; each maps to a disjunct of
  moonshot-live's sys_excuse in the lift): a connect failed hard (not
  l1_transient, not EINPROGRESS: hard_fail «sys_connect»), a channel of the
  client broke (kern_broke: Break or ConnFail), a hard recv/send error on
  an episode (as the proxy's pos_hard_err; to kern_broke as for the proxy),
  or an episode timed out (D23: timed_out_sys).  For C-asks and C-sends
  also chan_frozen c: c has seen its peer's EOF, broke or closed
  (moonshot-live's `ended`; closes_ob turns a frozen end before the
  connection is done into X).  C-reads has no frozen escape: the client
  reads up to the EOF.  "Done" is no escape here: the client asks until it
  reads the EOF, so a done connection's end is frozen first, or never.
  A Terminate behaviour: the client stops only once every connection's
  handle has read its EOF (client_guar' TERMINATION), so every ep i is
  frozen and the asks clause holds by its escape.

  HYPOTHESES (the live block, as for the proxy, plus two for connects):
  F1_io, F2 w0, F1_connect_io (D41 (2) on the trace, keyed by port), and
  connects_settle (a pending connect eventually settles; on l0sys from
  kernel_fair_obs, moonshotLiveSetup.connect_settles).

  POL FAIRNESS (explicit).  The client binary runs L1 with pol_never, so
  the L0 claim needs no pol hypothesis.  The proof goes through a generic
  E1 lemma (to state next to client_l1_claim, which quantifies ∀pol) whose
  asks clause takes `pol_ok hw pol` as an explicit hypothesis (wants_input
  needs ¬pol ps f infinitely often while f's outbox is within hw); the
  binary discharges it with pol_ok_never.

  DEPENDS ON (A) (orchestrator decision, confirmed 2026-10-17; close-v2's
  next E1 change): a connect that fails at once, even transiently, closes
  its fd, takes no handle number (nxt unchanged) and adds no ecm channel.  Without (A) a transient failure costs the client a handle
  (ERefused), so unboundedly many transients (F1_connect allows any finite
  number before each non-transient outcome) can exhaust cbound with no
  excuse.  With (A) the client's handle count grows only on connects that
  return a socket, each of which either serves its connection or ends in an
  excuse or a frozen end, so cbound (2^63 > N) is never reached.
*)
Theory moonshotClientLiveStmts
Ancestors
  moonshotClientL0Stmts clientLiveCopy l0sysEpisodes honestL0Outcome honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   Episodes by number: fd, channel
   ------------------------------------------------------------------------ *)

(* The fd → latest episode map that ep_io threads (episodes on fd 0 get no
   bytes there, so they are not mapped) *)
Definition ep_opn_def:
  ep_opn (opn : (word64 # num) list) (n : num) [] = opn ∧
  ep_opn opn n (ev :: evs) =
    case ev_new ev of
    | SOME (f, _) => ep_opn (if f = 0w then opn else (f, n) :: opn) (n + 1) evs
    | NONE => ep_opn opn n evs
End

(* After evs, episode j holds fd f, which is on channel c *)
Definition ep_chan_at_def:
  ep_chan_at w0 evs j f c ⇔
    ∃w. ALOOKUP (ep_opn [] 0 evs) f = SOME j ∧ world_at w0 evs = SOME w ∧
        l0_chan_of w f = SOME c
End

(* ------------------------------------------------------------------------
   Excuses
   ------------------------------------------------------------------------ *)

(* A connect failed hard: not retried, and not "in progress" *)
Definition conn_hard_io_def:
  conn_hard_io (io : io_event llist) ⇔
    ∃i conf bs e x. LNTH i io = SOME (IO_event (ExtCall «sys_connect») conf bs) ∧
                    l0_ev_res bs = SOME (Fail e x) ∧ ¬l1_transient e ∧ e ≠ E_INPROGRESS
End

(* A channel broke (honestL1BStmts' broke) *)
Definition ch_broke_def:
  ch_broke w0 io c ⇔
    ∃evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
            c < LENGTH w.chans ∧ (EL c w.chans).broken
End

(* A hard recv/send error on episode j's fd while j holds it *)
Definition ep_hard_err_n_def:
  ep_hard_err_n w0 j io ⇔
    ∃evs ev f c. LPREFIX (fromList (evs ++ [ev])) io ∧ ep_chan_at w0 evs j f c ∧
                 hard_err_on f ev
End

(* D23's observed excuse for episode j (ep_timed_out by number) *)
Definition ep_timed_out_n_def:
  ep_timed_out_n K w0 j io ⇔
    ∃evs span f c.
      LPREFIX (fromList (evs ++ span)) io ∧ ep_chan_at w0 evs j f c ∧
      K ≤ n_out_polls f span ∧ EVERY (λe. poll_ev e ⇒ out_poll f e) span ∧
      ¬EXISTS (send_took f) span ∧ ¬EXISTS (λe. l0_event_closed e = SOME f) span
End

Definition client_excuse_def:
  client_excuse K w0 io ⇔
    conn_hard_io io ∨ (∃c. ch_broke w0 io c) ∨
    ∃j. ep_hard_err_n w0 j io ∨ ep_timed_out_n K w0 j io
End

(* ------------------------------------------------------------------------
   Hypotheses on the run (never trusted)
   ------------------------------------------------------------------------ *)

(* D41 (2), on the trace: connects to port p made infinitely often
   infinitely often have an outcome that is not retried *)
Definition F1_connect_io_def:
  F1_connect_io (io : io_event llist) ⇔
    ∀p. (∀i. ∃i' conf bs. i ≤ i' ∧ LNTH i' io = SOME (IO_event (ExtCall «sys_connect») conf bs) ∧
                          conf = pbytes p) ⇒
        (∀i. ∃i' conf bs. i ≤ i' ∧ LNTH i' io = SOME (IO_event (ExtCall «sys_connect») conf bs) ∧
                          conf = pbytes p ∧ ¬retried (IO_event (ExtCall «sys_connect») conf bs))
End

(* A pending connect eventually settles (up, or failed) *)
Definition connects_settle_def:
  connects_settle w0 io ⇔
    ∀evs w c. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
              c < LENGTH w.chans ∧ (EL c w.chans).connecting ⇒
              ∃evs' w'. LPREFIX (fromList evs') io ∧ world_at w0 evs' = SOME w' ∧
                        c < LENGTH w'.chans ∧ ¬(EL c w'.chans).connecting
End

(* ------------------------------------------------------------------------
   The promise, and the claim
   ------------------------------------------------------------------------ *)

Definition client_live_l0_def:
  client_live_l0 K a N rqs (ep : num -> num) w0 io ⇔
    ∀i. i < N ⇒
      (* OPEN *)
      (client_excuse K w0 io ∨
       ∃evs. LPREFIX (fromList evs) io ∧ l0_ep_role (ep i) evs = SOME (Connected a)) ∧
      ∀evs f c w.
        LPREFIX (fromList evs) io ∧ ep_chan_at w0 evs (ep i) f c ∧ world_at w0 evs = SOME w ⇒
        let L = (client_excuse K w0 io ∨ chan_frozen w0 io c) in
          (* C-asks *)
          (L ∨ asks_io f io) ∧
          (* C-sends *)
          (drains w0 io c ⇒
           L ∨ ∃evs'. LPREFIX (fromList evs') io ∧ brequests (rqs i) ≼ l0_ep_sent (ep i) evs') ∧
          (* C-reads *)
          (client_excuse K w0 io ∨
           ∃evs'. LPREFIX (fromList evs') io ∧ (EL c w.chans).peer_sent ≼ l0_ep_recvd (ep i) evs')
End

(* The claim, for the client binary cprog a c N rqs, with K L1's write
   timeout (pf_sendwait, D23).  Hypotheses and early outcomes as
   l0_client_claim; ep i is lc's inverse on i < N *)
Definition client_live_claim_def:
  client_live_claim K cprog ⇔
    ∀a c N rqs w0.
      2 ≤ N ∧ N < 2 ** 63 ∧ (∀i. EVERY valid_brequest (rqs i)) ∧
      a < 65536 ∧ c < 65536 ∧ c ≠ a ∧
      l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
      ∃beh. semantics_prog (init_state (l0_ffi w0)) init_env (cprog a c N rqs) beh ∧
            beh ≠ Fail ∧
            (stdio_closed beh ∨ l0_listen_failed beh ∨
             stdio_open (beh_io beh) ∧
             ∃lc ep. client_safe_l0 a c N rqs lc (beh_io beh) ∧
                     (∀i i'. i < N ∧ i' < N ∧ ep i = ep i' ⇒ i = i') ∧
                     (∀i. i < N ⇒ lc (ep i) = i) ∧
                     (F1_io (beh_io beh) ∧ F1_connect_io (beh_io beh) ∧ F2 w0 ∧
                      connects_settle w0 (beh_io beh) ⇒
                      client_live_l0 K a N rqs ep w0 (beh_io beh)))
End
