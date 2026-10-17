(*
  TEMPORARY VERBATIM COPY — remove at L3-09 fold.
  Source: final/L3-00-statements (PR #153) at 2333844ae (D23 comments; 5113fff27 D23: ep_timed_out,
  stall_drains, poll_ev/out_poll/send_took; hup_drains and poll_hup removed;
  earlier: drains on sends/inflight 821835ed2; Q1 quiescence weakening; D20
  poll encoding; first copied at 676781133, resynced for ep_polls,
  l0_close_call and ep_ends), async/kernel/statements/kernelStatementsCoreScript.sml and
  kernelStatementsScript.sml (split since 61e7733e9), the raw-trace
  definitions (ev_lcall … echo2_guar_l0), copied unchanged so that L3-09 (S3) can be
  proved on spike/l3-quiet, where kernelStatements is not available.
  If #153's statements change, resync this copy.
  Approved by the coordinator (2026-10-16; user policy: temporary copies
  are fine if recorded and removed at merge).
*)
Theory honestL1BStmts
Ancestors
  llist ffi semantics ml_prog
  honestL0 honestL0World honestL0WorldProps honestL0Rely honestL0Part
  honestL1Model honestL1PFModel honestL1PFRound honestL1PFStream honestL1PFConnRun
  honestEchoL0Spec
Libs
  preamble

(* An IO event as the call the L0 world recorded *)
Definition ev_lcall_def:
  ev_lcall (IO_event nm conf bs) =
    ((case nm of ExtCall n => n | _ => «»), conf, MAP FST bs : word8 list)
End

(* The L0 world after the events evs *)
Definition world_at_def:
  world_at w0 evs = l0_replay w0 (MAP ev_lcall evs)
End

(* [F1] (D11′, approved), on the program's IO trace: per call kind and per
   fd, a call made infinitely often does not return a retried outcome
   infinitely often (honestL1PFLive.F1, read off the trace) *)
Definition F1_io_def:
  F1_io (io : io_event llist) ⇔
    ∀nm f.
      (∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ ev_on nm f ev) ⇒
      (∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ ev_on nm f ev ∧ ¬retried ev)
End

(* [F2] (D12, approved): with nothing in flight, a send takes a byte *)
Definition F2_def:
  F2 (w0 : l0world) ⇔ ∀j h n. 0 < n ⇒ 0 < w0.ch.takes j h 0 n
End

(* D(c), per episode (not trusted; the condition under which service is
   owed, D4): the peer reads what it was sent.  If nothing more is sent on
   channel c after a prefix, c's bytes in flight eventually reach 0.
   (Corrected 2026-10-17: the earlier form, "while bytes are in flight, the
   peer's read count `drained` later grows", was satisfied by a peer that
   only makes zero-byte reads, since LDrain j 0 counts as a read; under it
   the echo's replies could stall for ever.  This is the trace form of
   honestL1PFFlush's drains.) *)
Definition drains_def:
  drains w0 io c ⇔
    ∀evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧ c < LENGTH w.chans ∧
            (∀evs' w'. LPREFIX (fromList (evs ++ evs')) io ∧
                       world_at w0 (evs ++ evs') = SOME w' ⇒
                       (EL c w'.chans).sent = (EL c w.chans).sent) ⇒
            ∃evs' w'. LPREFIX (fromList (evs ++ evs')) io ∧
                      world_at w0 (evs ++ evs') = SOME w' ∧
                      c < LENGTH w'.chans ∧ (EL c w'.chans).inflight = 0
End

(* The listen failed and the program stopped *)
Definition listen_failed_def:
  listen_failed b ⇔
    ∃conf bs. b = Terminate Success [IO_event (ExtCall «sys_listen») conf bs] ∧
              ∀k. l0_ev_res bs ≠ SOME (Ok k)
End

(* Episode j (the j-th accepted connection) is open after evs, or has
   ended, as echo_safe_l0's episodes (l0_ep_events): an episode ends at a
   successful close of its fd, or at a later accept that returns its fd
   (after an interrupted close that freed it) *)
Definition ep_ends_def:
  ep_ends f e ⇔ l0_event_closed e = SOME f ∨ l0_event_accepted e = SOME f
End

Definition ep_open_def:
  ep_open j evs ⇔
    ∃pre ev post f.
      evs = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
      l0_event_accepted ev = SOME f ∧ EVERY (λe. ¬ep_ends f e) post
End

Definition ep_closed_def:
  ep_closed j evs ⇔
    ∃pre ev post f.
      evs = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
      l0_event_accepted ev = SOME f ∧ EXISTS (ep_ends f) post
End

(* A hard (not retried) error from a recv or send on fd f *)
Definition hard_err_on_def:
  hard_err_on f (IO_event nm conf bs) ⇔
    (nm = ExtCall «sys_recv» ∨ nm = ExtCall «sys_send») ∧ 8 ≤ LENGTH conf ∧
    bytes_fd (TAKE 8 conf) = f ∧
    ∃e x. l0_ev_res bs = SOME (Fail e x) ∧ ¬l1_transient e
End

(* D16's excuse, observed: a hard error on episode j's fd while it was open *)
Definition ep_hard_err_def:
  ep_hard_err j io ⇔
    ∃evs ev. LPREFIX (fromList (evs ++ [ev])) io ∧ ep_open j evs ∧
             hard_err_on (EL j (l0_accepted evs)) ev
End

(* Channel c broke (a queued connection dropped: aborted, or reset under
   EMFILE) *)
Definition broke_def:
  broke w0 io c ⇔
    ∃evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
            c < LENGTH w.chans ∧ (EL c w.chans).broken
End

(* Fewer than 2^64 - 1 connections are accepted in the whole run.  After
   that many, the L1 loop stops making calls (coordinator decision (A), over
   wrapping the handle counter), so no liveness is owed past it *)
Definition accepts_below_def:
  accepts_below (io : io_event llist) ⇔
    ∀evs. LPREFIX (fromList evs) io ⇒ LENGTH (l0_accepted evs) < 2 ** 64 − 1
End

(* A poll event *)
Definition poll_ev_def:
  poll_ev ev ⇔ ∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs
End

(* A poll that lists fd f for output (an entry (f, e), read back to the
   model's bits by pe_fe, with bit 2 of e set).  L1 polls f for output
   exactly in the rounds in which f's outbox is not empty (pf_poll_set);
   one poll per round (D20) *)
Definition out_poll_def:
  out_poll f ev ⇔
    ∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs ∧
              ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧
                  2 ≤ e MOD 4
End

(* The polls in a list of events that list fd f for output; idle polls
   (which a blocking L1 collapses) never count *)
Definition n_out_polls_def:
  n_out_polls f (evs : io_event list) = LENGTH (FILTER (out_poll f) evs)
End

(* A send on fd f from which the kernel took bytes *)
Definition send_took_def:
  send_took f (IO_event nm conf bs) ⇔
    nm = ExtCall «sys_send» ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = f ∧
    ∃k. l0_ev_res bs = SOME (Ok k) ∧ 0 < k
End

(* A call that closes fd f, whatever its result (an interrupted close may
   still free the fd, and L1 forgets f at its close call either way) *)
Definition l0_close_call_def:
  l0_close_call f (IO_event nm conf bs) ⇔
    nm = ExtCall «sys_close» ∧ LENGTH conf = 8 ∧ bytes_fd conf = f
End

(* The events of more before L1's first close call on fd f, after pre
   (none if pre has one): the part of more in which the episode holding f
   is still open *)
Definition ep_polls_def:
  ep_polls f (pre : io_event list) (more : io_event list) =
    if EXISTS (l0_close_call f) pre then []
    else FST (SPLITP (l0_close_call f) more)
End

(* D23 (user decision, the write timeout; replaces D19's hang-up policy):
   L1 drops the outbox of a fd it holds, and marks the fd gone, after K =
   pf_sendwait consecutive rounds with a non-empty outbox from which no
   send took bytes (honest-ffi's stall_step; the count restarts on
   progress or an empty outbox).  On the trace, with one poll per round
   (D20), that is: while episode j holds its fd f, a stretch of events
   with at least K polls, every one of them listing f for output, and no
   send on f that took bytes.  This is the OBSERVED excuse of the main
   form (as D16's hard error is): an L1 close need not follow, since a
   gone fd is closed only when the server closes it, and the stretch alone
   is exactly the condition under which L1 drops *)
Definition ep_timed_out_def:
  ep_timed_out K j io ⇔
    ∃evs span.
      LPREFIX (fromList (evs ++ span)) io ∧ ep_open j evs ∧
      K ≤ n_out_polls (EL j (l0_accepted evs)) span ∧
      EVERY (λe. poll_ev e ⇒ out_poll (EL j (l0_accepted evs)) e) span ∧
      ¬EXISTS (send_took (EL j (l0_accepted evs))) span ∧
      ¬EXISTS (ep_ends (EL j (l0_accepted evs))) span
End

(* The strong form's hypothesis instead (D23, generalising D19's
   user-approved b″ form from "after a hang-up" to "always"): whenever
   channel c has bytes in flight, its peer reads them all within K − 1
   polls that list episode j's fd for output while j holds it (only polls
   before j's close count, since the fd number may be reused after it).
   With [F2] (nothing in flight: a send takes a byte) this gives send
   progress before L1's timeout *)
Definition stall_drains_def:
  stall_drains K w0 io j c ⇔
    ∀evs mid w.
      LPREFIX (fromList (evs ++ mid)) io ∧ ep_open j evs ∧
      world_at w0 (evs ++ mid) = SOME w ∧ c < LENGTH w.chans ∧
      0 < (EL c w.chans).inflight ⇒
      ∃more w'. LPREFIX (fromList (evs ++ mid ++ more)) io ∧
                n_out_polls (EL j (l0_accepted evs))
                  (ep_polls (EL j (l0_accepted evs)) mid more) < K ∧
                world_at w0 (evs ++ mid ++ more) = SOME w' ∧ c < LENGTH w'.chans ∧
                (EL c w'.chans).inflight = 0
End

(* Raw liveness of the echo, per episode, unless X: if episode j is open on
   channel c after evs, c's peer drains, and the episode hypothesis D holds,
   then everything c's peer has sent so far is eventually sent back (taken
   by the kernel), and if the peer has closed its side, the episode is
   eventually closed *)
Definition echo_live_unless_def:
  echo_live_unless D X w0 io ⇔
    ∀evs j c w.
      LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
      l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧ drains w0 io c ∧ D j c ⇒
      X j c ∨
      ((∃evs'. LPREFIX (fromList evs') io ∧ (EL c w.chans).peer_sent ≼ l0_sent j evs') ∧
       ((EL c w.chans).peer_eof ⇒ ∃evs'. LPREFIX (fromList evs') io ∧ ep_closed j evs'))
End

(* Accepts fail infinitely often (D18's disjunct (c)) *)
Definition accepts_fail_io_def:
  accepts_fail_io (io : io_event llist) ⇔
    ∀i. ∃i' conf bs e x. i ≤ i' ∧
        LNTH i' io = SOME (IO_event (ExtCall «sys_accept») conf bs) ∧
        l0_ev_res bs = SOME (Fail e x)
End

(* Raw liveness for connections, unless X (D18): a connection queued on a
   listener is eventually accepted (an accepted fd names it) or dropped (it
   broke: aborted, or reset under EMFILE) *)
Definition conn_live_unless_def:
  conn_live_unless X w0 io ⇔
    ∀evs w l p q j0.
      LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
      MEM (l, p, q) w.listeners ∧ MEM j0 q ⇒
      X ∨
      (∃evs' w' f. LPREFIX (fromList evs') io ∧ world_at w0 evs' = SOME w' ∧
                   ALOOKUP w'.open_fds f = SOME j0 ∧ MEM f (l0_accepted evs')) ∨
      broke w0 io j0
End

(* The main (weakened) forms *)
Definition echo_live_l0_def:
  echo_live_l0 K w0 io ⇔
    echo_live_unless (λj c. T) (λj c. ep_hard_err j io ∨ ep_timed_out K j io) w0 io
End

Definition conn_live_l0_def:
  conn_live_l0 w0 io ⇔ conn_live_unless (accepts_fail_io io) w0 io
End

(* R4′, the template: the echo server with close, on the honest L0 FFI;
   K is L1's write timeout pf_sendwait (D23) *)
Definition l0_echo2_claim_def:
  l0_echo2_claim K prog ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃b. semantics_prog (init_state (l0_ffi w0)) init_env prog b ∧
          (listen_failed b ∨
           ∃io. b = Diverge io ∧ echo_safe_l0 io ∧
                (F1_io io ∧ F2 w0 ∧ accepts_below io ⇒ echo_live_l0 K w0 io ∧ conn_live_l0 w0 io))
End

(* ------------------------------------------------------------------------
   The corollary forms, under explicit hypotheses (never trusted)
   ------------------------------------------------------------------------ *)

(* D16's hypothesis HD16, read off the trace: a recv on f that fails with
   a hard (not retried) error happens only on a channel that really broke
   and lost its unread input (honestL1PFStream.flushed) *)
Definition HD16_io_def:
  HD16_io w0 io ⇔
    ∀evs conf bs f w.
      LPREFIX (fromList (evs ++ [IO_event (ExtCall «sys_recv») conf bs])) io ∧
      hard_err_on f (IO_event (ExtCall «sys_recv») conf bs) ∧
      world_at w0 (evs ++ [IO_event (ExtCall «sys_recv») conf bs]) = SOME w ⇒
      flushed w f
End

(* D16's corollary excuse: channel c broke and its unread input was
   discarded (a genuine reset) *)
Definition flushed_ch_def:
  flushed_ch w0 io c ⇔
    ∃evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
            c < LENGTH w.chans ∧ (EL c w.chans).broken ∧ (EL c w.chans).inbox = []
End

(* D18's H1, read off the trace: an accept that fails with an error L1
   does not keep (kept_err: retried, EMFILE, ENFILE) really removed a
   connection from the listener's queue *)
Definition H1_io_def:
  H1_io w0 io ⇔
    ∀evs conf bs e x w w' l p q p' q'.
      LPREFIX (fromList (evs ++ [IO_event (ExtCall «sys_accept») conf bs])) io ∧
      l0_ev_res bs = SOME (Fail e x) ∧ ¬kept_err e ∧
      world_at w0 evs = SOME w ∧
      world_at w0 (evs ++ [IO_event (ExtCall «sys_accept») conf bs]) = SOME w' ∧
      LENGTH conf = 8 ∧ l = bytes_fd conf ∧
      MEM (l, p, q) (l0_tick «sys_accept» w).listeners ∧ q ≠ [] ∧
      MEM (l, p', q') w'.listeners ⇒
      ∃j. MEM j q ∧ ¬MEM j q'
End

(* D18's H3 (H3′, the JOINT weak form), read off the trace: accepts on l
   made infinitely often infinitely often fail with no kept error *)
Definition H3_io_def:
  H3_io (io : io_event llist) ⇔
    ∀l. (∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ ev_on «sys_accept» l ev) ⇒
        (∀i. ∃i' conf bs. i ≤ i' ∧
             LNTH i' io = SOME (IO_event (ExtCall «sys_accept») conf bs) ∧
             ev_on «sys_accept» l (IO_event (ExtCall «sys_accept») conf bs) ∧
             ∀e x. l0_ev_res bs = SOME (Fail e x) ⇒ ¬kept_err e)
End

Definition l0_echo2_strong_claim_def:
  l0_echo2_strong_claim K prog ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃b. semantics_prog (init_state (l0_ffi w0)) init_env prog b ∧
          (listen_failed b ∨
           ∃io. b = Diverge io ∧
                (F1_io io ∧ F2 w0 ∧ accepts_below io ∧ HD16_io w0 io ⇒
                 echo_live_unless (λj c. stall_drains K w0 io j c) (λj c. flushed_ch w0 io c)
                   w0 io) ∧
                (F1_io io ∧ accepts_below io ∧ H1_io w0 io ∧ H3_io io ⇒
                 conn_live_unless F w0 io))
End

(* ========================================================================
   quiet_on_kernel, and the HUP bite
   ======================================================================== *)

(* Asleep: stopped inside a blocking poll that never returns *)
Definition asleep_l0_def:
  asleep_l0 b io ⇔
    ∃conf bs. b = Terminate (FFI_outcome (Final_event (ExtCall «sys_poll») conf bs
                                           FFI_diverged)) io
End

(* Finitely many arrivals: from some step on, nothing arrives *)
Definition arrivals_finite_l0_def:
  arrivals_finite_l0 (w0 : l0world) ⇔ ∃N. ∀n h nm. N ≤ n ⇒ w0.env n h nm = []
End

(* quiet_on_kernel: guar holds whether the program runs forever or sleeps;
   with finitely many arrivals it sleeps, unless [F1] fails or accepts fail
   infinitely often (D18's excuse: under EMFILE/ENFILE a blocking L1 keeps
   retrying the accept, so a correct program may never sleep).  There is no
   POLLHUP disjunct: a blocking poll never lists a hung-up fd.  An fd at EOF
   is not polled for input (the server is told and reads the EOF, which
   closes it), and the blocking L1 blocks only when no fd it holds has
   output pending; D23's write timeout ends every stalled flush, so this is
   eventually the case.  hup_spin_bite below is why a fd that stays in the
   blocking set would be fatal *)
Definition quiet_on_kernel_claim_def:
  quiet_on_kernel_claim guar prog ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃b. semantics_prog (init_state (l0_ffi w0)) init_env prog b ∧
          (listen_failed b ∨
           (∃io. b = Diverge io ∧ guar w0 io) ∨
           (∃io. asleep_l0 b io ∧ guar w0 (fromList io))) ∧
          (arrivals_finite_l0 w0 ⇒
           listen_failed b ∨ (∃io. asleep_l0 b io) ∨
           ∃io. b = Diverge io ∧ (¬F1_io io ∨ accepts_fail_io io))
End

(* The corollary form (D18, as l0_echo2_strong_claim's): under H1 and the
   joint weak H3, read off the trace, the accepts excuse goes.  ("Accepts
   fail only finitely often" as a premise on the trace would only restate
   the main form: ¬accepts_fail_io io ⇒ ¬F1_io io is its disjunct) *)
Definition quiet_on_kernel_strong_claim_def:
  quiet_on_kernel_strong_claim guar prog ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃b. semantics_prog (init_state (l0_ffi w0)) init_env prog b ∧
          (listen_failed b ∨
           (∃io. b = Diverge io ∧ guar w0 io) ∨
           (∃io. asleep_l0 b io ∧ guar w0 (fromList io))) ∧
          (arrivals_finite_l0 w0 ⇒
           listen_failed b ∨ (∃io. asleep_l0 b io) ∨
           ∃io. b = Diverge io ∧ (H1_io w0 io ∧ H3_io io ⇒ ¬F1_io io))
End

(* The echo's guarantee, for its quiet instance *)
Definition echo2_guar_l0_def:
  echo2_guar_l0 K w0 io ⇔
    echo_safe_l0 io ∧ (F1_io io ∧ F2 w0 ∧ accepts_below io ⇒ echo_live_l0 K w0 io ∧ conn_live_l0 w0 io)
End
