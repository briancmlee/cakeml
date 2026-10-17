(*
  Moonshot step 9 (design/45 §2.4): the proxy's guarantee on close-v2's
  endpoint HANDLE LAYER, as a STATEMENT for review (DRAFT).  Nothing is proved.

  Same pattern as the client (moonshotClientSpec, step 10): the guarantee
  is over the layer's history H n = ehhist lfd lv ifds m W n, in a world W
  with the run-local rely (run_rely, eh_round_ok); E1 carries it to L1's
  own history (proxy_l1_claim).  Level: the layer answers ELevel from an
  oracle lv, so every clause here holds for EVERY answer sequence; the
  bounded-buffer facts (S4_relay, the hw + pf_chunk bound) need true levels
  and are stated at L1 (honestL1PFS4w's draft additions).

  E1 AS IT STANDS vs AFTER ITS REBASE (close-v2, 3–4 days):
   [R1] honestL1EPModel takes hw where the current PF model takes pol; the
        proxy needs pol_never.  proxy_l1_claim below is written with hw
        (today's names); after the rebase hw becomes pol_never.
   [R2] E1's L1 has no stall_step (D23): the timeout excuse exists only on
        the raw trace (proxyL0Stmts.pos_timed_out) and at L1 after the
        rebase; at this layer writes complete at once, so there is none.
   [R3] The layer has no close or shutdown action (EAccept, EConnect,
        ERead, EWrite, ELevel): design/45's half-close, backend-EOF and
        closed-front clauses cannot be stated here; they are OWED (below),
        on both levels, once endpointHLModel has EClose / EShut.
   [R4] The rely is run_rely (eh_round_ok), as for the client: valid
        along the run's own rounds; nosock (option (b)) is the world's.

  REVISION 7 (user rulings): pairing liveness has the observed excuse
  "connects return no socket infinitely often" (hl_nosock; [F4] is not
  assumed).  The raw-trace bound is now exact, hw + pf_chunk + pread,
  with D23's timeout excuse (proxyL0Stmts).

  REVISION 4: the program takes its listener: pprog lfd b hw (it accepts
  on lfd, and polls it).

  REVISION 3: every condition on the program is one it can observe.  The
  world's up_at is replaced by hl_up (c has answered a read, so it was not
  refused): the program tells Up from Refused only by reading c, and that
  read is itself credit-gated on hd's Level.  (World facts remain only in
  conclusions: ever_up, and the connect liveness.)

  REVISION 2: a computation emits a round's actions before any of the
  round's results.  So (1) the relay lags one round: bytes read in round n
  are written in round n+1 (safety: prefixes; plus a one-round lag
  bound); (2) the Level gate is a CREDIT gate: the proxy reads hd in
  round n only if c's Level answered in round n−1, plus the bytes it
  writes to c in rounds n−1 and n, is ≤ hw (all known when round n's
  actions are emitted).  Bnd for the raw trace becomes hw + 3·pf_chunk.

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
Theory proxyHLStmts
Ancestors
  moonshotClientSpec endpointClients endpointHLModel honestL1EPRefine asyncCore
Libs
  preamble

(* Round n's (action, result) pairs, in a history with more than n
   snapshots *)
Definition hl_round_def:
  hl_round m (h : (word64, eresp) snapshot list) n =
    ZIP (new_actions (log_of m) (TAKE n h), (EL n h).results)
End

(* The handles accepted, in order *)
Definition hl_acc_handles_def:
  hl_acc_handles ps =
    FLAT (MAP (λ(x, r). case (x, r) of
                        | (EAccept l, EAccepted (SOME hd)) => [hd]
                        | _ => []) ps)
End

(* Bytes a round's actions ask to write on handle h *)
Definition wreq_def:
  wreq h (acts : eact list) =
    SUM (MAP (λa. case a of EWrite h' bs => if h' = h then LENGTH bs else 0 | _ => 0) acts)
End

(* Backend c has answered a read with data, would-block or EOF: it was not
   refused (the program's knowledge that c is up) *)
Definition hl_up_def:
  hl_up c ps ⇔ ∃k r. MEM (ERead c k, EGot r) ps
End

(* The connects that returned no socket (EConnected NONE) *)
Definition hl_nosock_def:
  hl_nosock (ps : (eact # eresp) list) = LENGTH (FILTER (λ(x, r). r = EConnected NONE) ps)
End

Definition is_level_def:
  is_level (x : eact) ⇔ ∃h. x = ELevel h
End

(* A proxy world: as a client world (pew_props), listening on a *)
Definition proxy_world_def:
  proxy_world lfd a (W : eworld) ⇔
    W.listening = [(lfd, a, [])] ∧ W.chans = [] ∧ W.open_fds = [] ∧ W.reserved = [] ∧
    no_backpressure W ∧ open_loop W ∧ alloc_ok W.alloc ∧ takes_ok W.takes
End

(* The guarantee.  pair hd = SOME c: front hd's backend is c *)
Definition proxy_guar_hl_def:
  proxy_guar_hl b hw lfd lv ifds m W ⇔
    ∃pair.
      let H = ehhist lfd lv ifds m W; S = ehst lfd lv ifds m W;
          ps = (λn. hl_pairs m (H n)); R = (λn. hl_round m (H (SUC n)) n);
          A = (λn. new_actions (log_of m) (H n));
          opn = (λn hd. MEM hd (MAP FST (SND (S n)).tbl)) in
      (* no misuse *)
      (∀n. ehacts lfd lv n 0 (S n) (new_actions (log_of m) (H n)) ≠ NONE) ∧
      (* accepts only on its listener; connects only to b *)
      (∀n x r. MEM (x, r) (ps n) ⇒ (∀p. x = EConnect p ⇒ p = b) ∧ (∀l. x = EAccept l ⇒ l = lfd)) ∧
      (* the pairing: injective; every backend serves an accepted front *)
      (∀hd hd' c. pair hd = SOME c ∧ pair hd' = SOME c ⇒ hd = hd') ∧
      (∀n c. MEM c (hl_conn_handles (ps n)) ⇒
             ∃hd. pair hd = SOME c ∧ MEM hd (hl_acc_handles (ps n))) ∧
      (* (rev 5) and only those: a pair is an accepted front and a connected
         backend, so no front is relayed to another front *)
      (∀hd c. pair hd = SOME c ⇒
              ∃n. MEM hd (hl_acc_handles (ps n)) ∧ MEM c (hl_conn_handles (ps n))) ∧
      (* SAFETY, the relay: each side has been written a prefix of what was
         read from the other; an unpaired front is written nothing *)
      (∀n hd c. pair hd = SOME c ⇒
         hl_sent c (ps n) ≼ hl_read hd (ps n) ∧ hl_sent hd (ps n) ≼ hl_read c (ps n)) ∧
      (* the relay lags one round: what was read by round n is written by
         round n + 1, unless that side was refused or has ended (read EOF:
         at this layer a break reads as an EOF) *)
      (∀n hd c. pair hd = SOME c ⇒
         (hl_read hd (ps n) ≼ hl_sent c (ps (SUC n)) ∨
          hl_refused c (ps (SUC n)) ∨ hl_eof c (ps (SUC n))) ∧
         (hl_read c (ps n) ≼ hl_sent hd (ps (SUC n)) ∨ hl_eof hd (ps (SUC n)))) ∧
      (∀n hd. MEM hd (hl_acc_handles (ps n)) ∧ pair hd = NONE ⇒ hl_sent hd (ps n) = []) ∧
      (* THE CREDIT GATE (design/45 §2.2, revised): a round's Level queries
         come before its other actions; a paired handle is read in round n
         only if its partner's Level answered in round n − 1, plus the bytes
         written to the partner in rounds n − 1 and n, is ≤ hw *)
      (∀n pre x post. R n = pre ++ [x] ++ post ∧ is_level (FST x) ⇒ EVERY (is_level o FST) pre) ∧
      (∀n hd c k. pair hd = SOME c ∧ MEM (ERead hd k) (A n) ⇒
                  0 < n ∧ ∃l. MEM (ELevel c, ELvl l) (R (n − 1)) ∧
                              l + wreq c (A (n − 1)) + wreq c (A n) ≤ hw) ∧
      (∀n hd c k. pair hd = SOME c ∧ MEM (ERead c k) (A n) ⇒
                  0 < n ∧ ∃l. MEM (ELevel hd, ELvl l) (R (n − 1)) ∧
                              l + wreq hd (A (n − 1)) + wreq hd (A n) ≤ hw) ∧
      (* the gate is evaluated every round, and is all that holds a read
         back: an open paired handle whose partner is open has its
         partner's Level queried; a ready one, with the gate open, is read *)
      (∀n hd c. pair hd = SOME c ∧ opn n hd ∧ opn n c ⇒
                MEM (ELevel c) (new_actions (log_of m) (H n)) ∧
                MEM (ELevel hd) (new_actions (log_of m) (H n))) ∧
      (∀n hd c l. pair hd = SOME c ∧ opn (SUC n) hd ∧ opn (SUC n) c ∧ hl_up c (ps (SUC n)) ∧
                  hd ∈ (LAST (H (SUC n))).ready ∧ MEM (ELevel c, ELvl l) (R n) ∧
                  l + wreq c (A n) + wreq c (A (SUC n)) ≤ hw ⇒
                  ∃k. MEM (ERead hd k) (A (SUC n))) ∧
      (∀n hd c l. pair hd = SOME c ∧ opn (SUC n) hd ∧ opn (SUC n) c ∧
                  c ∈ (LAST (H (SUC n))).ready ∧ MEM (ELevel hd, ELvl l) (R n) ∧
                  l + wreq hd (A n) + wreq hd (A (SUC n)) ≤ hw ⇒
                  ∃k. MEM (ERead c k) (A (SUC n))) ∧
      (* a front is read only once its backend has answered a read (so it
         was not refused; and it was up in the world) *)
      (∀n hd k. MEM (ERead hd k) (new_actions (log_of m) (H n)) ∧ MEM hd (hl_acc_handles (ps n)) ⇒
                ∃c. pair hd = SOME c ∧ hl_up c (ps n) ∧ ever_up lfd lv ifds m W n c) ∧
      (* LIVENESS, under connect fairness: every accepted front gets a
         backend that comes up or is refused, unless (rev 7, user: [F4] is
         not assumed) connects return no socket infinitely often.  (A
         socketless connect, option (b), is retried by the program) *)
      (conn_fair lfd lv ifds m W ⇒
       ∀n hd. MEM hd (hl_acc_handles (ps n)) ⇒
              (∃n' c. pair hd = SOME c ∧ (ever_up lfd lv ifds m W n' c ∨ hl_refused c (ps n'))) ∨
              ∀k. ∃n'. k ≤ hl_nosock (ps n'))
End

(* The proxy on the layer, in every proxy world with the run-local rely.
   pprog lfd b hw / pifds lfd b hw: the proxy's computation and interest (a pure
   step function, design/44) *)
Definition proxy_hl_claim_def:
  proxy_hl_claim pprog pifds ⇔
    ∀a b hw lfd lv W.
      proxy_world lfd a W ∧ run_rely lfd lv (pifds lfd b hw) (pprog lfd b hw) W ⇒
      proxy_guar_hl b hw lfd lv (pifds lfd b hw) (pprog lfd b hw) W
End

(* Through E1, along every run of the honest L1 (as client_l1_claim).
   [R1], applied: E1's erounds/ecm/elv/pew take the L1 policy pol_never;
   hw is the proxy's own Level threshold only *)
Definition proxy_l1_claim_def:
  proxy_l1_claim pprog pifds ⇔
    ∀a b lfd hw w0 calls.
      l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
      (∀n. SND (ecm lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0 n) + 1 < dimword (:64)) ∧
      (∀n. erounds lfd pol_never (pifds lfd b hw) (pprog lfd b hw) (w0, einit) n ≠ NONE) ⇒
      proxy_guar_hl b hw lfd (elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0)
        (pifds lfd b hw) (pprog lfd b hw) (pew lfd a pol_never (pifds lfd b hw) (pprog lfd b hw) w0 calls)
End

(* ------------------------------------------------------------------------
   The bite: unbounded_needed (design/45 §2.4).  The OLD proxy guarantee
   (endpointClients.proxy_guar, with its unconditional input_live) plus
   bounded buffering, with the same pairing, is met by NO program: in a
   world where the client keeps sending and the backend never reads, input
   liveness makes the proxy read without bound, and the bound forbids it
   ------------------------------------------------------------------------ *)
Definition proxy_guar_bnd_def:
  proxy_guar_bnd Bnd b w io ⇔
    ∃pair.
      (∀i i'. pair i = pair i' ⇒ i = i') ∧
      always (λevs. ∀i. ep_accepted evs i ⇒
                        (pair i < LENGTH (opened_fds evs) ⇒ ep_connected_to evs (pair i) b) ∧
                        ch_sent (pair i) evs ≼ ch_read i evs ∧
                        ch_sent i evs ≼ ch_read (pair i) evs) io ∧
      always (λevs. ∀i. ep_accepted evs i ⇒
                        LENGTH (ch_read i evs) ≤ LENGTH (ch_sent (pair i) evs) + Bnd ∧
                        LENGTH (ch_read (pair i) evs) ≤ LENGTH (ch_sent i evs) + Bnd) io ∧
      input_live w io
End

(* The claim to prove (the bite): for every bound, no program *)
Definition unbounded_needed_def:
  unbounded_needed ⇔
    ∀lfd a b Bnd. ¬∃prog. rg_spec (ep_server_world all_calls lfd a) (proxy_guar_bnd Bnd b) prog
End
