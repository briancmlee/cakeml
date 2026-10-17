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
          opn = (λn hd. MEM hd (MAP FST (SND (S n)).tbl)) in
      (* no misuse *)
      (∀n. ehacts lfd lv n 0 (S n) (new_actions (log_of m) (H n)) ≠ NONE) ∧
      (* accepts only on its listener; connects only to b *)
      (∀n x r. MEM (x, r) (ps n) ⇒ (∀p. x = EConnect p ⇒ p = b) ∧ (∀l. x = EAccept l ⇒ l = lfd)) ∧
      (* the pairing: injective; every backend serves an accepted front *)
      (∀hd hd' c. pair hd = SOME c ∧ pair hd' = SOME c ⇒ hd = hd') ∧
      (∀n c. MEM c (hl_conn_handles (ps n)) ⇒
             ∃hd. pair hd = SOME c ∧ MEM hd (hl_acc_handles (ps n))) ∧
      (* SAFETY, the relay, exact at this layer (writes complete at once):
         each side was written what was read from the other, except that a
         refused backend was written nothing; an unpaired front is
         written nothing *)
      (∀n hd c. pair hd = SOME c ⇒
         (hl_sent c (ps n) = hl_read hd (ps n) ∨ hl_refused c (ps n) ∧ hl_sent c (ps n) = []) ∧
         hl_sent hd (ps n) = hl_read c (ps n)) ∧
      (∀n hd. MEM hd (hl_acc_handles (ps n)) ∧ pair hd = NONE ⇒ hl_sent hd (ps n) = []) ∧
      (* THE LEVEL GATE (design/45 §2.2, at the round's start): a round's
         Level queries come before its other actions; a paired handle is
         read only if its partner's Level was ≤ hw in that round *)
      (∀n pre x post. R n = pre ++ [x] ++ post ∧ is_level (FST x) ⇒ EVERY (is_level o FST) pre) ∧
      (∀n hd c k r. pair hd = SOME c ∧ MEM (ERead hd k, r) (R n) ⇒
                    ∃l. l ≤ hw ∧ MEM (ELevel c, ELvl l) (R n)) ∧
      (∀n hd c k r. pair hd = SOME c ∧ MEM (ERead c k, r) (R n) ⇒
                    ∃l. l ≤ hw ∧ MEM (ELevel hd, ELvl l) (R n)) ∧
      (* the gate is evaluated every round, and is all that holds a read
         back: an open paired handle whose partner is open has its
         partner's Level queried; a ready one, with the gate open, is read *)
      (∀n hd c. pair hd = SOME c ∧ opn n hd ∧ opn n c ⇒
                MEM (ELevel c) (new_actions (log_of m) (H n)) ∧
                MEM (ELevel hd) (new_actions (log_of m) (H n))) ∧
      (∀n hd c l. pair hd = SOME c ∧ opn (SUC n) hd ∧ up_at lfd lv ifds m W (SUC n) c ∧
                  hd ∈ (LAST (H (SUC n))).ready ∧ MEM (ELevel c, ELvl l) (R (SUC n)) ∧ l ≤ hw ⇒
                  ∃k. MEM (ERead hd k) (new_actions (log_of m) (H (SUC n)))) ∧
      (∀n hd c l. pair hd = SOME c ∧ opn (SUC n) hd ∧ up_at lfd lv ifds m W (SUC n) c ∧
                  c ∈ (LAST (H (SUC n))).ready ∧ MEM (ELevel hd, ELvl l) (R (SUC n)) ∧ l ≤ hw ⇒
                  ∃k. MEM (ERead c k) (new_actions (log_of m) (H (SUC n)))) ∧
      (* a front is not read before its backend is up *)
      (∀n hd k. MEM (ERead hd k) (new_actions (log_of m) (H n)) ∧ MEM hd (hl_acc_handles (ps n)) ⇒
                ∃c. pair hd = SOME c ∧ up_at lfd lv ifds m W n c) ∧
      (* LIVENESS, under connect fairness: every accepted front gets a
         backend that comes up or is refused.  (A socketless connect,
         option (b), is retried by the program) *)
      (conn_fair lfd lv ifds m W ⇒
       ∀n hd. MEM hd (hl_acc_handles (ps n)) ⇒
              ∃n' c. pair hd = SOME c ∧ (ever_up lfd lv ifds m W n' c ∨ hl_refused c (ps n')))
End

(* The proxy on the layer, in every proxy world with the run-local rely.
   pprog b hw / pifds b hw: the proxy's computation and interest (a pure
   step function, design/44) *)
Definition proxy_hl_claim_def:
  proxy_hl_claim pprog pifds ⇔
    ∀a b hw lfd lv W.
      proxy_world lfd a W ∧ run_rely lfd lv (pifds b hw) (pprog b hw) W ⇒
      proxy_guar_hl b hw lfd lv (pifds b hw) (pprog b hw) W
End

(* Through E1, along every run of the honest L1 (as client_l1_claim).
   [R1]: after E1's rebase, erounds/ecm/elv/pew take pol_never where they
   take hw here, and hw stays the proxy's own Level threshold *)
Definition proxy_l1_claim_def:
  proxy_l1_claim pprog pifds ⇔
    ∀a b lfd hw w0 calls.
      l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
      (∀n. SND (ecm lfd hw (pifds b hw) (pprog b hw) w0 n) + 1 < dimword (:64)) ∧
      (∀n. erounds lfd hw (pifds b hw) (pprog b hw) (w0, einit) n ≠ NONE) ⇒
      proxy_guar_hl b hw lfd (elv lfd hw (pifds b hw) (pprog b hw) w0)
        (pifds b hw) (pprog b hw) (pew lfd a hw (pifds b hw) (pprog b hw) w0 calls)
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
