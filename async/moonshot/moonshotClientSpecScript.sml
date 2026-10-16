(*
  The moonshot's client, step 10 (design/45 §2.5): its guarantee, as a
  STATEMENT for review.  Nothing here is proved.

  LEVEL.  The client is a computation m on close-v2's endpoint HANDLE LAYER
  (endpointHLModel): it emits actions on handles (EConnect, ERead, EWrite;
  handles are never reused) and sees, each round, the results and the
  ready handles.  Its guarantee is stated over the layer's history
  ehhist lfd ifds m W n in a world W: so E1 (honestL1EPRefine,
  l1ep_refines_ehl) carries it to the honest L1 unchanged, because along
  every L1 run the layer's history in the run-built world pew IS L1's
  history.  (The raw L0 trace is a further transfer, as KV's step 11.)

  THE RELY is run-local (design/45 §2.5, as E1 delivers it): the world's
  arrivals are valid along the run's own rounds (eh_round_ok), not for
  every call sequence (ep_rely).

  FAILURES, per handle (an EPISODE):
   - a connect may get NO SOCKET (EConnected NONE: the world's nosock,
     #157): no episode; the client tries again;
   - a connect may be REFUSED (ERead gives ERefused, once; the handle is
     closed): the client tries again (nothing was sent on it: writes wait
     for the settle);
   - an Up connection may BREAK: at this level a break reads as an EOF
     (L1 maps a reset to EOF): the client stops using that handle and does
     not retry (bytes may have been sent; resending could repeat writes).

  The vocabulary: the round-by-round (action, result) pairs of a history,
  and per handle the bytes written and read, EOF, refusal.
*)
Theory moonshotClientSpec
Ancestors
  endpointHLModel honestL1EPRefine HttpSpec HttpSpecBodies asyncLevel1 asyncCore
Libs
  preamble

(* ------------------------------------------------------------------------
   The vocabulary of a handle-layer history
   ------------------------------------------------------------------------ *)

(* Round k's actions (emitted with the first k snapshots), each with its
   result (in snapshot k) *)
Definition hl_pairs_def:
  hl_pairs m (h : (word64, eresp) snapshot list) =
    FLAT (GENLIST (λk. ZIP (new_actions (log_of m) (TAKE k h), (EL k h).results))
                  (LENGTH h))
End

(* What the client wrote on handle hd: of each write, the bytes taken *)
Definition hl_sent_def:
  hl_sent hd ps =
    FLAT (MAP (λ(x, r). case (x, r) of
                        | (EWrite h' bs, EWrote k) => if h' = hd then TAKE k bs else []
                        | _ => []) ps)
End

(* What it read on hd *)
Definition hl_read_def:
  hl_read hd ps =
    FLAT (MAP (λ(x, r). case (x, r) of
                        | (ERead h' n, EGot (SOME d)) => if h' = hd then d else []
                        | _ => []) ps)
End

Definition hl_eof_def:
  hl_eof hd ps ⇔ ∃n. MEM (ERead hd n, EGot (SOME [])) ps
End

Definition hl_refused_def:
  hl_refused hd ps ⇔ ∃n. MEM (ERead hd n, ERefused) ps
End

(* The connects, in order: the address and the result *)
Definition hl_connects_def:
  hl_connects ps =
    FLAT (MAP (λ(x, r). case x of EConnect p => [(p, r)] | _ => []) ps)
End

(* The handles connected (with a socket), in order *)
Definition hl_conn_handles_def:
  hl_conn_handles ps =
    FLAT (MAP (λ(p, r). case r of EConnected (SOME hd) => [hd] | _ => []) (hl_connects ps))
End

(* A connect handle has settled Up: reported ready while settling, and not
   refused *)
Definition hl_up_def:
  hl_up hd ps ⇔ MEM hd (hl_conn_handles ps) ∧ ¬hl_refused hd ps ∧
                (hl_sent hd ps ≠ [] ∨ hl_read hd ps ≠ [] ∨ hl_eof hd ps)
End

Definition inf_often_def:
  inf_often (P : num -> bool) ⇔ ∀n. ∃n'. n ≤ n' ∧ P n'
End

(* ------------------------------------------------------------------------
   The class of worlds, and the guarantee
   ------------------------------------------------------------------------ *)

(* A client world: as the run-built world pew is (pew_props), with the
   listener L1 needs on a private port c (question Q1 of the note) *)
Definition client_world_def:
  client_world lfd c (W : eworld) ⇔
    W.listening = [(lfd, c, [])] ∧ W.chans = [] ∧ W.open_fds = [] ∧ W.reserved = [] ∧
    no_backpressure W ∧ open_loop W ∧ alloc_ok W.alloc ∧ takes_ok W.takes
End

(* The run-local rely: every round's arrivals are valid (E1's eh_round_ok) *)
Definition run_rely_def:
  run_rely lfd ifds m W ⇔ ∀n. eh_round_ok lfd ifds m W n
End

(* World fairness for connects, the handle layer's form of [F4]: if the
   client attempts connects in infinitely many rounds, infinitely many of
   them settle Up *)
Definition conn_fair_def:
  conn_fair lfd ifds m W ⇔
    inf_often (λn. ∃p. MEM (EConnect p) (new_actions (log_of m) (ehhist lfd ifds m W n))) ⇒
    inf_often (λn. ∃hd. MEM hd (hl_conn_handles (hl_pairs m (ehhist lfd ifds m W n))) ∧
                        hl_up hd (hl_pairs m (ehhist lfd ifds m W n)) ∧
                        ¬hl_up hd (hl_pairs m (ehhist lfd ifds m W (n - 1))))
End

(* The guarantee, over the run H n = ehhist lfd ifds m W n (S n its state);
   lc: each handle's logical connection *)
Definition client_guar'_def:
  client_guar' a N rqs lfd ifds m W ⇔
    ∃lc. let H = ehhist lfd ifds m W; S = ehst lfd ifds m W; ps = (λn. hl_pairs m (H n)) in
      (* no misuse: every round's actions are performed *)
      (∀n. ehacts lfd (S n) (new_actions (log_of m) (H n)) ≠ NONE) ∧
      (* it connects only to a, and never accepts *)
      (∀n x r. MEM (x, r) (ps n) ⇒ (∀p. x = EConnect p ⇒ p = a) ∧ ∀l. x ≠ EAccept l) ∧
      (* each logical connection i < N sends a prefix of its requests, on
         at most one handle *)
      (∀n hd. hl_sent hd (ps n) ≠ [] ⇒
              lc hd < N ∧ hl_sent hd (ps n) ≼ brequests (rqs (lc hd)) ∧
              ∀hd'. hl_sent hd' (ps n) ≠ [] ∧ lc hd' = lc hd ⇒ hd' = hd) ∧
      (* the sink: every open handle is in the interest, and a ready one is
         read in the next round *)
      (∀n hd. MEM hd (MAP FST (SND (S n)).tbl) ⇒ MEM hd (ifds (H n))) ∧
      (∀n hd. hd ∈ (LAST (H (SUC n))).ready ∧ MEM hd (MAP FST (SND (S (SUC n))).tbl) ⇒
              ∃k. MEM (ERead hd k) (new_actions (log_of m) (H (SUC n)))) ∧
      (* it does not take a refusal for an empty answer *)
      (∀n hd. ¬(hl_refused hd (ps n) ∧ hl_eof hd (ps n))) ∧
      (* RETRY: while fewer than N connections are up, it keeps connecting
         (a connect with no socket, or refused, is followed by another) *)
      (∀n. CARD {hd | hl_up hd (ps n)} < N ⇒
           ∃n'. n ≤ n' ∧ ∃p. MEM (EConnect p) (new_actions (log_of m) (H n'))) ∧
      (* LIVENESS, under connect fairness: every logical connection gets up
         and sends all of its requests (the world takes every write: no
         backpressure) *)
      (conn_fair lfd ifds m W ⇒
       ∃n. ∀i. i < N ⇒ ∃hd. lc hd = i ∧ hl_sent hd (ps n) = brequests (rqs i)) ∧
      (* TERMINATION: once every up connection has read its EOF, the client
         finishes *)
      (∀n. (∀hd. hl_up hd (ps n) ⇒ hl_eof hd (ps n)) ∧ CARD {hd | hl_up hd (ps n)} = N ⇒
           ∃n' x. n ≤ n' ∧ (m (H n')).result = SOME x)
End

(* ------------------------------------------------------------------------
   The statements to prove (as claims; nothing is proved here)
   ------------------------------------------------------------------------ *)

(* The client, in every client world with the run-local rely.  cprog a N
   rqs and cifds are the client's computation and interest (to be defined:
   a pure step function, design/44) *)
Definition client_hl_claim_def:
  client_hl_claim cprog cifds ⇔
    ∀a N rqs lfd c W.
      2 ≤ N ∧ (∀i. EVERY valid_brequest (rqs i)) ∧
      client_world lfd c W ∧ run_rely lfd cifds (cprog a N rqs) W ⇒
      client_guar' a N rqs lfd cifds (cprog a N rqs) W
End

(* Through E1: along EVERY run of the honest L1 in an L0 world, running the
   client, the guarantee holds of L1's own history (the run-built world is
   a client world, with the run-local rely, by pew_props and
   l1ep_refines_ehl) *)
Definition client_l1_claim_def:
  client_l1_claim cprog cifds ⇔
    ∀a N rqs lfd c hw w0 calls.
      2 ≤ N ∧ (∀i. EVERY valid_brequest (rqs i)) ∧
      l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
      (∀n. SND (ecm lfd hw cifds (cprog a N rqs) w0 n) + 1 < dimword (:64)) ∧
      (* the client's L1 run never fails (no misuse, no handle overflow) *)
      (∀n. erounds lfd hw cifds (cprog a N rqs) (w0, einit) n ≠ NONE) ⇒
      client_guar' a N rqs lfd cifds (cprog a N rqs)
        (pew lfd c hw cifds (cprog a N rqs) w0 calls)
End
