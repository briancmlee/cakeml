(*
  Moonshot liveness, N8 part 1 (README §2): the rank chain of one logical
  connection, at l0sys level.

  The connection's ends: the client's (cl, jc), paired by the kernel with
  the proxy's front (px, ja); the proxy's backend (px, jb), paired with
  KV's (kv, jk).  Each program's "asks infinitely often" clause (README
  N4, owed by the programs' claims) is an explicit hypothesis here, each
  conditional on the drain of the end its asking waits on, and each with
  the run's excuse X as a way out:
   - the client asks on jc (unconditionally: the sink);
   - the proxy asks on its backend jb once its front ja drains (the gate
     on the front's Level);
   - KV asks on jk once jk drains (pol_self: its own outbox);
   - the proxy asks on its front ja once its backend jb drains (the gate
     on the backend's Level).
  Then, unless X, all four directions drain (sys_drains): once an end
  stops sending, all it sent is moved and acknowledged, for good.  The
  order of the proof is the rank order d0, d1, d2, d3 (P→C, K→P, P→K,
  C→P), each step drains_of_asks (N5).
*)
Theory moonshotLiveChain
Ancestors
  moonshotLiveDrains moonshotLiveStmts l0sysFair l0sys l0sysCausal
Libs
  preamble

(* End e drains: from any instant at which it has stopped sending, all
   it sent is eventually moved and acknowledged for good (the system form
   of each process's `drains`, honestL1BStmts) *)
Definition sys_drains_def:
  sys_drains (ss : num -> sysstate) e ⇔
    ∀n0. (∀n. n0 ≤ n ⇒ LENGTH (sys_chan (ss n) e).sent = LENGTH (sys_chan (ss n0) e).sent) ⇒
         ∃n2. n0 ≤ n2 ∧ ∀n. n2 ≤ n ⇒
              (ss n).moved e = LENGTH (sys_chan (ss n0) e).sent ∧
              (ss n).acked e = LENGTH (sys_chan (ss n0) e).sent
End

(* N5 as sys_drains: an end with a peer whose receiver asks infinitely
   often drains *)
Theorem sys_drains_of_asks:
  l0sys_irun ps ss rs ∧ kernel_fair_obs ss rs ∧
  (ss m).peer e = SOME (k', j') ∧ io (asks_in ss rs k' j') ⇒
  sys_drains ss e
Proof
  rw[sys_drains_def] >>
  ‘(ss (m + n0)).peer e = SOME (k', j')’ by
    (drule irun_mono >> disch_then (qspec_then ‘e’ mp_tac) >>
     disch_then (qspecl_then [‘m’, ‘m + n0’] mp_tac) >> simp[]) >>
  ‘∀n. m + n0 ≤ n ⇒ LENGTH (sys_chan (ss n) e).sent = LENGTH (sys_chan (ss n0) e).sent’ by
    simp[] >>
  qspecl_then [‘ps’, ‘ss’, ‘rs’, ‘m + n0’, ‘e’, ‘k'’, ‘j'’, ‘LENGTH (sys_chan (ss n0) e).sent’]
    mp_tac (Q.GENL [‘ps’, ‘ss’, ‘rs’, ‘n0’, ‘e’, ‘k'’, ‘j'’, ‘L’] drains_of_asks) >>
  impl_tac
  >- (simp[] >> fs[io_def, io_from_def] >> metis_tac[]) >>
  strip_tac >> qexists_tac ‘n2’ >> simp[]
QED

(* The chain of one logical connection *)
Theorem moonshot_chain_drains:
  l0sys_irun ps ss rs ∧ kernel_fair_obs ss rs ∧
  (* the kernel pairs the client with the front, the backend with KV *)
  (ss m).peer (cl, jc) = SOME (px, ja) ∧ (ss m).peer (px, jb) = SOME (kv, jk) ∧
  (* the programs' asks clauses (N4), each unless X *)
  (X ∨ io (asks_in ss rs cl jc)) ∧
  (sys_drains ss (px, ja) ⇒ X ∨ io (asks_in ss rs px jb)) ∧
  (sys_drains ss (kv, jk) ⇒ X ∨ io (asks_in ss rs kv jk)) ∧
  (sys_drains ss (px, jb) ⇒ X ∨ io (asks_in ss rs px ja)) ⇒
  X ∨ (sys_drains ss (px, ja) ∧ sys_drains ss (kv, jk) ∧
       sys_drains ss (px, jb) ∧ sys_drains ss (cl, jc))
Proof
  strip_tac >> Cases_on ‘X’ >> fs[] >>
  ‘kinv (ss m)’ by metis_tac[irun_kinv] >>
  ‘(ss m).peer (px, ja) = SOME (cl, jc) ∧ (ss m).peer (kv, jk) = SOME (px, jb)’ by
    fs[kinv_def] >>
  (* d0: P→C, the client is the sink *)
  ‘sys_drains ss (px, ja)’ by metis_tac[sys_drains_of_asks] >>
  (* d1: K→P, the proxy reads its backend once the front drains *)
  ‘sys_drains ss (kv, jk)’ by metis_tac[sys_drains_of_asks] >>
  (* d2: P→K, KV reads once its own outbox drains *)
  ‘sys_drains ss (px, jb)’ by metis_tac[sys_drains_of_asks] >>
  (* d3: C→P, the proxy reads its front once the backend drains *)
  metis_tac[sys_drains_of_asks]
QED

(* ========================================================================
   N8 part 2 (STATEMENTS ONLY, for review): the data chain
   ======================================================================== *)

(* What end e's sends accepted by instant n, and what arrived at e from its
   peer by instant n (the kernel's byte streams) *)
Definition sent_at_def:
  sent_at (ss : num -> sysstate) e n = (sys_chan (ss n) e).sent
End

Definition dlv_at_def:
  dlv_at (ss : num -> sysstate) e n = (sys_chan (ss n) e).peer_sent
End

(* Everything f had at any instant, g has at some later instant *)
Definition ev_ext_def:
  ev_ext (f : num -> 'a list) (g : num -> 'a list) ⇔ ∀n. ∃n'. n ≤ n' ∧ f n ≼ g n'
End

(* As ev_ext, unless B holds by then *)
Definition ev_ext_unless_def:
  ev_ext_unless (B : num -> bool) (f : num -> 'a list) (g : num -> 'a list) ⇔
    ∀n. ∃n'. n ≤ n' ∧ (f n ≼ g n' ∨ B n')
End

(* End e has lost its stream at instant n: broken, or closed by its
   process (a FIN read is no loss: Fin follows all moved data) *)
Definition lost_def:
  lost (ss : num -> sysstate) e n ⇔ (sys_chan (ss n) e).broken ∨ (sys_chan (ss n) e).closed
End

(* N5b, the kernel's part (TO PROVE, from kernel_fair_obs (D) and kinv,
   with kinv's frozen case refined to peer_eof-after-Fin): if the receiver
   (k', j') of e keeps asking, everything e sent arrives, unless the
   receiving end is lost by then *)
Definition sys_delivers_claim_def:
  sys_delivers_claim ⇔
    ∀ps ss rs m e k' j'.
      l0sys_irun ps ss rs ∧ kernel_fair_obs ss rs ∧
      (ss m).peer e = SOME (k', j') ∧ io (asks_in ss rs k' j') ⇒
      ev_ext_unless (lost ss (k', j')) (sent_at ss e) (dlv_at ss (k', j'))
End

(* KV answers every complete request that has arrived (count only: which
   replies is kv_safe's) *)
Definition kv_answers_def:
  kv_answers X (ss : num -> sysstate) e ⇔
    ∀n rqs. EVERY valid_brequest rqs ∧ brequests rqs ≼ dlv_at ss e n ⇒
            X ∨ ∃n' ans. LENGTH ans = LENGTH rqs ∧ reply_bytes ans ≼ sent_at ss e n'
End

(* The client has read complete replies to rq on its episode jep by n *)
Definition served_by_def:
  served_by rs cl jep (rq : brequest list) n ⇔
    ∃ans. LENGTH ans = LENGTH rq ∧ reply_bytes ans ≼ l0_ep_recvd jep (ptr rs cl n)
End

(* The data chain of one logical connection (TO PROVE, pure glue: prefix
   transitivity along client → kernel → proxy → kernel → KV and back,
   from N5b and moonshot_chain_drains).  The programs' liveness clauses,
   at system level, each unless X, each conditional on the drain it needs:
    - the client sends all of rq on jc (needs jc to drain);
    - the proxy forwards what arrived on its front ja to its backend jb
      (needs jb to drain), and what arrived on jb to ja (needs ja);
    - KV answers what arrived on jk (needs jk to drain);
    - the client reads (recv) whatever arrived on jc, as its episode jep;
    - an end of the chain lost before the client is served is X: a break
      is sys_excuse's; a close before then is excluded by the programs'
      close clauses ([R3]: each closes only after the EOF it relays) *)
Definition chain_served_claim_def:
  chain_served_claim ⇔
    ∀ps ss rs m X cl jc px ja jb kv jk jep rq.
      l0sys_irun ps ss rs ∧ kernel_fair_obs ss rs ∧
      (ss m).peer (cl, jc) = SOME (px, ja) ∧ (ss m).peer (px, jb) = SOME (kv, jk) ∧
      EVERY valid_brequest rq ∧
      (* asks (N4), as moonshot_chain_drains *)
      (X ∨ io (asks_in ss rs cl jc)) ∧
      (sys_drains ss (px, ja) ⇒ X ∨ io (asks_in ss rs px jb)) ∧
      (sys_drains ss (kv, jk) ⇒ X ∨ io (asks_in ss rs kv jk)) ∧
      (sys_drains ss (px, jb) ⇒ X ∨ io (asks_in ss rs px ja)) ∧
      (* the programs' liveness (N6, N7, proxy_live_l0), at system level *)
      (sys_drains ss (cl, jc) ⇒ X ∨ ∃n. brequests rq ≼ sent_at ss (cl, jc) n) ∧
      (sys_drains ss (px, jb) ⇒ X ∨ ev_ext (dlv_at ss (px, ja)) (sent_at ss (px, jb))) ∧
      (sys_drains ss (kv, jk) ⇒ kv_answers X ss (kv, jk)) ∧
      (sys_drains ss (px, ja) ⇒ X ∨ ev_ext (dlv_at ss (px, jb)) (sent_at ss (px, ja))) ∧
      (X ∨ ev_ext (dlv_at ss (cl, jc)) (λn. l0_ep_recvd jep (ptr rs cl n))) ∧
      (* a chain end lost before the client is served *)
      (∀n e. MEM e [(cl, jc); (px, ja); (px, jb); (kv, jk)] ∧ lost ss e n ∧
             ¬served_by rs cl jep rq n ⇒ X) ⇒
      X ∨ ∃n. served_by rs cl jep rq n
End
