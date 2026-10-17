(*
  Moonshot step 12: the TRUSTED definitions and the headline, as
  STATEMENTS for the user's review (DRAFT).  Nothing here is proved.

  1. moonshot_sys: the system.  Three programs, launched as processes 0, 1
     and 2 of an l0sys run, each by sys_init with a fresh L0 state (D33: no
     fd reserved; each program checks its stdio itself).  l0sys has no
     launch arguments, so the ports are the programs' own parameters:
       - the client cprog a c N rqs connects to a, and listens on its
         private port c (L1's listener);
       - the proxy pprog a b listens on a and connects to b;
       - KV kprog b listens on b.

  2. isolated a b: no OUTSIDE peer on the system's ports a and b
     (design/45 §4.1's form; user ruling 2026-10-17, the middle option).
     Over the run's labels and states:
       - no outside process connects to a listener on a or b (no Env
         (EIncoming k p) with p ∈ {a, b});
       - no connect to a or b completes with, or gets bytes from, an
         outside process (no Env (EConnUp k j) or Env (EArrive …) on an end
         whose target is a or b);
       - every connect to a or b that the L0 state says connected at once
         was paired with a listener of the system.
     Outside traffic on any other port, e.g. the client's private port c,
     is allowed.  It is also irrelevant: the headline speaks only of the
     client's CONNECT episodes, its connections to the proxy (conn_only).
     isolated reads the run's states ss, so the headline uses
     l0sys_iso_run: l0sys_run with the same s0 and ss, plus isolated.

  3. b2_iso_stmt (for m4-server, B2's isolated variant): in an isolated
     run, B2's pairing also has b2_quiet_ab: an episode on a or b (its role
     is Connected or Accepted on a or b) that conn leaves unpaired reads
     nothing.  An unpaired end gets bytes only from an outside peer (Env
     EArrive) or from a peer in the system (Move).  On a and b, isolated
     rules out the outside peer, and an end with a system peer is paired.

  4. topology_stmt: moonshot_sys plus the three claims' port clauses
     (listens_only / connects_only / no_connects on each process's whole
     trace) gives moonshotPairGlue.topology.  This uses m4-server's
     accepts_known (W4), since an accept's port is its listener's.

  5. The per-process claims, in the form step 12 consumes:
       - the client: moonshotClientL0Stmts.l0_client_claim (approved);
       - the proxy: proxy_claim_safe, the safety half of step 9's
         l0_proxy_claim (rev 6), over B1's world class (D33), plus
         no_close_stdio (for W2, with D33's fdok check: NEW, the proxy's
         statement must add it);
       - KV: kv_claim_safe, what step 11 must deliver (kv_safe_g at
         l0_ep_recvd / l0_ep_sent, plus T7/T8).
     Each allows the early outcomes stdio_closed (honestL0Outcome, D33)
     and l0_listen_failed.

  6. moonshot_safe_stmt: THE HEADLINE (design/45 §4.1), exactly as it will
     be proved.  In every run with no outsider on a or b, the client's
     view of its connections to the proxy is linearizable against KV.
*)
Theory moonshotStep12Stmts
Ancestors
  moonshotSysGlue moonshotClientL0Stmts moonshotPairGlue proxyL0StmtsCopy
  moonshotKvClient l0sysBridges l0sys l0sysEpisodes honestEchoL0SpecCopy
Libs
  preamble

(* ------------------------------------------------------------------------
   1. The system
   ------------------------------------------------------------------------ *)

Definition moonshot_sys_def:
  moonshot_sys cprog pprog kprog (a : num) (b : num) (c : num) (N : num)
               (rqs : num -> brequest list) =
    [cprog a c N rqs; pprog a b; kprog b] : dec list list
End

(* The processes' indices *)
Definition client_ix_def:
  client_ix = (0 : num)
End

Definition proxy_ix_def:
  proxy_ix = (1 : num)
End

Definition kv_ix_def:
  kv_ix = (2 : num)
End

(* ------------------------------------------------------------------------
   2. isolated
   ------------------------------------------------------------------------ *)

(* An end's target is a or b *)
Definition on_ab_def:
  on_ab (a : num) (b : num) (s : sysstate) e ⇔ s.target e = SOME a ∨ s.target e = SOME b
End

(* No outside peer on the ports a and b; at-once connects to them are paired *)
Definition isolated_def:
  isolated a b (rs : syslabel list) (ss : sysstate list) ⇔
    ∀i. i < LENGTH rs ⇒
      (∀k p. EL i rs = Env (EIncoming k p) ⇒ p ≠ a ∧ p ≠ b) ∧
      (∀k j. EL i rs = Env (EConnUp k j) ⇒ ¬on_ab a b (EL i ss) (k, j)) ∧
      (∀k x j. EL i rs = Env (EArrive k x) ∧ env_arrival_chan x = SOME j ⇒
               ¬on_ab a b (EL i ss) (k, j)) ∧
      ∀k conf bytes out.
        EL i rs = Call k «sys_connect» conf bytes out ∧ (w22n conf = a ∨ w22n conf = b) ∧
        LENGTH (EL k (EL (SUC i) ss).procs).chans = LENGTH (EL k (EL i ss).procs).chans + 1 ∧
        ¬(sys_chan (EL (SUC i) ss) (k, LENGTH (EL k (EL i ss).procs).chans)).connecting ∧
        ¬(sys_chan (EL (SUC i) ss) (k, LENGTH (EL k (EL i ss).procs).chans)).broken ⇒
        (EL (SUC i) ss).peer (k, LENGTH (EL k (EL i ss).procs).chans) ≠ NONE
End

(* An l0sys run that is isolated, along its own states *)
Definition l0sys_iso_run_def:
  l0sys_iso_run (S : dec list list) a b rs ⇔
    ∃s0 ss. sys_init S s0 ∧ sys_steps s0 rs ss ∧
            (∀k. k < LENGTH S ⇒ prog_makes (EL k S) (proc_events k rs)) ∧
            isolated a b rs ss
End

(* ------------------------------------------------------------------------
   3. B2, isolated (for m4-server)
   ------------------------------------------------------------------------ *)

(* An episode on a or b that cn leaves unpaired reads nothing *)
Definition b2_quiet_ab_def:
  b2_quiet_ab a b rs cn ⇔
    ∀k j t r. cn (k, j) = NONE ∧ l0_ep_role j (proc_events k rs) = SOME r ∧
              MEM r [Connected a; Connected b; Accepted a; Accepted b] ⇒
              l0_ep_recvd j (proc_events k (TAKE t rs)) = []
End

Definition b2_iso_stmt_def:
  b2_iso_stmt ⇔
    ∀S a b rs. l0sys_iso_run S a b rs ⇒
      ∃cn. (∀e e'. cn e = SOME e' ⇔ cn e' = SOME e) ∧
           (∀k j k' j'. cn (k, j) = SOME (k', j') ⇒
              k < LENGTH S ∧ k' < LENGTH S ∧
              (∃p. l0_ep_role j (proc_events k rs) = SOME (Connected p) ∧
                   l0_ep_role j' (proc_events k' rs) = SOME (Accepted p) ∨
                   l0_ep_role j (proc_events k rs) = SOME (Accepted p) ∧
                   l0_ep_role j' (proc_events k' rs) = SOME (Connected p)) ∧
              ∀t. l0_ep_recvd j' (proc_events k' (TAKE t rs)) ≼
                  l0_ep_sent j (proc_events k (TAKE t rs))) ∧
           b2_quiet_ab a b rs cn
End

(* ------------------------------------------------------------------------
   4. The ports, and topology
   ------------------------------------------------------------------------ *)

Definition listens_only_def:
  listens_only p evs ⇔
    ∀conf bs k. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ∧
                l0_ev_res bs = SOME (Ok k) ⇒ conf = pbytes p
End

(* Every connect that opened an episode was to port p (at the episodes'
   level: a connect that got no socket opens none) *)
Definition connects_only_def:
  connects_only p evs ⇔ ∀ev f q. MEM ev evs ∧ ev_new ev = SOME (f, INL q) ⇒ q = p
End

Definition no_connects_def:
  no_connects evs ⇔ ∀conf bs. ¬MEM (IO_event (ExtCall «sys_connect») conf bs) evs
End

Definition topology_stmt_def:
  topology_stmt ⇔
    ∀cprog pprog kprog a b c N rqs rs.
      l0sys_run (moonshot_sys cprog pprog kprog a b c N rqs) rs ∧
      a < 65536 ∧ b < 65536 ∧ c < 65536 ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧
      listens_only c (proc_events client_ix rs) ∧ connects_only a (proc_events client_ix rs) ∧
      listens_only a (proc_events proxy_ix rs) ∧ connects_only b (proc_events proxy_ix rs) ∧
      listens_only b (proc_events kv_ix rs) ∧ no_connects (proc_events kv_ix rs) ⇒
      topology (sys_rl rs) client_ix proxy_ix kv_ix a b
End

(* ------------------------------------------------------------------------
   5. The proxy's and KV's claims, as step 12 consumes them
   ------------------------------------------------------------------------ *)

(* The safety half of step 9's l0_proxy_claim (rev 6), over B1's world class
   (D33) *)
Definition proxy_claim_safe_def:
  proxy_claim_safe Bnd pprog ⇔
    ∀a b w0. a < 65536 ∧ b < 65536 ∧ a ≠ b ∧ l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
      ∃beh. semantics_prog (init_state (l0_ffi w0)) init_env (pprog a b) beh ∧ beh ≠ Fail ∧
            (stdio_closed beh ∨ l0_listen_failed beh ∨
             (∃pr. proxy_safe_l0 Bnd a b pr (beh_io beh)) ∧
             ∀evs. LPREFIX (fromList evs) (beh_io beh) ⇒ no_close_stdio evs)
End

(* What step 11 must deliver: KV's linearizability on its raw trace, in
   l0sysEpisodes' vocabulary, plus its ports (T7, T8) *)
Definition kv_claim_safe_def:
  kv_claim_safe kprog ⇔
    ∀b w0. b < 65536 ∧ l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
      ∃beh. semantics_prog (init_state (l0_ffi w0)) init_env (kprog b) beh ∧ beh ≠ Fail ∧
            (stdio_closed beh ∨ l0_listen_failed beh ∨
             kv_safe_g l0_ep_recvd l0_ep_sent (beh_io beh) ∧
             ∀evs. LPREFIX (fromList evs) (beh_io beh) ⇒ listens_only b evs ∧ no_connects evs)
End

(* ------------------------------------------------------------------------
   6. THE HEADLINE
   ------------------------------------------------------------------------ *)

(* The client's view of episode j: only if j is a connect episode (its
   connections to the proxy; any other episode shows nothing) *)
Definition conn_only_def:
  conn_only sel j evs = if (∃p. l0_ep_role j evs = SOME (Connected p)) then sel j evs else []
End

(* In every run with no outsider on a or b, the client observes one
   sequential store: its view of its connections to the proxy is
   linearizable against KV *)
Definition moonshot_safe_stmt_def:
  moonshot_safe_stmt Bnd cprog pprog kprog ⇔
    l0_client_claim cprog ∧ proxy_claim_safe Bnd pprog ∧ kv_claim_safe kprog ⇒
    ∀a b c N rqs rs.
      a < 65536 ∧ b < 65536 ∧ c < 65536 ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧
      2 ≤ N ∧ (∀i. EVERY valid_brequest (rqs i)) ∧
      l0sys_iso_run (moonshot_sys cprog pprog kprog a b c N rqs) a b rs ⇒
      kv_client_safe (conn_only l0_ep_sent) (conn_only l0_ep_recvd)
                     (fromList (proc_events client_ix rs))
End
