(*
  Moonshot step 12, C1: the CLIENT's guarantee on its RAW L0 trace, as a
  STATEMENT for review (DRAFT).  Nothing here is proved.

  Same shape as the proxy's l0_proxy_claim (step 9): for every world of the
  class, the binary has a behaviour that is not Fail, and either its first
  listen failed or its trace satisfies the safety property.  Unlike the
  proxy, the episodes are named in l0sysEpisodes' vocabulary (l0_ep_sent,
  l0_ep_role, by episode number), the one moonshot_view_safe uses, so no
  position ↔ number bridge is needed for the client.

  THE WORLD CLASS is B1's (l0sys_proj): l0_rely ∧ l0_fresh ∧ fds_lt.  So the
  client's claim plugs into B1/G2 directly, whatever G3 decides for the
  servers.

  THE LISTENER.  The client runs on L1, which needs a listener (lfd, until
  L1/E1's listener is optional): the binary first listens on a private port
  c, then runs L1.  So the client CAN accept (on c), and T3 is stated as
  "every successful listen is on c, and nothing is sent on an accepted
  episode".  moonshotPairGlue.topology must then allow the client's
  Accepted c episodes with c ∉ {pa, pb}: such an episode has no partner in
  conn (a partner would be Connected c, which topology rules out), so
  b2_conn makes it read nothing (to do, a small change to topology).

  The safety content, per prefix of the trace (lc: each episode's logical
  connection, fixed for the whole trace, like the proxy's pr):
   - [T3] every successful sys_listen is on c;
   - [T4] every sys_connect is to a;
   - nothing is sent on an accepted episode;
   - each connect episode serves a logical connection lc j < N and sends a
     prefix of its requests brequests (rqs (lc j));
   - at most one episode sends anything per logical connection (a refused
     or broken connection's retry sends nothing on the old one; design/45
     §2.5, client_guar' at the handle layer).
  Liveness and termination are left out (the client's liveness is not in
  moonshot_safe).

  [D] l0_listen_failed: the proxy's listen_failed (honestL1BStmts, on
  spike/echo-live-pol), reworded for this branch; to merge with it.
*)
Theory moonshotClientL0Stmts
Ancestors
  l0sysBridges l0sysInv l0sysEpisodes proxyL0StmtsCopy honestEchoL0SpecCopy
  HttpSpecBodies
Libs
  preamble

(* The first call, a listen, failed, and the program stopped *)
Definition l0_listen_failed_def:
  l0_listen_failed b ⇔
    ∃conf bs. b = Terminate Success [IO_event (ExtCall «sys_listen») conf bs] ∧
              ∀k. l0_ev_res bs ≠ SOME (Ok k)
End

(* Safety, at every prefix (no fairness) *)
Definition client_safe_l0_def:
  client_safe_l0 a c (N : num) rqs (lc : num -> num) io ⇔
    ∀evs. LPREFIX (fromList evs) io ⇒
      (* [T3] its only listener is its private port c *)
      (∀conf bs k. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ∧
                   l0_ev_res bs = SOME (Ok k) ⇒ conf = pbytes c) ∧
      (* [T4] it connects only to a *)
      (∀conf bs. MEM (IO_event (ExtCall «sys_connect») conf bs) evs ⇒ conf = pbytes a) ∧
      (* it sends nothing on an accepted episode *)
      (∀j p. l0_ep_role j evs = SOME (Accepted p) ⇒ l0_ep_sent j evs = []) ∧
      (* a connect episode serves logical connection lc j, and sends a
         prefix of that connection's requests *)
      (∀j p. l0_ep_role j evs = SOME (Connected p) ⇒
             lc j < N ∧ l0_ep_sent j evs ≼ brequests (rqs (lc j))) ∧
      (* at most one sending episode per logical connection *)
      (∀j j'. l0_ep_sent j evs ≠ [] ∧ l0_ep_sent j' evs ≠ [] ∧ lc j = lc j' ⇒ j = j')
End

(* The claim, for the client binary cprog a c N rqs: in every world of B1's
   class, a behaviour that is not Fail, and safe unless the listen failed *)
Definition l0_client_claim_def:
  l0_client_claim cprog ⇔
    ∀a c N rqs w0.
      2 ≤ N ∧ (∀i. EVERY valid_brequest (rqs i)) ∧
      a < 65536 ∧ c < 65536 ∧ c ≠ a ∧
      l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
      ∃beh. semantics_prog (init_state (l0_ffi w0)) init_env (cprog a c N rqs) beh ∧
            beh ≠ Fail ∧
            (l0_listen_failed beh ∨ ∃lc. client_safe_l0 a c N rqs lc (beh_io beh))
End
