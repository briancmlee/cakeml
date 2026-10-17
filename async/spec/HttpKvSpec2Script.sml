(*
  HttpKvSpec2: the HTTP key-value server in a world where connections are
  closed and fds are REUSED.  DRAFT, for the user's decision.  A companion
  of HttpKvSpec (unchanged); it is to HttpKvSpec what HttpSpecBodies2 is
  to HttpSpecBodies.

  TRUSTED SURFACE: this file, HttpKvSpec (the store, kv_run, replies,
  earlier, reply_bytes: reused unchanged), HttpSpecBodies (requests) and
  EchoSpec2 (the version-2 world, the per-EPISODE projections ep_read,
  ep_written, sent2_upto, and the closing clause echo_closes2).

  What changes from HttpKvSpec: connections are EPISODES (the j-th
  accepted connection, from its accept to its close), not fds.
   - Safety (kv_safe2): HttpKvSpec's linearizability, with episodes for
     connections.  At every point there is one order of all the complete
     requests read so far, in all episodes, that keeps each episode's
     requests in its order, respects real time, and whose replies extend
     what each episode was written.  So an answer can never reach a later
     connection that reuses the fd, and two episodes on the same fd are
     two concurrent clients, not one.
   - Liveness (kv_live2): per client j (= episode j), as HttpKvSpec's.
   - Closing (echo_closes2): once the server has read the EOF of an
     episode's client, it eventually closes the episode's fd.
  The store is shared across all episodes, as across all connections in
  HttpKvSpec, and lives for the whole run.

  APPROVED by the user (2026-10-16, PR #117), as drafted: episodes on a
  reused fd are distinct concurrent clients, ordered by real time when it
  applies; the server closes only after the client's EOF.

  Nothing here is proved; kv_spec2 is a definition.
  HttpKvSpec2BiteScript.sml shows that it rules out the reuse leak, which
  HttpKvSpec's per-fd kv_safe misses, and a server that never closes, and
  that it is satisfiable (non-vacuity).
*)
Theory HttpKvSpec2
Ancestors
  EchoSpec HttpSpec HttpSpecBodies HttpKvSpec EchoSpec2 rich_list
Libs
  preamble

(* rss j: the complete requests read in episode j so far.  (j, i) names
   the i-th of them.  An order lists each exactly once, each episode's in
   their own order (HttpKvSpec's is_order, with episodes for fds). *)
Definition is_order2_def:
  is_order2 (rss : num -> brequest list) (order : (num # num) list) ⇔
    ∀j. MAP SND (FILTER (λx. FST x = j) order) = COUNT_LIST (LENGTH (rss j))
End

(* Real time: at some point evs1 of the trace evs, the server had written,
   in episode j, the whole response to (j, i), and had read in episode k
   no byte of (k, l) *)
Definition precedes2_def:
  precedes2 rss order evs (j, i) (k, l) ⇔
    ∃evs1. evs1 ≼ evs ∧
           reply_bytes (TAKE (SUC i) (replies rss order j)) ≼ ep_written j evs1 ∧
           ep_read k evs1 ≼ brequests (TAKE l (rss k))
End

(* Safety: HttpKvSpec's kv_safe, per episode *)
Definition kv_safe2_def:
  kv_safe2 io ⇔
    ∀evs rss rests.
      LPREFIX (fromList evs) io ∧
      (∀j. EVERY valid_brequest (rss j) ∧ no_full_brequest (rests j) ∧
           ep_read j evs = brequests (rss j) ++ rests j) ⇒
      ∃order.
        is_order2 rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedes2 rss order evs x y ⇒ earlier order x y) ∧
        ∀j. ep_written j evs ≼ reply_bytes (replies rss order j)
End

(* Liveness: if client j has sent the requests rs (within the first n
   steps of the schedule), the server eventually writes as many whole
   responses in episode j *)
Definition kv_live2_def:
  kv_live2 sk io ⇔
    ∀j n rs.
      EVERY valid_brequest rs ∧ brequests rs ≼ sent2_upto j n sk ⇒
      ∃evs ans. LPREFIX (fromList evs) io ∧ LENGTH ans = LENGTH rs ∧
               reply_bytes ans ≼ ep_written j evs
End

(* THE STATEMENT: in every fair version-2 world with one listener lfd, the
   program runs forever, its I/O trace is linearizable and live per
   episode, and it closes every episode whose client has closed. *)
Definition kv_spec2_def:
  kv_spec2 lfd (prog : dec list) ⇔
    ∀sk. server_world2 lfd sk ⇒
         ∃io. semantics_prog (init_state (socket2_ffi sk)) init_env prog
                (Diverge io) ∧
              kv_safe2 io ∧ kv_live2 sk io ∧ echo_closes2 io
End
