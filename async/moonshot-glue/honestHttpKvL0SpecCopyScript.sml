(*
  TEMPORARY VERBATIM COPY (remove at merge): the KV safety and topology
  definitions of honestHttpKvL0Spec (P4 draft), from spike/servers-honest-l1,
  async/honest-echo/honestHttpKvL0SpecScript.sml @ a1f3e4403, so that
  moonshotKvBridge can state the bridge on this branch.  Copied unchanged;
  the claims (kv_l0_claim, which changes with D33) are left out until their
  final form lands.  At the merge, delete this file and make moonshotKvBridge's
  ancestor honestHttpKvL0Spec: the proofs only unfold these definitions.
*)
Theory honestHttpKvL0SpecCopy
Ancestors
  llist ffi honestL0 honestL0World honestEchoL0SpecCopy HttpSpecBodies HttpKvSpec rich_list
Libs
  preamble

Definition is_order_l0_def:
  is_order_l0 (rss : num -> brequest list) (order : (num # num) list) ⇔
    ∀j. MAP SND (FILTER (λx. FST x = j) order) = COUNT_LIST (LENGTH (rss j))
End

Definition precedes_l0_def:
  precedes_l0 rss order evs (j, i) (k, l) ⇔
    ∃evs1. evs1 ≼ evs ∧
           reply_bytes (TAKE (SUC i) (replies rss order j)) ≼ l0_sent j evs1 ∧
           l0_read k evs1 ≼ brequests (TAKE l (rss k))
End

Definition kv_safe_l0_def:
  kv_safe_l0 io ⇔
    ∀evs rss rests.
      LPREFIX (fromList evs) io ∧
      (∀j. EVERY valid_brequest (rss j) ∧ no_full_brequest (rests j) ∧
           l0_read j evs = brequests (rss j) ++ rests j) ⇒
      ∃order.
        is_order_l0 rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedes_l0 rss order evs x y ⇒ earlier order x y) ∧
        ∀j. l0_sent j evs ≼ reply_bytes (replies rss order j)
End

Definition l0_topo_ev_def:
  l0_topo_ev port (IO_event (ExtCall n) conf bytes) =
    ((n = «sys_listen» ∧ (∃k. l0_ev_res bytes = SOME (Ok k)) ⇒ w22n conf = port) ∧
     n ≠ «sys_connect») ∧
  l0_topo_ev port _ = T
End

Definition l0_topology_def:
  l0_topology port io ⇔ ∀n ev. LNTH n io = SOME ev ⇒ l0_topo_ev port ev
End

