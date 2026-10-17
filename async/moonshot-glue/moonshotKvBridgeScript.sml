(*
  Step 12, KV's side (glue): KV's P4 claim on its raw trace (kv_l0_claim,
  honestHttpKvL0Spec's episodes l0_read / l0_sent) gives what step 12
  consumes (kv_claim_safe: kv_safe_g at l0sysEpisodes' l0_ep_recvd /
  l0_ep_sent, listens_only, no_connects).

  - kv_safe_l0 is kv_safe_g at l0_read / l0_sent (kv_safe_l0_g), and
    kv_safe_g depends only on the projections at the trace's prefixes
    (kv_safe_g_cong);
  - at every prefix of a lone KV run the two vocabularies agree
    (l0sysEpisodesEcho.l0_ep_echo), given: no connect (KV's topology),
    ops_live (lone_ops_live) and no episode on fd 0 (lone_no_fd0: D33's
    stdio check, and no close of fd 0);
  - the port: a listen that succeeded had a 2-byte conf (lone_listen_conf),
    so w22n conf = b is conf = pbytes b.
*)
Theory moonshotKvBridge
Ancestors
  moonshotStep12Stmts honestHttpKvL0SpecCopy moonshotLoneTrace moonshotW2 moonshotWorldFacts
  l0sysEpisodesEcho moonshotKvClient HttpKvSpec2 l0sysEpisodes l0sysInv l0sysInvCall
  honestL0World honestL0WorldProps honestEchoL0SpecCopy l0sysBridges proxyL0StmtsCopy
  llist rich_list
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The safety statements *)

Theorem kv_safe_l0_g:
  kv_safe_l0 io ⇔ kv_safe_g l0_read l0_sent io
Proof
  ‘is_order_l0 = is_order2’ by simp[FUN_EQ_THM, is_order_l0_def, is_order2_def] >>
  ‘precedes_l0 = precedes_g l0_read l0_sent’
    by simp[FUN_EQ_THM, FORALL_PROD, precedes_l0_def, precedes_g_def] >>
  simp[kv_safe_l0_def, kv_safe_g_def]
QED

Theorem LPREFIX_prefix:
  LPREFIX (fromList evs) io ∧ evs1 ≼ evs ⇒ LPREFIX (fromList evs1) io
Proof
  strip_tac >> irule LPREFIX_TRANS >> qexists_tac ‘fromList evs’ >>
  simp[LPREFIX_fromList, from_toList]
QED

Theorem kv_safe_g_cong_imp[local]:
  (∀evs j. LPREFIX (fromList evs) io ⇒ rd j evs = rd' j evs ∧ wr j evs = wr' j evs) ∧
  kv_safe_g rd wr io ⇒ kv_safe_g rd' wr' io
Proof
  rw[kv_safe_g_def] >>
  ‘∀rss order. precedes_g rd' wr' rss order evs = precedes_g rd wr rss order evs’
    by (rw[FUN_EQ_THM, FORALL_PROD, precedes_g_def] >> eq_tac >> rw[] >>
        qexists_tac ‘evs1’ >> ‘LPREFIX (fromList evs1) io’ by metis_tac[LPREFIX_prefix] >>
        metis_tac[]) >>
  first_x_assum (qspecl_then [‘evs’, ‘rss’, ‘rests’] mp_tac) >> impl_tac >- metis_tac[] >>
  strip_tac >> qexists_tac ‘order’ >> metis_tac[]
QED

Theorem kv_safe_g_cong:
  (∀evs j. LPREFIX (fromList evs) io ⇒ rd j evs = rd' j evs ∧ wr j evs = wr' j evs) ⇒
  (kv_safe_g rd wr io ⇔ kv_safe_g rd' wr' io)
Proof
  metis_tac[kv_safe_g_cong_imp]
QED

(*---------------------------------------------------------------------------*)
(* The two vocabularies agree at a prefix *)

Theorem MEM_l0_accepted:
  MEM f (l0_accepted evs) ⇒ ∃ev. MEM ev evs ∧ l0_event_accepted ev = SOME f
Proof
  rw[l0_accepted_def, MEM_FLAT, MEM_MAP] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem kv_eps_agree:
  EVERY no_connect evs ∧ ops_live evs ∧ EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs ⇒
  l0_ep_recvd j evs = l0_read j evs ∧ l0_ep_sent j evs = l0_sent j evs
Proof
  strip_tac >> irule l0_ep_echo >> simp[] >> strip_tac >>
  ‘MEM (EL j (l0_accepted evs)) (l0_accepted evs)’ by simp[EL_MEM] >>
  drule MEM_l0_accepted >> strip_tac >> fs[EVERY_MEM] >>
  ‘OPTION_MAP FST (ev_new ev) = l0_event_accepted ev’ by metis_tac[no_connect_ev_new] >>
  Cases_on ‘ev_new ev’ >> gvs[] >> rename1 ‘ev_new ev = SOME x’ >> PairCases_on ‘x’ >>
  gvs[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem kv_safe_bridge:
  (∀evs. LPREFIX (fromList evs) io ⇒
         EVERY no_connect evs ∧ ops_live evs ∧ EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs) ∧
  kv_safe_l0 io ⇒ kv_safe_g l0_ep_recvd l0_ep_sent io
Proof
  rw[kv_safe_l0_g] >> irule kv_safe_g_cong_imp >>
  qexistsl_tac [‘l0_read’, ‘l0_sent’] >> simp[] >> metis_tac[kv_eps_agree]
QED

(*---------------------------------------------------------------------------*)
(* KV's topology at a prefix: listens_only, no_connects *)

Theorem LPREFIX_LNTH:
  LPREFIX (fromList evs) io ∧ n < LENGTH evs ⇒ LNTH n io = SOME (EL n evs)
Proof
  rw[LPREFIX_fromList] >> every_case_tac >> gvs[]
  >- (irule LTAKE_LNTH_EL >> metis_tac[]) >>
  ‘LFINITE io’ by (CCONTR_TAC >> gvs[toList]) >>
  ‘io = fromList x’ by metis_tac[to_fromList, THE_DEF] >>
  gvs[LNTH_fromList] >> imp_res_tac IS_PREFIX_LENGTH >>
  ‘n < LENGTH x’ by simp[] >> simp[] >> metis_tac[is_prefix_el]
QED

Theorem MEM_LPREFIX_LNTH:
  LPREFIX (fromList evs) io ∧ MEM ev evs ⇒ ∃n. LNTH n io = SOME ev
Proof
  rw[MEM_EL] >> metis_tac[LPREFIX_LNTH]
QED

Theorem pbytes_w22n:
  LENGTH conf = 2 ⇒ pbytes (w22n conf) = conf
Proof
  strip_tac >> ‘pbytes (w22n conf) = n2w2 (w22n conf)’ by simp[pbytes_def, MarshallingTheory.n2w2_def] >>
  simp[MarshallingTheory.n2w2_w22n]
QED

Theorem kv_topology_prefix:
  l0_topology b io ∧ LPREFIX (fromList evs) io ∧
  (∀conf bs. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ⇒ LENGTH conf = 2) ⇒
  listens_only b evs ∧ no_connects evs ∧ EVERY no_connect evs
Proof
  strip_tac >>
  ‘∀ev. MEM ev evs ⇒ l0_topo_ev b ev’ by metis_tac[MEM_LPREFIX_LNTH, l0_topology_def] >>
  rw[listens_only_def, no_connects_def, EVERY_MEM, no_connect_def]
  >- (first_x_assum drule >> simp[l0_topo_ev_def] >> rw[] >>
      gvs[] >> metis_tac[pbytes_w22n])
  >- (strip_tac >> first_x_assum drule >> simp[l0_topo_ev_def])
  >> strip_tac >> gvs[] >> first_x_assum drule >> simp[l0_topo_ev_def]
QED
