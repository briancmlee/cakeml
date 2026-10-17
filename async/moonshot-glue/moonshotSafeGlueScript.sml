(*
  Moonshot step 12 glue: the composition (design/45 §4.1), with every
  remaining hypothesis explicit.  The client's raw trace is linearizable
  against KV (kv_client_safe at l0_ep_sent / l0_ep_recvd), from:

   [B2]   b2_conn cn rl tr: l0sys_causal, plus "an unpaired episode reads
          nothing", which `isolated` must give (step12-gaps.md B2, B3);
   [TOP]  topology rl cl px kv pa pb: who listens and connects where
          (gaps T1–T8: moonshot_sys, the client's and KV's raw claims);
   [PX]   the proxy's raw claim (step 9 rev 5, proxy_safe_l0) on its io_p,
          with its whole system trace ft a prefix of io_p, and ep_ok ft
          (gaps W1–W4, honest-L0 facts);
   [G2]   the instants: tr k t is process k's trace at instant t,
          monotone in t, KV's a prefix of io_k, and every prefix of the
          client's io_c some instant's (gaps G2/G3);
   [KV]   KV's raw claim (step 11): kv_safe_g at l0_ep_recvd / l0_ep_sent.

  moonshot_view_safe is moonshotKvClient.kv_client_view_safe with
  e = comp_ep cn (prx_of pr ft) cl px kv (moonshotPairGlue.moonshot_pairs,
  moonshotProxyGlue.proxy_safe_bridge).
*)
Theory moonshotSafeGlue
Ancestors
  moonshotKvClient moonshotPairGlue moonshotProxyGlue
Libs
  preamble

Theorem moonshot_view_safe:
  (* [B2] *)
  b2_conn cn rl tr ∧
  (* [TOP] *)
  topology rl cl px kv pa pb ∧
  (* [PX] *)
  proxy_safe_l0 kt hw pa pb pr io_p ∧ LPREFIX (fromList ft) io_p ∧ ep_ok ft ∧
  pa < 65536 ∧ pb < 65536 ∧
  (∀t. tr px t ≼ ft) ∧ (∀j. rl px j = l0_ep_role j ft) ∧
  (* [G2] *)
  (∀(t:num) t'. t ≤ t' ⇒ tr kv t ≼ tr kv t' ∧ tr cl t ≼ tr cl t') ∧
  (∀t. LPREFIX (fromList (tr kv t)) io_k) ∧
  (∀evs. LPREFIX (fromList evs) io_c ⇒ ∃t. tr cl t = evs) ∧
  (* [KV] *)
  kv_safe_g l0_ep_recvd l0_ep_sent io_k ⇒
  kv_client_safe l0_ep_sent l0_ep_recvd io_c
Proof
  strip_tac >>
  ‘proxy_safe_ep (prx_of pr ft) rl tr px pa pb’ by metis_tac[proxy_safe_bridge] >>
  ‘topology rl cl px kv pa pb’ by simp[] >>
  drule_all moonshot_pairs >> strip_tac >>
  irule (INST_TYPE [alpha |-> “:io_event”] kv_client_view_safe) >>
  qexistsl_tac [‘tr cl’, ‘comp_ep cn (prx_of pr ft) cl px kv’, ‘io_k’, ‘l0_ep_recvd’,
                ‘tr kv’, ‘l0_ep_sent’] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
