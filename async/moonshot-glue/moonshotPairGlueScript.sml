(*
  Moonshot step 12 glue, G4 and G5 (design/45 §4.1): the client's episodes
  are paired with KV's through the proxy, and at every instant, per pair,
  KV has read at most what the client sent and the client has read at most
  what KV wrote.  These are the four episode hypotheses of
  kv_client_view_safe (moonshotKvClient), at l0sysEpisodes' l0_ep_sent /
  l0_ep_recvd.

  Everything is over three processes cl (the client), px (the proxy) and kv
  (KV), with
   - tr k t: process k's trace at instant t (proc_events k (TAKE t rs));
   - rl k j: how process k's episode j began (l0_ep_role j of k's whole
     trace);
   - cn: B2's pairing of episodes (l0sys_causal);
   - prx: the proxy's pairing of a front with its backend, by episode
     number.
  The hypotheses, as definitions:
   - b2_conn: what l0sys_causal gives, plus that an unpaired episode reads
     nothing (no outside peer: what `isolated` must give);
   - topology: who listens and who connects where (from moonshot_sys);
   - proxy_safe_ep: proxy_safe_l0 restated over episode numbers.

  G4: comp_ep, the composite map; comp_ep_inj (injectivity),
  comp_ep_unpaired_client and comp_ep_unpaired_kv (an unpaired episode
  reads nothing).  G5: comp_ep_chain, the per-instant chain.
  moonshot_pairs: the four together, in kv_client_view_safe's form.
*)
Theory moonshotPairGlue
Ancestors
  l0sysEpisodes
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The hypotheses *)

(* B2 (l0sys_causal), and no outside peer *)
Definition b2_conn_def:
  b2_conn (cn : num # num -> (num # num) option) rl tr ⇔
    (∀x y. cn x = SOME y ⇔ cn y = SOME x) ∧
    (∀k j k' j'. cn (k, j) = SOME (k', j') ⇒
       ∃p. rl k j = SOME (Connected p) ∧ rl k' j' = SOME (Accepted p) ∨
           rl k j = SOME (Accepted p) ∧ rl k' j' = SOME (Connected p)) ∧
    (∀k j k' j' t. cn (k, j) = SOME (k', j') ⇒
       l0_ep_recvd j' (tr k' t) ≼ l0_ep_sent j (tr k t)) ∧
    (∀k j t. cn (k, j) = NONE ⇒ l0_ep_recvd j (tr k t) = [])
End

(* The proxy px listens on pa and connects to pb, where KV kv listens; the
   client cl connects to pa *)
Definition topology_def:
  topology rl cl px kv pa pb ⇔
    cl ≠ px ∧ cl ≠ kv ∧ px ≠ kv ∧ pa ≠ pb ∧
    (∀k j p. rl k j = SOME (Accepted p) ⇒ k = px ∧ p = pa ∨ k = kv ∧ p = pb) ∧
    (∀k j p. rl k j = SOME (Connected p) ⇒ k = cl ∧ p = pa ∨ k = px ∧ p = pb)
End

(* proxy_safe_l0 over episode numbers: prx is injective; a backend is a
   connect, and every connect is the backend of a front; an unpaired front
   is sent nothing; per pair, the relay prefixes both ways *)
Definition proxy_safe_ep_def:
  proxy_safe_ep prx rl tr px pa pb ⇔
    (∀a a' b. prx a = SOME b ∧ prx a' = SOME b ⇒ a = a') ∧
    (∀a b. prx a = SOME b ⇒ rl px b = SOME (Connected pb)) ∧
    (∀b. rl px b = SOME (Connected pb) ⇒
         ∃a. prx a = SOME b ∧ rl px a = SOME (Accepted pa)) ∧
    (∀a t. rl px a = SOME (Accepted pa) ∧ prx a = NONE ⇒ l0_ep_sent a (tr px t) = []) ∧
    (∀a b t. prx a = SOME b ⇒
       l0_ep_sent b (tr px t) ≼ l0_ep_recvd a (tr px t) ∧
       l0_ep_sent a (tr px t) ≼ l0_ep_recvd b (tr px t))
End

(*---------------------------------------------------------------------------*)
(* G4: the composite map *)

(* Client episode j: its front a at px, a's backend b, and b's episode j'
   at kv *)
Definition comp_ep_def:
  comp_ep cn prx cl px kv j =
    case cn (cl, j) of
    | SOME (k1, a) =>
        if k1 = px then
          case prx a of
          | SOME b =>
              (case cn (px, b) of
               | SOME (k2, j') => if k2 = kv then SOME j' else NONE
               | NONE => NONE)
          | NONE => NONE
        else NONE
    | NONE => NONE
End

Theorem comp_ep_SOME:
  comp_ep cn prx cl px kv j = SOME j' ⇔
  ∃a b. cn (cl, j) = SOME (px, a) ∧ prx a = SOME b ∧ cn (px, b) = SOME (kv, j')
Proof
  rw[comp_ep_def] >> every_case_tac >> gvs[]
QED

(* Access to the hypotheses *)
Theorem b2_sym:
  b2_conn cn rl tr ∧ cn x = SOME y ⇒ cn y = SOME x
Proof
  rw[b2_conn_def] >> metis_tac[]
QED

Theorem b2_flow:
  b2_conn cn rl tr ∧ cn (k, j) = SOME (k', j') ⇒
  l0_ep_recvd j' (tr k' t) ≼ l0_ep_sent j (tr k t)
Proof
  rw[b2_conn_def]
QED

Theorem b2_quiet:
  b2_conn cn rl tr ∧ cn (k, j) = NONE ⇒ l0_ep_recvd j (tr k t) = []
Proof
  rw[b2_conn_def]
QED

Theorem b2_role:
  b2_conn cn rl tr ∧ cn (k, j) = SOME (k', j') ⇒
  ∃p. rl k j = SOME (Connected p) ∧ rl k' j' = SOME (Accepted p) ∨
      rl k j = SOME (Accepted p) ∧ rl k' j' = SOME (Connected p)
Proof
  rw[b2_conn_def]
QED

(* The far end of a connect is an accept on the same port, and back *)
Theorem b2_connected:
  b2_conn cn rl tr ∧ cn (k, j) = SOME (k', j') ∧ rl k j = SOME (Connected p) ⇒
  rl k' j' = SOME (Accepted p)
Proof
  strip_tac >> drule_all b2_role >> rw[] >> gvs[]
QED

Theorem b2_accepted:
  b2_conn cn rl tr ∧ cn (k, j) = SOME (k', j') ∧ rl k j = SOME (Accepted p) ⇒
  rl k' j' = SOME (Connected p)
Proof
  strip_tac >> drule_all b2_role >> rw[] >> gvs[]
QED

(* The client only connects, to pa; KV only accepts, on pb *)
Theorem b2_client:
  b2_conn cn rl tr ∧ topology rl cl px kv pa pb ∧ cn (cl, j) = SOME y ⇒
  rl cl j = SOME (Connected pa)
Proof
  rw[] >> PairCases_on ‘y’ >> drule_all b2_role >> rw[] >>
  gvs[topology_def] >> res_tac >> gvs[]
QED

Theorem b2_kv:
  b2_conn cn rl tr ∧ topology rl cl px kv pa pb ∧ cn (kv, j) = SOME y ⇒
  rl kv j = SOME (Accepted pb)
Proof
  rw[] >> PairCases_on ‘y’ >> drule_all b2_role >> rw[] >>
  gvs[topology_def] >> res_tac >> gvs[]
QED

(* Who is on each port *)
Theorem top_ports:
  topology rl cl px kv pa pb ⇒
  (rl k j = SOME (Accepted pa) ⇒ k = px) ∧ (rl k j = SOME (Accepted pb) ⇒ k = kv) ∧
  (rl k j = SOME (Connected pa) ⇒ k = cl) ∧ (rl k j = SOME (Connected pb) ⇒ k = px)
Proof
  rw[topology_def] >> res_tac >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* G4 *)

Theorem comp_ep_inj:
  b2_conn cn rl tr ∧ proxy_safe_ep prx rl tr px pa pb ∧
  comp_ep cn prx cl px kv j1 = SOME j' ∧ comp_ep cn prx cl px kv j2 = SOME j' ⇒
  j1 = j2
Proof
  rw[comp_ep_SOME] >>
  rename1 ‘cn (px, b1) = SOME (kv, j')’ >> rename1 ‘cn (px, b2) = SOME (kv, j')’ >>
  imp_res_tac b2_sym >> gvs[] >>
  ‘a = a'’ by (fs[proxy_safe_ep_def] >> res_tac) >> gvs[]
QED

(* An unpaired client episode reads nothing *)
Theorem comp_ep_unpaired_client:
  b2_conn cn rl tr ∧ topology rl cl px kv pa pb ∧ proxy_safe_ep prx rl tr px pa pb ∧
  comp_ep cn prx cl px kv j = NONE ⇒
  l0_ep_recvd j (tr cl t) = []
Proof
  strip_tac >>
  Cases_on ‘cn (cl, j)’ >- metis_tac[b2_quiet] >>
  rename1 ‘cn (cl, j) = SOME y’ >> PairCases_on ‘y’ >> rename1 ‘cn (cl, j) = SOME (k1, a)’ >>
  (* the client connects to pa, so k1 accepted on pa: k1 = px *)
  ‘rl k1 a = SOME (Accepted pa)’ by metis_tac[b2_client, b2_connected] >>
  ‘k1 = px’ by metis_tac[top_ports] >> pop_assum SUBST_ALL_TAC >>
  ‘l0_ep_recvd j (tr cl t) ≼ l0_ep_sent a (tr px t)’ by (imp_res_tac b2_sym >> metis_tac[b2_flow]) >>
  Cases_on ‘prx a’
  >- (‘l0_ep_sent a (tr px t) = []’ by (fs[proxy_safe_ep_def] >> metis_tac[]) >> gvs[]) >>
  rename1 ‘prx a = SOME b’ >>
  ‘rl px b = SOME (Connected pb) ∧ l0_ep_sent a (tr px t) ≼ l0_ep_recvd b (tr px t)’
    by (fs[proxy_safe_ep_def] >> metis_tac[]) >>
  Cases_on ‘cn (px, b)’
  >- (‘l0_ep_recvd b (tr px t) = []’ by metis_tac[b2_quiet] >>
      metis_tac[IS_PREFIX_TRANS, IS_PREFIX_NIL]) >>
  rename1 ‘cn (px, b) = SOME y’ >> PairCases_on ‘y’ >> rename1 ‘cn (px, b) = SOME (k2, j')’ >>
  (* px connected to pb, so k2 accepted on pb: k2 = kv *)
  ‘rl k2 j' = SOME (Accepted pb)’ by metis_tac[b2_connected] >>
  ‘k2 = kv’ by metis_tac[top_ports] >> gvs[comp_ep_def]
QED

(* An episode of KV that no client episode maps to reads nothing *)
Theorem comp_ep_unpaired_kv:
  b2_conn cn rl tr ∧ topology rl cl px kv pa pb ∧ proxy_safe_ep prx rl tr px pa pb ∧
  (∀j. comp_ep cn prx cl px kv j ≠ SOME j') ⇒
  l0_ep_recvd j' (tr kv t) = []
Proof
  rw[comp_ep_SOME] >>
  Cases_on ‘cn (kv, j')’ >- metis_tac[b2_quiet] >>
  rename1 ‘cn (kv, j') = SOME y’ >> PairCases_on ‘y’ >> rename1 ‘cn (kv, j') = SOME (k1, b)’ >>
  (* KV accepts on pb, so k1 connected to pb: k1 = px *)
  ‘rl k1 b = SOME (Connected pb)’ by metis_tac[b2_kv, b2_accepted] >>
  ‘k1 = px’ by metis_tac[top_ports] >> pop_assum SUBST_ALL_TAC >>
  ‘l0_ep_recvd j' (tr kv t) ≼ l0_ep_sent b (tr px t)’
    by (imp_res_tac b2_sym >> metis_tac[b2_flow]) >>
  ‘∃a. prx a = SOME b ∧ rl px a = SOME (Accepted pa)’ by (fs[proxy_safe_ep_def] >> metis_tac[]) >>
  ‘l0_ep_sent b (tr px t) ≼ l0_ep_recvd a (tr px t)’ by (fs[proxy_safe_ep_def] >> metis_tac[]) >>
  Cases_on ‘cn (px, a)’
  >- (‘l0_ep_recvd a (tr px t) = []’ by metis_tac[b2_quiet] >>
      metis_tac[IS_PREFIX_TRANS, IS_PREFIX_NIL]) >>
  rename1 ‘cn (px, a) = SOME y’ >> PairCases_on ‘y’ >> rename1 ‘cn (px, a) = SOME (k2, j)’ >>
  (* px accepted on pa, so k2 connected to pa: k2 = cl, and j maps to j' *)
  ‘rl k2 j = SOME (Connected pa)’ by metis_tac[b2_accepted] >>
  ‘k2 = cl’ by metis_tac[top_ports] >> pop_assum SUBST_ALL_TAC >>
  imp_res_tac b2_sym >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* G5: the per-instant chain *)

Theorem comp_ep_chain:
  b2_conn cn rl tr ∧ proxy_safe_ep prx rl tr px pa pb ∧
  comp_ep cn prx cl px kv j = SOME j' ⇒
  l0_ep_recvd j' (tr kv t) ≼ l0_ep_sent j (tr cl t) ∧
  l0_ep_recvd j (tr cl t) ≼ l0_ep_sent j' (tr kv t)
Proof
  rw[comp_ep_SOME] >>
  imp_res_tac b2_sym >>
  ‘l0_ep_sent b (tr px t) ≼ l0_ep_recvd a (tr px t) ∧
   l0_ep_sent a (tr px t) ≼ l0_ep_recvd b (tr px t)’ by (fs[proxy_safe_ep_def] >> metis_tac[]) >>
  metis_tac[b2_flow, IS_PREFIX_TRANS]
QED

(*---------------------------------------------------------------------------*)
(* kv_client_view_safe's episode hypotheses, with
   e = comp_ep cn prx cl px kv, kvs = tr kv, cls = tr cl, and
   snt = kwr = l0_ep_sent, crd = krd = l0_ep_recvd *)
Theorem moonshot_pairs:
  b2_conn cn rl tr ∧ topology rl cl px kv pa pb ∧ proxy_safe_ep prx rl tr px pa pb ⇒
  (∀j1 j2 j'. comp_ep cn prx cl px kv j1 = SOME j' ∧ comp_ep cn prx cl px kv j2 = SOME j' ⇒
              j1 = j2) ∧
  (∀t j. comp_ep cn prx cl px kv j = NONE ⇒ l0_ep_recvd j (tr cl t) = []) ∧
  (∀t j j'. comp_ep cn prx cl px kv j = SOME j' ⇒
     l0_ep_recvd j' (tr kv t) ≼ l0_ep_sent j (tr cl t) ∧
     l0_ep_recvd j (tr cl t) ≼ l0_ep_sent j' (tr kv t)) ∧
  (∀t j'. (∀j. comp_ep cn prx cl px kv j ≠ SOME j') ⇒ l0_ep_recvd j' (tr kv t) = [])
Proof
  metis_tac[comp_ep_inj, comp_ep_unpaired_client, comp_ep_unpaired_kv, comp_ep_chain]
QED
