# v1-conv (⇒ directions of the disciplined sym_equiv): status and next steps

Branch spike/v1-conv. Approved statement shape (2026-10-16):
  echo_sym_equiv_disc ⇔ ∀lfd a prog. v1_disciplined lfd prog ⇒
    (rg_spec C1 ep_echo_guar prog ⇒ echo_spec_le lfd prog) ∧                      [⇐, proved: endpointV1Echo]
    (echo_spec_le lfd prog ⇒ rg_spec (λw. C1 w ∧ nonsat lfd a w) ep_echo_guar prog) [⇒, this work]
  C1 w := ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w;
  echo_spec_le = echo_spec over v1 server worlds with sched_connects_le M, M+3<2^64;
  nonsat = endpointEcho2Conv's. Same shape for http_b and kv.

Done (on this branch):
- endpointV1Sim: v12rel generalized. Any reserved fds; the alloc clause is consistency on
  exp_used res lfd cs j = res ++ [lfd] ++ REVERSE (TAKE j cs); the bound includes reserved.
  v12rel_init now needs sched_wf. Also core_conns_distinct, conn_fd_sched (shared;
  V1Proj's conn_fd_EL removed). LSP-green; V1Sim built green before the Settle merge.
- endpointV1Run: v1_trace adapted (LSP-green).
- endpointV1Conv (WIP, NOT yet built): cfds/cfd (client j's fd = alloc j (exp_used ..)),
  cfds_GENLIST, cfd_alloc, cfds_fresh, rn2_arr/rn2_step/rn2_sched (+ LHD/LTL), ix_ok,
  rn1_rn2_step (the renaming inverts), rn2_step_count, step_ok2_ix, rn2_step_conns,
  v1of2 (the v1 world of a v2 world), F2_inj.

Next steps, in order:
1. Holmake the whole endpoint-world on this branch. Fix V1Inst/V1Disc/V1Echo/V1Http/V1Kv
   after the v12rel generalization (expected: only small call-site changes, e.g.
   v12rel_init's sched_wf hypothesis in V1Inst.v2of1_server_world2).
2. endpointV1Conv: v1of2_sched (draft below), via LUNFOLD_EQ with the relation
   "(cs, L) ~ ll iff ∃n. cs = GENLIST F (clients of ticks2 n sk2), L = rn2_sched F (same)
   (ticks2 n sk2).future, ll = (ticks2 n sk2).future".
   The last step remains: show the new state matches at SUC n (ticks2_SUC', tick2_def,
   FOLDL_deliver2 future).
3. Reverse arrival lemma: v12core ∧ arrival_ok2 s2 (rn1 of a) ∧ freshness ⇒ arrival_ok s1 a,
   then the step version. Then sched_wf (v1of2 sk2) by induction on ticks (v12core along
   ticks, k = 0).
4. v1of2_props: server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧ LENGTH res + M + 3 < 2^64 ⇒
   server_world lfd (v1of2 lfd sk2) ∧ sched_connects_le M .. ∧ v12rel lfd (v1of2..).sched (v1of2..) sk2.
   The alloc clause comes from cfd_alloc and sched_conns = GENLIST F n (rn2_step_conns).
5. Generalize endpointEcho2Conv.endpoint_of_echo_spec2 over a hypothesis
   H := ∀sk. server_world2 lfd sk ∧ bounded ⇒ ∃io. sem ∧ echo_safe2 io ∧ echo_live2 sk io
   (echo_spec2 is one instance). The v1 instance comes from echo_spec_le on v1of2 sk +
   v12_diverge + translations (sent2_upto j = sent_upto (cfd j), ep_written j = written c_j:
   reuse V1Proj's proj_v1/sent_v2of1-style lemmas, in the reverse direction).
6. HTTP and KV ⇒: need an ext1-style world whose new client sends a valid full request
   (the ticks_forever argument); otherwise as echo.

## Draft of v1of2_sched (not yet proved; it was removed from the script so the commit is cheat-free)
```
(* MAIN: renamed back, the version-1 schedule is version 2's *)
Theorem v1of2_sched:
  server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ⇒
  rn1_sched [] (v1of2 lfd sk2).sched = sk2.future
Proof
  strip_tac >> simp[v1of2_def] >>
  ‘∀n. LENGTH (ticks2 n sk2).clients ≤ M’
    by (fs[server_world2_def] >> metis_tac[ticks2_clients, ADD]) >>
  irule LUNFOLD_EQ >>
  qexists_tac ‘λ(cs, L) ll. ∃n. cs = GENLIST (F2 lfd sk2) (LENGTH (ticks2 n sk2).clients) ∧
                                L = rn2_sched (F2 lfd sk2) (LENGTH (ticks2 n sk2).clients)
                                      (ticks2 n sk2).future ∧
                                ll = (ticks2 n sk2).future’ >>
  conj_tac >- (simp[] >> qexists_tac ‘0’ >> fs[ticks2_def, server_world2_def]) >>
  simp[FORALL_PROD] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qabbrev_tac ‘s = ticks2 n sk2’ >>
  Cases_on ‘LHD s.future’ >> simp[rn2_sched_LHD]
  >- (disj1_tac >> Cases_on ‘s.future’ >> fs[]) >>
  rename1 ‘LHD s.future = SOME st’ >>
  ‘step_ok2 s st’
    by (fs[server_world2_def, sched_wf2_def] >>
        first_x_assum (qspec_then ‘n’ mp_tac) >> simp[Abbr ‘s’, next_step2_def]) >>
  ‘LENGTH (ticks2 (SUC n) sk2).clients = FST (rn2_step (F2 lfd sk2) (LENGTH s.clients) st)’
    by (simp[ticks2_SUC', rn2_step_count, Abbr ‘s’] >>
        simp[tick2_def] >> drule step_ok2_clients >> simp[]) >>
  ‘rn1_step (GENLIST (F2 lfd sk2) (LENGTH s.clients))
     (SND (rn2_step (F2 lfd sk2) (LENGTH s.clients) st)) =
   (GENLIST (F2 lfd sk2) (FST (rn2_step (F2 lfd sk2) (LENGTH s.clients) st)), st)’
    by (irule rn1_rn2_step >> qexists_tac ‘M + 1’ >>
        simp[step_ok2_ix] >> conj_tac
        >- (qpat_x_assum ‘LENGTH (ticks2 (SUC n) sk2).clients = _’ (SUBST1_TAC o SYM) >>
            first_x_assum (qspec_then ‘SUC n’ mp_tac) >> decide_tac) >>
        metis_tac[F2_inj, server_world2_def]) >>
  simp[] >>
  ‘∃ll'. s.future = st ::: ll'’ by (Cases_on ‘s.future’ >> fs[]) >>
  simp[rn2_sched_LTL] >>
  qexists_tac ‘SUC n’ >>
  simp[ticks2_SUC', Abbr ‘s’] >> simp[tick2_def] >>
  cheat
QED
```
