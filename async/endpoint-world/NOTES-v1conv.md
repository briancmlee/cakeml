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

UPDATE (58262ecb8, Holmake green): v1of2_ticks (v1of2 follows sk2 along ticks, every
step effective), v1of2_conns (sched_conns m = GENLIST F2 (nconn sk2 m)), v1of2_props
(server_world, ∀m. LENGTH (sched_conns m ..) ≤ M, v12rel). Steps 2-4 below are DONE.
sched_connects_le form: convert with V1Inst's sched_connects_le_conns (make it public).

BOUNDARY ISSUE (DECIDED 2026-10-16 by the user: nonsat1 for the three ⇒ directions): ⇒ with
nonsat is false when w.reserved = [] and M = 2^64-4 (a program that stops polling after
accepting 2^64-4 clients that have all sent EOF meets echo_spec_le but not ticks_forever).
Proposed: nonsat1 (reserved + M + 4 < 2^64) for the v1 ⇒ directions. Working with nonsat1.

ECHO ⇒ DONE (endpointV1EchoConv, LSP 15/15; see the build log for Holmake):
  endpoint_of_echo_spec_le: v1_disciplined ∧ echo_spec_le ⇒
    rg_spec (C1 ∧ nonsat1 lfd a w) ep_echo_guar prog
  echo_sym_equiv_disc_thm: both directions (⇐ from endpointV1Echo).
  Route: w ↦ w2 = w with v2 calls (rclass_v1: rely restricted to v1 calls);
  sk0 = v2of w; v1of2 sk0 bounded (v1of2_props); echo_spec_le there; v1of2_run
  (fd_disciplined, run in sk0); live2_of_v1 (echo_live → echo_live2 via v1of2_sent,
  v1of2_written, sent2_unconn); endpointEcho2Conv.endpoint_of_live2 (liveness, ticks;
  the ext1 worlds bounded by M+1, hence nonsat1); ep_guar_v1 back to v1 calls;
  v1_sym_safe (ren_evs_prefix_inv + proj_v1/proj_ren_beyond).
  Shared refactors: endpointV2Sim.polls_rely/v2of_props_polls; endpointEcho2Conv
  rely_on/rclass/live2_ticks/endpoint_of_live2 (old statements unchanged).

Next: HTTP-b and KV ⇒. endpoint_of_live2/live2_ticks are echo-specific (echo_live2,
ext1 sends [0w]): generalise over the liveness relation P and ext1's request bytes, so
the new client sends a valid full request; then copy the echo route per server.

Older next steps, in order:
1. Holmake the whole endpoint-world on this branch. Fix V1Inst/V1Disc/V1Echo/V1Http/V1Kv
   after the v12rel generalization (expected: only small call-site changes, e.g.
   v12rel_init's sched_wf hypothesis in V1Inst.v2of1_server_world2).
2. DONE: endpointV1Conv.v1of2_sched (LSP 16/16), via LUNFOLD_EQ with the relation
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
