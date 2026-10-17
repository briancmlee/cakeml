(*
  Liveness per client, for the key-value server on the version-2 handle
  layer (kv2_live : kv_live2 for its run in a fair version-2 world), as
  asyncProto2Model's proto2_live: from the version-1 liveness
  (kv_live_rounds) in the renamed world, through the per-episode bridge
  ep_rounds_gen.  Closing is gen_closes2, for any server.
*)
Theory asyncKv2Live
Ancestors
  llist words ffiSpikeSocketFFI ffiSpikeSocketFair asyncM4GRounds
  asyncM4GTrans asyncRunOkGen EchoSpec EchoSpec2 HttpSpec HttpSpecBodies
  HttpKvSpec HttpKvSpec2 socketV2FFI socketV2Fair asyncHLModel
  asyncHLSimWorld asyncHLSimTick asyncHLEchoSpec2 asyncProtoEof
  asyncProto2Model asyncKvModel asyncKvLive asyncKvEof
Libs
  preamble

Theorem brequests_nonempty[local]:
  rs ≠ [] ⇒ brequests rs ≠ []
Proof
  Cases_on ‘rs’ >> simp[brequests_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_brequest_def]
QED

(* MAIN: liveness, per client *)
Theorem kv2_live:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  kv_live2 s2 (gtrace2 (kv_server lfdn) lfdn s2)
Proof
  rw[kv_live2_def] >>
  ‘uses_ok lfdn (kv_server lfdn) ∧ srv_eof_last (kv_server lfdn)’
    by simp[kv_server_uses_ok, kv_server_eof_last] >>
  Cases_on ‘rs = []’
  >- (qexistsl_tac [‘[]’, ‘[]’] >>
      simp[LPREFIX_def, from_toList, reply_bytes_def, bytes_def] >> CASE_TAC) >>
  ‘brequests rs ≠ []’ by simp[brequests_nonempty] >>
  ‘sent2_upto j n s2 ≠ []’ by (strip_tac >> fs[]) >>
  ‘j < dimword (:64) − 1’
    by (drule_all hsim_init >> strip_tac >>
        mp_tac (Q.SPECL [‘n’, ‘v1of (n2w lfdn) s2’, ‘s2’, ‘hinit’]
                 (Q.INST [‘lfd’ |-> ‘n2w lfdn’] data_bound)) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
        gvs[sent2_upto_def, FLAT_EQ_NIL, EVERY_MEM, MEM_MAP] >>
        rename1 ‘MEM y (arrivals2_upto _ _)’ >> Cases_on ‘y’ >> gvs[] >>
        Cases_on ‘n' = j’ >> gvs[] >> res_tac) >>
  ‘sent2_upto j n s2 = sent_upto (hdl (n2w lfdn) j) n (v1of (n2w lfdn) s2)’
    by metis_tac[sent2_rn] >>
  ‘sched_wf (v1of (n2w lfdn) s2)’ by metis_tac[v1of_sched_wf] >>
  ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
    by simp[v1of_def] >>
  ‘kv_live (v1of (n2w lfdn) s2)
     (LFLATTEN (LGENLIST (λi. fromList (grounds_events (interest [n2w lfdn])
        (srelabel (kv_server lfdn)) (v1of (n2w lfdn) s2) i)) NONE))’
    by (irule kv_live_rounds >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
  pop_assum (qspecl_then [‘hdl (n2w lfdn) j’, ‘n’, ‘rs’] mp_tac o REWRITE_RULE [kv_live_def]) >>
  impl_tac >- fs[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))’ >>
  ‘∀i. f i ≠ []’ by simp[Abbr ‘f’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  qexistsl_tac [‘FLAT (GENLIST (hround_events (n2w lfdn) (interest [n2w lfdn])
                                  (srelabel (kv_server lfdn)) s2) (SUC n'))’, ‘ans’] >>
  simp[rounds_LPREFIX] >>
  ‘ep_written j (FLAT (GENLIST (hround_events (n2w lfdn) (interest [n2w lfdn])
                                  (srelabel (kv_server lfdn)) s2) (SUC n'))) =
   bytes_written_to (hdl (n2w lfdn) j) (FLAT (GENLIST f (SUC n')))’
    by (simp[Abbr ‘f’] >> metis_tac[ep_rounds_gen]) >>
  pop_assum SUBST1_TAC >>
  irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
  irule bytes_written_to_mono >> first_assum ACCEPT_TAC
QED
