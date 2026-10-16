(*
  The bridge between the key-value server's episodes (version 2, the
  handle loop) and its model transcript (version 1, in the renamed world
  v1of), round by round:
   - kv2_rounds_bytes: what episode j had read by the end of round k, and
     written by the end of round k + 1, are the bytes read and written on
     handle hdln lfdn j in the model transcript after k rounds;
   - kv2_query_handle: every query the store answered is from a handle
     hdln lfdn j handed out by then (so queries can be keyed by episode).
*)
Theory asyncKv2Bridge
Ancestors
  llist words ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore asyncLevel1
  asyncTranscript asyncServer asyncServerSafety asyncM4GRounds asyncM4GTrans
  asyncM4SockInv asyncM4SockModel asyncRunOkGen EchoSpec EchoSpec2 HttpSpec
  socketV2FFI socketV2Fair asyncHLModel asyncHLSimWorld asyncHLSimTick
  asyncHLEpisodes asyncHLEchoSpec2 asyncProtoEof asyncHLEofGen
  asyncHLSimRunGen asyncHLSimTraceGen asyncProto2Model asyncWithStore
  asyncServerWithK asyncKvHandler asyncKvModel asyncKvEof
Libs
  preamble

(* the model transcript after k rounds, in the renamed world *)
Overload KT1 = “λlfdn s2 k. TSg (kv_server lfdn) (interest [n2w lfdn : word64])
                                (v1of (n2w lfdn) s2) k”
(* the handle loop's events of the first k rounds *)
Overload KP2 = “λlfdn s2 k. FLAT (GENLIST (hround_events (n2w lfdn)
                                (interest [n2w lfdn : word64]) (srelabel (kv_server lfdn)) s2) k)”

Theorem hdln_lt[local]:
  lfdn < dimword (:64) ∧ j < dimword (:64) − 1 ⇒ hdln lfdn j < dimword (:64)
Proof
  rw[hdln_def]
QED

Theorem w2n_hdl[local]:
  lfdn < dimword (:64) ∧ j < dimword (:64) − 1 ⇒
  w2n (hdl (n2w lfdn : word64) j) = hdln lfdn j
Proof
  strip_tac >> simp[hdl_def] >> drule_all hdln_lt >> simp[]
QED

(* MAIN: per episode, the bytes at round boundaries are the model's *)
Theorem kv2_rounds_bytes:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ∧ j < dimword (:64) − 1 ⇒
  ep_written j (KP2 lfdn s2 (SUC k)) =
    HttpSpec$bytes (FLAT (written (hdln lfdn j) (KT1 lfdn s2 k))) ∧
  ep_read j (KP2 lfdn s2 k) =
    HttpSpec$bytes (FLAT (read (hdln lfdn j) (KT1 lfdn s2 k)))
Proof
  strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn) ∧ srv_eof_last (kv_server lfdn)’
    by simp[kv_server_uses_ok, kv_server_eof_last] >>
  ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
    by simp[v1of_def] >>
  ‘∀k. ep_read j (KP2 lfdn s2 k) =
         bytes_read_from (hdl (n2w lfdn) j)
           (FLAT (GENLIST (grounds_events (interest [n2w lfdn]) (srelabel (kv_server lfdn))
                             (v1of (n2w lfdn) s2)) k)) ∧
       ep_written j (KP2 lfdn s2 k) =
         bytes_written_to (hdl (n2w lfdn) j)
           (FLAT (GENLIST (grounds_events (interest [n2w lfdn]) (srelabel (kv_server lfdn))
                             (v1of (n2w lfdn) s2)) k))’
    by metis_tac[ep_rounds_gen] >>
  ‘w2n (hdl (n2w lfdn : word64) j) = hdln lfdn j’ by simp[w2n_hdl] >>
  qspecl_then [‘kv_server lfdn’, ‘lfdn’, ‘v1of (n2w lfdn) s2’, ‘hdl (n2w lfdn) j’, ‘k’,
               ‘interest [n2w lfdn]’]
    mp_tac (Q.GENL [‘m’, ‘lfdn’, ‘s0’, ‘c’, ‘n’, ‘ifds’] gen_rounds_bytes) >>
  impl_tac >- fs[] >> strip_tac >> fs[HttpSpecTheory.bytes_def]
QED

(* MAIN: the store's queries come from handed-out handles *)
Theorem kv2_query_handle:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ∧
  EXISTS (on_fd fd) (KT1 lfdn s2 k) ⇒
  ∃j. j < dimword (:64) − 1 ∧ fd = hdln lfdn j
Proof
  strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
    by simp[v1of_def] >>
  qpat_x_assum ‘EXISTS _ _’ (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
  gvs[MEM_SPLIT] >>
  ‘MEM fd (accepted (KT1 lfdn s2 k)) ∧ fd < dimword (:64)’
    by (irule TS_on_fd_lt_g >> simp[] >>
        conj_tac >- (qexistsl_tac [‘e’, ‘l1’, ‘l2’] >> simp[]) >>
        qexists_tac ‘lfdn’ >> simp[]) >>
  ‘accepted (KT1 lfdn s2 k) =
   MAP w2n (wacc (SPg (kv_server lfdn) (interest [n2w lfdn]) (v1of (n2w lfdn) s2) k))’
    by metis_tac[accepted_TSg] >>
  drule_all hrun_sim_gen >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  Cases_on ‘hst (n2w lfdn) (interest [n2w lfdn]) (srelabel (kv_server lfdn)) s2 k’ >>
  rename1 ‘_ = (sk, hk)’ >> gvs[] >>
  qpat_x_assum ‘GENLIST _ _ = wacc _’ (assume_tac o SYM) >> gvs[MEM_MAP, MEM_GENLIST] >>
  rename1 ‘j < hk.nxt’ >> qexists_tac ‘j’ >>
  ‘hk.nxt ≤ LENGTH sk.clients’ by fs[hsim_def, hsim0_def] >>
  ‘sk.clients ≠ []’ by (strip_tac >> fs[]) >>
  ‘LENGTH sk.clients + 1 < dimword (:64)’ by metis_tac[hsim_def, hsim0_bound] >>
  ‘j < dimword (:64) − 1’ by fs[] >> conj_tac >- fs[] >> irule w2n_hdl >> fs[]
QED
