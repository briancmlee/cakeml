(*
  P4 (design/46), step E2: L1's handle j against the version-2 key-value
  server's episode j.

  The handle loop's history of the key-value server is its model history
  (hrun_sim_gen), so per handle, the bytes the server wrote and read in
  the renamed transcript are those in its model transcript, which
  asyncKv2Bridge's kv2_rounds_bytes ties to episode j of the handle
  loop's trace.

  hwritten_bytes / hread_bytes: per handle, the renamed transcript's bytes
  are the model transcript's, for any server that uses only accepted fds.
  hdl_v2_bytes: after n rounds, handle j's writes are episode j's writes
  at instant n + 1, and its reads are episode j's reads at instant n.
*)
Theory honestKvL0Pair
Ancestors
  words asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4ServerUses
  asyncRunOkGen HttpSpec asyncHLModel asyncHLEpisodes asyncHLSimRunGen
  asyncProto2Model asyncKvModel asyncKv2Bridge
  honestEchoL0Model honestEchoL0Run honestKvL0Run
Libs
  preamble

Overload rl = “λxs ys. MAP (λ(a,r). (sfa a, r)) xs = MAP (λ(a,r). (a, OPTION_MAP sfr r)) ys”

(* Copies of honestEchoL0Model's local w2n_lt64, rl_written and rl_read *)
Theorem w2n_lt64[local]:
  w2n (c : word64) < 18446744073709551616
Proof
  assume_tac (INST_TYPE [alpha |-> “:64”] w2n_lt) >> fs[]
QED

Theorem rl_written[local]:
  ∀xs ys. rl xs ys ∧ (∀fd d r. MEM (Write fd d, r) xs ⇒ fd < dimword (:64)) ⇒
        hwritten hd ys = FLAT (MAP (MAP (n2w o ORD)) (written (w2n hd) xs))
Proof
  Induct >> Cases_on ‘ys’ >> simp[hwritten_def, written_def] >>
  gen_tac >> PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  impl_tac >- metis_tac[] >>
  simp[hwritten_def, written_def] >> strip_tac >>
  Cases_on ‘h'0’ >> gvs[sfa_def] >>
  first_x_assum (qspecl_then [‘n’, ‘s’, ‘OPTION_MAP sfr h1’] mp_tac) >> simp[] >> strip_tac >>
  rw[] >> gvs[w2n_n2w] >> CCONTR_TAC >> gvs[w2n_n2w]
QED

Theorem rl_read[local]:
  ∀xs ys. rl xs ys ∧ (∀fd r. MEM (Read fd, r) xs ⇒ fd < dimword (:64)) ⇒
        hread hd ys = FLAT (MAP (MAP (n2w o ORD)) (read (w2n hd) xs))
Proof
  Induct >> Cases_on ‘ys’ >> simp[hread_def, read_def] >>
  gen_tac >> PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  impl_tac >- metis_tac[] >>
  simp[hread_def, read_def] >> strip_tac >>
  Cases_on ‘h'0’ >> gvs[sfa_def] >> Cases_on ‘h1’ >> gvs[] >>
  first_x_assum (qspecl_then [‘n’, ‘SOME (sfr x)’] mp_tac) >> simp[] >> strip_tac >>
  Cases_on ‘x’ >> gvs[sfr_def] >>
  TRY (rename1 ‘Got oo’ >> Cases_on ‘oo’) >> TRY (rename1 ‘Accepted oo’ >> Cases_on ‘oo’) >>
  gvs[sfr_def] >>
  ‘n2w n = hd ⇔ n = w2n hd’ by (eq_tac >> rw[] >> simp[w2n_n2w]) >>
  rw[] >> gvs[bytes_round_trip]
QED

(* Copies of asyncKv2Bridge's local hdln_lt and w2n_hdl *)
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

Theorem rl_srelabel[local]:
  rl (trans m (MAP sfs h)) (trans (srelabel m) h)
Proof
  irule trans_relabel >> simp[snap_map_def]
QED

(* A server that uses only accepted fds uses only fds below 2^64 *)
Theorem uses_ok_fd_lt:
  uses_ok lfd m ∧ MEM p (trans m (MAP sfs h)) ∧ on_fd fd p ⇒ fd < dimword (:64)
Proof
  strip_tac >>
  ‘acc_first fd (trans m (MAP sfs h))’ by fs[uses_ok_def] >>
  drule_all acc_first_accepted >>
  assume_tac (Q.INST [‘h’ |-> ‘h’] rl_srelabel) >>
  drule rl_accepted >> disch_then (fn th => rewrite_tac[th]) >>
  simp[MEM_MAP, PULL_EXISTS, w2n_lt64]
QED

Theorem hwritten_bytes:
  uses_ok lfd m ⇒
  hwritten hd (trans (srelabel m) h) = bytes (FLAT (written (w2n hd) (trans m (MAP sfs h))))
Proof
  strip_tac >> assume_tac rl_srelabel >> drule rl_written >>
  impl_tac
  >- (rpt strip_tac >> irule uses_ok_fd_lt >>
      qexistsl [‘h’, ‘lfd’, ‘m’, ‘(Write fd d, r)’] >> simp[on_fd_def]) >>
  simp[bytes_def, MAP_FLAT]
QED

Theorem hread_bytes:
  uses_ok lfd m ⇒
  hread hd (trans (srelabel m) h) = bytes (FLAT (read (w2n hd) (trans m (MAP sfs h))))
Proof
  strip_tac >> assume_tac rl_srelabel >> drule rl_read >>
  impl_tac
  >- (rpt strip_tac >> irule uses_ok_fd_lt >>
      qexistsl [‘h’, ‘lfd’, ‘m’, ‘(Read fd, r)’] >> simp[on_fd_def]) >>
  simp[bytes_def, MAP_FLAT]
QED

Theorem kv_hwritten_bytes = GEN_ALL (MATCH_MP hwritten_bytes (SPEC_ALL kv_server_uses_ok))
Theorem kv_hread_bytes = GEN_ALL (MATCH_MP hread_bytes (SPEC_ALL kv_server_uses_ok))

(* The executed rounds read what the whole transcript reads *)
Theorem hread_texec:
  (∀i. i < LENGTH h ⇒ LENGTH (EL i h).results = LENGTH (new_actions (log_of m) (TAKE i h))) ⇒
  hread hd (texec m h) = hread hd (trans m h)
Proof
  strip_tac >> drule trans_texec >> simp[]
QED

(* MAIN: after n rounds of the handle loop, handle j's writes are episode
   j's writes at instant n + 1 and its reads are episode j's reads at
   instant n *)
Theorem hdl_v2_bytes:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ∧ j < dimword (:64) − 1 ⇒
  hwritten (hdl (n2w lfdn) j)
    (trans (srelabel (kv_server lfdn)) (hhist (n2w lfdn) EI (srelabel (kv_server lfdn)) s2 n)) =
    ep_written j (KP2 lfdn s2 (SUC n)) ∧
  hread (hdl (n2w lfdn) j)
    (trans (srelabel (kv_server lfdn)) (hhist (n2w lfdn) EI (srelabel (kv_server lfdn)) s2 n)) =
    ep_read j (KP2 lfdn s2 n)
Proof
  strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  drule_all hrun_sim_gen >>
  disch_then (qspec_then ‘n’ (fn th => REWRITE_TAC [CONJUNCT1 th])) >>
  ‘w2n (hdl (n2w lfdn : word64) j) = hdln lfdn j’ by (irule w2n_hdl >> simp[]) >>
  simp[kv_hwritten_bytes, kv_hread_bytes] >>
  drule_all kv2_rounds_bytes >> simp[]
QED
