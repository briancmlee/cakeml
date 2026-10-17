(*
  The echo's SQ obligation on the live interest list (echo_SQ):

     echo_run lfdn pol w0 ∧ linv (n2w lfdn) w0 ⇒ SQ (n2w lfdn) pol EI (K F) ES w0

  by honestL1BSQLive's SQ_live: the live-held clause is live_held with
  echo_reads_handed, the drain clause is echo_drain, and settling is
  server_settles carried through the socket relabelling (settles_relabel).
*)
Theory honestEchoL0BSQ
Ancestors
  asyncCore asyncLevel1 asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  asyncM4LiveInterest honestEchoQuiesce honestL1BSQLive honestL1PFOblLive
  honestEchoReadsAcc honestEchoL0Obl honestEchoL0BDrain honestL1PFRound
Libs
  preamble

Overload ES = “srelabel (server lfdn)”
Overload EI = “asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel (server lfdn)))”

Theorem noready_snap_map:
  fe ∅ = ∅ ⇒ ∀q. noready q ⇒ noready (MAP (snap_map fe fr) q)
Proof
  strip_tac >> Induct >> simp[snap_map_def]
QED

(* Settling survives a relabelling that keeps empty ready sets empty *)
Theorem settles_relabel:
  fe ∅ = ∅ ∧ settles d m (MAP (snap_map fe fr) h) ⇒
  settles d (relabel fa (snap_map fe fr) m) h
Proof
  simp[settles_def, new_actions_relabel] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘MAP (snap_map fe fr) q’ mp_tac) >>
  (impl_tac >- (conj_tac >- (irule noready_snap_map >> ASM_REWRITE_TAC[]) >> simp[])) >>
  simp[relabel_def, MAP_TAKE]
QED

Theorem srelabel_settles:
  settles 2 (srelabel (server lfdn)) h
Proof
  irule settles_relabel >> simp[sfe_def, server_settles]
QED

(* MAIN: the echo meets SQ on the live list *)
Theorem echo_SQ:
  echo_run lfdn pol w0 ∧ linv (n2w lfdn) w0 ⇒ SQ (n2w lfdn) pol EI (K F) ES w0
Proof
  strip_tac >> irule SQ_live >>
  ‘run_ok (n2w lfdn) pol EI ES w0’ by fs[echo_run_def] >> ASM_REWRITE_TAC[] >>
  rpt conj_tac
  >- (qexists_tac ‘2’ >> rewrite_tac[srelabel_settles])
  >- (rpt strip_tac >> irule live_held >> simp[echo_reads_handed] >>
      fs[echo_run_def, winv_def])
  >- (rpt strip_tac >> drule_all echo_drain >> simp[dr_def])
QED
