(*
  KV's obligations for its raw liveness on the PF run (kv_live_l0; the
  echo's honestEchoL0Obl is the template): the PF KV, m = srelabel
  (kv_server lfdn) polled through the live list (D26).

   - uses_reads_accepted: any server that uses the socket API correctly
     (asyncRunOkGen's uses_ok) reads only handles it was handed
     (honest-ffi's reads_accepted), so kv_reads_handed;
   - kv_S1: S1 (S1_live).

  MAIN: kv_reads_handed, kv_S1.
*)
Theory honestKvL0Obl
Ancestors
  honestL1PFOblLive honestEchoReadsAcc honestL1PFLive honestL1PFRound
  asyncRunOkGen asyncM4ServerUses asyncKvModel asyncServerSafety asyncTranscript
  asyncServer asyncLevel2 asyncLevel1 asyncCore asyncM4SockModel asyncM4Relabel
  asyncM4RelabelDist asyncM3World asyncM4LiveInterest
Libs
  preamble

Overload KS = “srelabel (kv_server lfdn)”
Overload KI = “asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel (kv_server lfdn)))”

(* The PF KV's run hypotheses (honestEchoL0Obl's echo_run, for KV) *)
Definition kv_run_def:
  kv_run lfdn pol w0 ⇔
    run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
    (∀n. SND (pcm (n2w lfdn) pol KI KS w0 n) + 1 < dimword (:64)) ∧
    lfdn < dimword (:64)
End

(* ------------------------------------------------------------------------
   Reads only on handed handles, for any uses_ok server
   ------------------------------------------------------------------------ *)

(* A pair on fd after acc_first fd: fd was handed out before *)
Theorem acc_first_on_fd:
  ∀tr. acc_first fd tr ∧ MEM p tr ∧ on_fd fd p ⇒ MEM fd (accepted tr)
Proof
  Induct >> simp[acc_first_def] >> rpt gen_tac >>
  Cases_on ‘accepts fd h’ >> simp[]
  >- (strip_tac >> fs[accepts_def, accepted_def]) >>
  strip_tac >> gvs[] >> fs[accepted_def] >>
  PairCases_on ‘h’ >> simp[] >> every_case_tac >> simp[]
QED

Theorem sfa_read[local]:
  sfa a = Read h k ⇒ ∃fd. a = Read fd ∧ h = n2w fd
Proof
  Cases_on ‘a’ >> simp[sfa_def]
QED

Theorem sfr_accepted[local]:
  sfr r = Accepted fd ⇒ ∃c. r = Accepted (SOME c) ∧ fd = w2n c
Proof
  Cases_on ‘r’ >> TRY (Cases_on ‘o'’) >> rw[sfr_def]
QED

(* MAIN: a uses_ok server reads only handles it was handed *)
Theorem uses_reads_accepted:
  uses_ok lfd m ⇒ reads_accepted (srelabel m)
Proof
  rw[reads_accepted_def, uses_ok_def, new_actions_relabel, MEM_MAP] >>
  qpat_x_assum ‘Read _ _ = sfa _’ (assume_tac o SYM) >>
  drule sfa_read >> strip_tac >> gvs[] >>
  drule new_trans >> strip_tac >>
  ‘MEM fd (accepted (trans m (MAP sfs hh)))’
    by (irule acc_first_on_fd >> conj_tac
        >- (qpat_x_assum ‘∀hh. _’ (qspec_then ‘MAP sfs hh’ strip_assume_tac) >>
            qpat_x_assum ‘∀fd. acc_first _ _’ (qspec_then ‘fd’ ACCEPT_TAC)) >>
        qpat_x_assum ‘MEM (Read fd, NONE) _’ (irule_at Any) >> simp[on_fd_def]) >>
  drule accepted_resp >> rw[MEM_MAP] >>
  gvs[snap_map_def, MEM_MAP] >>
  qpat_x_assum ‘Accepted _ = sfr _’ (assume_tac o SYM) >>
  drule sfr_accepted >> strip_tac >> gvs[] >>
  first_x_assum (irule_at Any) >> simp[]
QED

Theorem kv_reads_handed:
  reads_handed (n2w lfdn) [n2w lfdn] (srelabel (kv_server lfdn))
Proof
  simp[reads_handed_def] >> irule uses_reads_accepted >>
  qexists_tac ‘lfdn’ >> simp[kv_server_uses_ok]
QED

(* MAIN (D26): the PF KV meets S1 *)
Theorem kv_S1:
  kv_run lfdn pol w0 ⇒ S1 (n2w lfdn) pol KI KS w0
Proof
  rw[kv_run_def] >> irule S1_live >> fs[winv_def, kv_reads_handed]
QED
