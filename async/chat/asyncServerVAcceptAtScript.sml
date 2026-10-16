(*
  Accept progress with a bound (for the library): m_queue_progress
  (asyncServerVLive) says a connection at position k of the listener's
  queue at round n is eventually handed out; the same proof shows it is
  handed out by round n + 3 (k + 1).  (A machine that keeps accepting,
  accepts_progress, accepts at least once in every 2 rounds in which the
  listener is readable, so each 3 rounds move c forward.)
*)
Theory asyncServerVAcceptAt
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec HttpSpec
  asyncM3World asyncM4GRounds asyncM4Relabel asyncM4RelabelDist
  asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop asyncM4EchoRunOk
  asyncM4Sched asyncM4Account asyncM4LiveProg asyncM4LiveWorld asyncM4ReadSoon
  asyncM4Queue asyncM4AcceptSoon asyncM4Drain asyncRunOkGen asyncServerWith
  asyncM4ServerUses asyncServerWithUses asyncSWProgress asyncSWSock
  asyncServerWithLive asyncServerV asyncServerVProgress asyncServerVLive
Libs
  preamble

Theorem m_queue_progress_at:
  asyncLevel1$wf (M : 'mx smach) ∧
  accepts_progress lfdn M ∧ uses_ok lfdn M ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k (gstate (EI lfdn) (srelabel M) s0 n) ⇒
        ∃N. N ≤ n + 3 * (k + 1) ∧ MEM c (wacc (SPg M (EI lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[])
  >> completeInduct_on ‘k’ >> rpt strip_tac
  >> Cases_on ‘MEM c (wacc (SPg M (EI lfdn) s0 (n + 3)))’
  >- (qexists_tac ‘n + 3’ >> simp[])
  (* not handed out by round n + 3: still pending in rounds n .. n + 3 *)
  >> ‘∀d. d ≤ 3 ⇒ ∃k'. queued (n2w lfdn) c k' (gstate (EI lfdn) (srelabel M) s0 (n + d)) ∧
                       k' ≤ k’
       by (rpt strip_tac
           >> qspecl_then [‘EI lfdn’, ‘srelabel M’, ‘s0’, ‘n’, ‘n2w lfdn’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘l’, ‘c’] rounds_queued)
           >> simp[] >> disch_then (qspecl_then [‘d’, ‘k’] mp_tac) >> simp[]
           >> strip_tac >- (‘MEM c (wacc (SPg M (EI lfdn) s0 (n + 3)))’
                              suffices_by metis_tac[]
                            >> irule wacc_mono >> qexists_tac ‘d + n’ >> simp[])
           >> metis_tac[])
  (* so M accepts in round n + 1 or n + 2 *)
  >> qspecl_then [‘s0’, ‘lfdn’, ‘n’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘n’] m_accept_soon_s)
  >> impl_tac
  >- (simp[] >> rpt strip_tac
      >> first_x_assum (qspec_then ‘j − n’ mp_tac) >> simp[] >> strip_tac
      >> ‘n + (j − n) = j’ by simp[] >> gvs[] >> metis_tac[queued_ready])
  >> strip_tac
  (* which moves c forward *)
  >> first_assum (qspec_then ‘i’ mp_tac) >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘EI lfdn’, ‘srelabel M’, ‘s0’, ‘n2w lfdn’, ‘c’, ‘k'’, ‘n + i’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘l’, ‘c’, ‘k’, ‘n’] round_queued)
  >> simp[] >> strip_tac
  >- (qexists_tac ‘SUC (n + i)’ >> simp[])
  >> ‘0 < nacc (n2w lfdn) (SAg M (EI lfdn) s0 (i + n))’
       by (gvs[nacc_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >> metis_tac[])
  >> qpat_x_assum ‘∀m. m < k ⇒ _’ (qspec_then ‘k''’ mp_tac) >> impl_tac >- fs[]
  >> disch_then (qspec_then ‘SUC (i + n)’ mp_tac) >> fs[] >> strip_tac
  >> qexists_tac ‘N’ >> fs[]
QED
