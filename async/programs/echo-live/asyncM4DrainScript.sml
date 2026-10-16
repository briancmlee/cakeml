(*
  Draining a connection, with bounded reads, at the socket level.

  The server reads at most bufsz bytes at a time.  So "everything sent on c
  by round n is eventually read" is proved with a measure: while some of it
  is unread, c has unread data, so within four rounds the server reads c
  (read_soon_s), and the bytes read from c grow (drain_step).  Then
  everything read is written back in the next round (m4-safety's
  echo_rounds_written_read), which gives EchoSpec's liveness for accepted
  connections (accepted_live).
*)
Theory asyncM4Drain
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec asyncM3World
  asyncM4GRounds asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  asyncM4SockInv asyncM4GTrans asyncM4Loop asyncM4EchoRunOk asyncM4EchoSafe
  asyncM4Sched asyncM4Account asyncM4LiveProg asyncM4LiveWorld asyncM4ReadSoon
Libs
  preamble

(* ------------------------------------------------------------------------
   A read of a connection with unread data reads something
   ------------------------------------------------------------------------ *)

Theorem sock_acts_read_nonempty:
  ∀acts s rs evs s' cn.
    sock_acts s acts = SOME (rs, evs, s') ∧ reads_c c acts ∧
    ALOOKUP s.conns c = SOME cn ∧ cn.incoming ≠ [] ⇒
    pread_all c (ZIP (acts, rs)) ≠ []
Proof
  Induct >> rw[sock_acts_def, reads_c_def] >> gvs[AllCaseEqs()]
  >- (gvs[sock_do_def, sock_read_def, AllCaseEqs(), pread_def]
      >> Cases_on ‘cn.incoming’ >> gvs[] >> Cases_on ‘k’ >> gvs[])
  >> drule_all sock_do_conn >> strip_tac
  >> Cases_on ‘∃k. h = Read c k’
  >- (gvs[sock_do_def, sock_read_def, AllCaseEqs(), pread_def]
      >> Cases_on ‘cn.incoming’ >> gvs[] >> Cases_on ‘k'’ >> gvs[])
  >> gvs[] >> first_x_assum drule >> disch_then (qspec_then ‘cn'’ mp_tac)
  >> simp[reads_c_def] >> impl_tac >- metis_tac[]
  >> simp[]
QED

(* ------------------------------------------------------------------------
   Prefixes
   ------------------------------------------------------------------------ *)

Theorem arrivals_upto_prefix:
  ∀n l d. arrivals_upto n l ≼ arrivals_upto (n + d) l
Proof
  Induct >- simp[arrivals_upto_def] >> rpt gen_tac
  >> ‘SUC n + d = SUC (n + d)’ by simp[] >> ASM_REWRITE_TAC[arrivals_upto_def]
  >> CASE_TAC >> simp[]
QED

Theorem sent_upto_prefix:
  sent_upto c n s0 ≼ sent_upto c (n + d) s0
Proof
  simp[sent_upto_sent_of, sent_of_def]
  >> qspecl_then [‘n’, ‘s0.sched’, ‘d’] mp_tac arrivals_upto_prefix
  >> rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem pread_all_prefix:
  p ≼ p' ⇒ pread_all c p ≼ pread_all c p'
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem prefix_by_length:
  a ≼ x ∧ b ≼ x ∧ LENGTH a ≤ LENGTH b ⇒ a ≼ b
Proof
  rw[] >> qspecl_then [‘x’, ‘a’, ‘b’] mp_tac prefixes_is_prefix_total
  >> rw[] >> simp[] >> imp_res_tac IS_PREFIX_LENGTH
  >> ‘LENGTH b = LENGTH a’ by simp[]
  >> ‘b = a’ by metis_tac[IS_PREFIX_LENGTH_ANTI] >> simp[]
QED

(* ------------------------------------------------------------------------
   Draining
   ------------------------------------------------------------------------ *)

Overload RD = “λlfdn s0 c k. pread_all c (SP lfdn (EI lfdn) s0 k)”

Theorem least_round[local]:
  P ((k:num) + i) ⇒ ∃j. k ≤ j ∧ j ≤ k + i ∧ P j ∧ ∀l. k ≤ l ∧ l < j ⇒ ¬P l
Proof
  strip_tac
  >> qspec_then ‘λx. P (k + x)’ mp_tac arithmeticTheory.WOP >> simp[]
  >> impl_tac >- metis_tac[] >> strip_tac
  >> ‘n ≤ i’ by (CCONTR_TAC >> gvs[NOT_LESS_EQUAL] >> res_tac)
  >> qexists_tac ‘k + n’ >> simp[] >> rpt strip_tac
  >> first_x_assum (qspec_then ‘l − k’ mp_tac) >> simp[]
QED

(* While some of what was sent on an accepted c by round n is unread, the
   bytes read from c grow within four rounds *)
Theorem drain_step:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  MEM c (wacc (SP lfdn (EI lfdn) s0 k)) ∧
  tgt ≼ sent_upto c k s0 ∧ ¬(tgt ≼ RD lfdn s0 c k) ⇒
  ∃k'. k < k' ∧ k' ≤ k + 4 ∧ LENGTH (RD lfdn s0 c k) < LENGTH (RD lfdn s0 c k')
Proof
  rpt strip_tac >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* c has unread data *)
  >> qspecl_then [‘s0’, ‘EI lfdn’, ‘EM lfdn’, ‘c’] mp_tac
       (Q.GENL [‘s0’, ‘ifds’, ‘m’, ‘c’] grounds_acct)
  >> impl_tac >- simp[] >> disch_then (qspec_then ‘k’ mp_tac)
  >> simp[acct_def] >> CASE_TAC >> strip_tac >> gvs[]
  >> ‘x.incoming ≠ []’ by (strip_tac >> gvs[])
  (* so the server reads c in some round j ≤ k + 3; take the first *)
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘k’, ‘x’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’, ‘cn’] read_soon_s)
  >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘λj. reads_c c (SA lfdn (EI lfdn) s0 j)’, ‘k’, ‘i’] mp_tac
       (Q.GENL [‘P’, ‘k’, ‘i’] least_round)
  >> simp[] >> strip_tac
  (* until then c's data stays unread *)
  >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘k’, ‘c’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] quiet_rounds_s)
  >> impl_tac >- simp[] >> disch_then (qspecl_then [‘j − k’, ‘x’] mp_tac)
  >> impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[])
  >> strip_tac
  >> ‘k + (j − k) = j’ by simp[] >> gvs[]
  >> ‘cn'.incoming ≠ []’ by (strip_tac >> gvs[])
  (* so that read reads something *)
  >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘j’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’] grun_ok_sock_acts)
  >> simp[] >> strip_tac
  >> drule_all sock_acts_read_nonempty >> strip_tac
  >> qexists_tac ‘SUC j’ >> simp[gperf_SUC]
  >> ‘RD lfdn s0 c k ≼ RD lfdn s0 c j’
       by (irule pread_all_prefix >> ‘j = k + (j − k)’ by simp[]
           >> pop_assum SUBST1_TAC >> simp[gperf_prefix])
  >> imp_res_tac IS_PREFIX_LENGTH
  >> Cases_on ‘pread_all c (ZIP (gacts (EI lfdn) (EM lfdn) s0 j,
                                 gres (EI lfdn) (EM lfdn) s0 j))’
  >> gvs[]
QED

(* What has been read from c is a prefix of what was sent on it *)
Theorem RD_sent:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ⇒
  RD lfdn s0 c k ≼ sent_upto c k s0
Proof
  strip_tac >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> qspecl_then [‘s0’, ‘EI lfdn’, ‘EM lfdn’, ‘c’] mp_tac
       (Q.GENL [‘s0’, ‘ifds’, ‘m’, ‘c’] grounds_acct)
  >> impl_tac >- simp[] >> disch_then (qspec_then ‘k’ mp_tac)
  >> simp[acct_def] >> CASE_TAC >> simp[]
QED

(* MAIN: draining.  On an accepted connection, everything sent by a given
   round is eventually read *)
Theorem drain:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ⇒
  ∀m k. MEM c (wacc (SP lfdn (EI lfdn) s0 k)) ∧ tgt ≼ sent_upto c k s0 ∧
        LENGTH tgt ≤ LENGTH (RD lfdn s0 c k) + m ⇒
        ∃N. k ≤ N ∧ tgt ≼ RD lfdn s0 c N
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >> qexists_tac ‘k’ >> simp[]
      >> qspecl_then [‘tgt’, ‘sent_upto c k s0’, ‘RD lfdn s0 c k’] mp_tac
           (Q.GENL [‘a’, ‘x’, ‘b’] prefix_by_length)
      >> simp[RD_sent])
  >> rpt strip_tac
  >> Cases_on ‘tgt ≼ RD lfdn s0 c k’ >- (qexists_tac ‘k’ >> simp[])
  >> drule_all drain_step >> strip_tac
  >> first_x_assum (qspec_then ‘k'’ mp_tac) >> impl_tac
  >- (rpt conj_tac
      >- (irule wacc_prefix >> qexists_tac ‘SP lfdn (EI lfdn) s0 k’ >> simp[]
          >> ‘k' = k + (k' − k)’ by simp[] >> pop_assum SUBST1_TAC >> simp[gperf_prefix])
      >- (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c k s0’ >> simp[]
          >> ‘k' = k + (k' − k)’ by simp[] >> pop_assum SUBST1_TAC
          >> simp[sent_upto_prefix])
      >> simp[])
  >> strip_tac >> qexists_tac ‘N’ >> simp[]
QED

(* MAIN: liveness for accepted connections, on raw I/O events.  If c has
   been handed out by round n, everything sent on c by round n is written
   back to c in the events of some finite number of rounds. *)
Theorem accepted_live:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  MEM c (wacc (SP lfdn (EI lfdn) s0 n)) ⇒
  ∃N. sent_upto c n s0 ≼
      bytes_written_to c (FLAT (GENLIST (grounds_events (EI lfdn) (EM lfdn) s0) (SUC N)))
Proof
  strip_tac >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘sent_upto c n s0’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘tgt’] drain)
  >> impl_tac >- simp[]
  >> disch_then (qspecl_then [‘LENGTH (sent_upto c n s0)’, ‘n’] mp_tac)
  >> simp[] >> strip_tac >> qexists_tac ‘N’
  >> simp[echo_rounds_written_read, bytes_read_from_rounds]
QED
