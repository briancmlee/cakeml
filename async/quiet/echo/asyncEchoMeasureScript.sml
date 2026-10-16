(*
  The quiescence measure of the echo server's run (option C, design/33
  §2.5 (b)-(d)).

  For the polling run of EchoSpec's program (EI, EM) in a socket world
  that receives nothing more after round N (static), the measure of round
  n is
     the connections pending on the listener
   + for each connection whose EOF the server has not read (eofr):
       its unread bytes, plus 1 if its peer has closed.
  - It never grows after N (meas_mono), since only the server's accepts
    and reads change it.
  - It shrinks in every round that accepts a connection, reads bytes, or
    reads an EOF the server had not read (meas_step).
  - While it is positive, it shrinks within four rounds (meas_progress):
    a pending connection is accepted (accept_soon_s), and a ready
    connection is read (read_ready_soon_s).
  So it reaches 0 (meas_zero).

  MAIN: meas_mono, meas_progress, meas_zero.
*)
Theory asyncEchoMeasure
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  ffiSpikeSocketFFI ffiSpikeSocketFair asyncM3World asyncM4GRounds
  asyncM4GTrans asyncM4SockInv asyncM4Loop asyncM4EchoRunOk asyncM4Sched
  asyncM4Queue asyncM4LiveProg asyncM4LiveWorld asyncM4AcceptSoon
  asyncM4ReadSoon asyncStaticRounds asyncEchoReadySoon QuietSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   Within one round's actions
   ------------------------------------------------------------------------ *)

(* An accept of l with connections pending accepts one *)
Theorem sock_acts_accepts:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧ MEM (Accept l) acts ∧ lq l s ≠ [] ⇒
    0 < nacc_ok l (ZIP (acts, rs))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘sock_acts _ _ = _’ mp_tac >> simp[Once sock_acts_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> rename1 ‘sock_do s h = SOME (r, s1)’ >>
  REWRITE_TAC[ZIP] >> ONCE_REWRITE_TAC[counts_CONS] >>
  drule sock_do_counts >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  Cases_on ‘nacc_ok l [(h, r)]’ >> simp[] >>
  Cases_on ‘h = Accept l’
  >- gvs[sock_do_def, sock_accept_def, lq_def, AllCaseEqs(), nacc_ok_def] >>
  ‘MEM (Accept l) acts’ by gvs[] >>
  ‘lq l s1 ≠ []’ by (strip_tac >> gvs[]) >>
  first_x_assum (qspecl_then [‘s1’, ‘rs'’, ‘evs'’, ‘s'’] mp_tac) >> simp[]
QED

(* A read of a ready connection c reads bytes or its EOF *)
Theorem sock_acts_reads:
  ∀acts s rs evs s' cn.
    sock_acts s acts = SOME (rs, evs, s') ∧ MEM (Read c k) acts ∧
    ALOOKUP s.conns c = SOME cn ∧ ¬(cn.incoming = [] ∧ ¬cn.peer_closed) ⇒
    0 < rdbytes c (ZIP (acts, rs)) ∨
    ∃k'. MEM (Read c k', Got (SOME [])) (ZIP (acts, rs))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘sock_acts _ _ = _’ mp_tac >> simp[Once sock_acts_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> rename1 ‘sock_do s h = SOME (r, s1)’ >>
  REWRITE_TAC[ZIP] >> ONCE_REWRITE_TAC[counts_CONS] >>
  drule sock_do_counts >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  qpat_x_assum ‘∀c cn. ALOOKUP s.conns c = SOME cn ⇒ _’ drule >> strip_tac >>
  Cases_on ‘∃k'. h = Read c k'’
  >- (gvs[sock_do_def, sock_read_def, AllCaseEqs(), rdbytes_def] >>
      Cases_on ‘cn.incoming’ >> gvs[] >> metis_tac[]) >>
  Cases_on ‘rdbytes c [(h, r)]’ >> simp[] >>
  ‘MEM (Read c k) acts’
    by (qpat_x_assum ‘MEM (Read c k) (h :: acts)’ mp_tac >> rw[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [‘s1’, ‘rs'’, ‘evs'’, ‘s'’, ‘cn'’] mp_tac) >> simp[] >>
  impl_tac >- (Cases_on ‘cn.incoming’ >> Cases_on ‘cn'.incoming’ >> gvs[]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The measure
   ------------------------------------------------------------------------ *)

(* The server has read c's EOF in the first n rounds *)
Definition eofr_def:
  eofr lfdn s0 c n ⇔ ∃k. MEM (Read c k, Got (SOME [])) (SP lfdn (EI lfdn) s0 n)
End

(* What is left to read on c: its unread bytes, and its EOF *)
Definition cm_def:
  cm s c = case ALOOKUP s.conns c of
           | NONE => 0
           | SOME cn => LENGTH cn.incoming + (if cn.peer_closed then 1 else 0)
End

(* ... counted while the server has not read c's EOF *)
Definition cterm_def:
  cterm lfdn s0 n c =
    if eofr lfdn s0 c n then 0 else cm (gstate (EI lfdn) (EM lfdn) s0 n) c
End

(* The connections pending on the listener *)
Definition qlen_def:
  qlen lfdn s0 n = LENGTH (lq (n2w lfdn) (gstate (EI lfdn) (EM lfdn) s0 n))
End

(* The measure, over the connections ks *)
Definition meas_def:
  meas lfdn s0 ks n = qlen lfdn s0 n + SUM (MAP (cterm lfdn s0 n) ks)
End

Theorem SUM_MAP_LE[local]:
  ∀l. (∀x. MEM x l ⇒ f x ≤ g x) ⇒ SUM (MAP f l) ≤ SUM (MAP g l)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  ‘f h ≤ g h ∧ SUM (MAP f l) ≤ SUM (MAP g l)’ by simp[] >> simp[]
QED

Theorem SUM_MAP_LT[local]:
  ∀l. (∀x. MEM x l ⇒ f x ≤ g x) ∧ MEM y l ∧ f y < g y ⇒
      SUM (MAP f l) < SUM (MAP g l)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[]
  >- (‘SUM (MAP f l) ≤ SUM (MAP g l)’ by (irule SUM_MAP_LE >> simp[]) >> simp[])
  >> ‘f h ≤ g h ∧ SUM (MAP f l) < SUM (MAP g l)’ by (simp[] >> metis_tac[]) >> simp[]
QED

Theorem eofr_SUC:
  eofr lfdn s0 c (SUC n) ⇔
  eofr lfdn s0 c n ∨
  ∃k. MEM (Read c k, Got (SOME []))
          (ZIP (SA lfdn (EI lfdn) s0 n, gres (EI lfdn) (EM lfdn) s0 n))
Proof
  simp[eofr_def, gperf_SUC] >> metis_tac[]
QED

(* The run of the echo program has no misuse *)
Theorem echo_ok[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒ grun_ok (EI lfdn) (EM lfdn) s0
Proof
  strip_tac >> irule echo_grun_ok >> simp[]
QED

(* One static round: the queue shrinks by the accepts *)
Theorem qlen_step:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  next_step (gstate (EI lfdn) (EM lfdn) s0 n) = [] ⇒
  qlen lfdn s0 (SUC n) +
    nacc_ok (n2w lfdn) (ZIP (SA lfdn (EI lfdn) s0 n, gres (EI lfdn) (EM lfdn) s0 n)) =
  qlen lfdn s0 n
Proof
  strip_tac >> drule_all echo_ok >> strip_tac >>
  drule_all static_round >> simp[qlen_def]
QED

(* One static round: c's term does not grow, and shrinks if c is read *)
Theorem cterm_step:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  next_step (gstate (EI lfdn) (EM lfdn) s0 n) = [] ⇒
  cterm lfdn s0 (SUC n) c ≤ cterm lfdn s0 n c ∧
  (¬eofr lfdn s0 c n ∧
   (0 < rdbytes c (ZIP (SA lfdn (EI lfdn) s0 n, gres (EI lfdn) (EM lfdn) s0 n)) ∨
    ∃k. MEM (Read c k, Got (SOME []))
            (ZIP (SA lfdn (EI lfdn) s0 n, gres (EI lfdn) (EM lfdn) s0 n))) ⇒
   cterm lfdn s0 (SUC n) c < cterm lfdn s0 n c)
Proof
  strip_tac >> drule_all echo_ok >> strip_tac >>
  drule_all static_round >> disch_then (qspec_then ‘ARB’ strip_assume_tac) >>
  ‘∀k. MEM (Read c k, Got (SOME []))
           (ZIP (SA lfdn (EI lfdn) s0 n, gres (EI lfdn) (EM lfdn) s0 n)) ⇒
       ∃cn. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c = SOME cn ∧
            cn.peer_closed’
    by (rpt strip_tac >> drule grun_ok_sock_acts >>
        disch_then (qspec_then ‘n’ strip_assume_tac) >>
        ‘∃cn. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c = SOME cn’
          by (Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c’ >> simp[] >>
              drule_all sock_acts_eof >> strip_tac >>
              drule sock_acts_counts >> strip_tac >> res_tac >> gvs[]) >>
        drule_all sock_acts_conn >> metis_tac[]) >>
  simp[cterm_def, eofr_SUC] >>
  Cases_on ‘eofr lfdn s0 c n’ >> simp[] >>
  Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c’ >> simp[cm_def]
  >- (rw[] >> res_tac >> gvs[]) >>
  rename1 ‘_ = SOME cn’ >> first_x_assum drule >> strip_tac >> simp[] >>
  rw[] >> res_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   After the last arrival
   ------------------------------------------------------------------------ *)

(* The world receives nothing from round N on *)
Overload static_from = “λlfdn s0 N.
  ∀n. N ≤ n ⇒ next_step (gstate (EI lfdn) (EM lfdn) s0 n) = []”

(* MAIN: from N on, the queue and every connection's term only shrink *)
Theorem meas_mono:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ static_from lfdn s0 N ⇒
  ∀d n. N ≤ n ⇒
        qlen lfdn s0 (n + d) ≤ qlen lfdn s0 n ∧
        ∀c. cterm lfdn s0 (n + d) c ≤ cterm lfdn s0 n c
Proof
  strip_tac >> Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  ‘next_step (gstate (EI lfdn) (EM lfdn) s0 (n + d)) = []’ by simp[] >>
  ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  drule_all qlen_step >> strip_tac >>
  conj_tac
  >- (qpat_x_assum ‘_ + _ = _’ mp_tac >>
      qpat_x_assum ‘qlen _ _ (n + d) ≤ _’ mp_tac >> simp[]) >>
  gen_tac >> drule_all cterm_step >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem meas_le:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ static_from lfdn s0 N ∧
  N ≤ n ∧ n ≤ j ⇒
  meas lfdn s0 ks j ≤ meas lfdn s0 ks n
Proof
  strip_tac >> drule_all meas_mono >> disch_then (qspec_then ‘j − n’ mp_tac) >>
  simp[] >> strip_tac >> simp[meas_def] >>
  ‘SUM (MAP (cterm lfdn s0 j) ks) ≤ SUM (MAP (cterm lfdn s0 n) ks)’
    by (irule SUM_MAP_LE >> simp[]) >>
  simp[]
QED

(* The measure shrinks once the queue or one connection's term has *)
Theorem meas_lt:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ static_from lfdn s0 N ∧
  N ≤ n ∧ n ≤ j ∧
  (qlen lfdn s0 j < qlen lfdn s0 n ∨
   ∃c. MEM c ks ∧ cterm lfdn s0 j c < cterm lfdn s0 n c) ⇒
  meas lfdn s0 ks j < meas lfdn s0 ks n
Proof
  strip_tac >> drule_all meas_mono >> disch_then (qspec_then ‘j − n’ mp_tac) >>
  simp[] >> strip_tac >> simp[meas_def]
  >- (‘SUM (MAP (cterm lfdn s0 j) ks) ≤ SUM (MAP (cterm lfdn s0 n) ks)’
        by (irule SUM_MAP_LE >> simp[]) >> simp[])
  >> ‘SUM (MAP (cterm lfdn s0 j) ks) < SUM (MAP (cterm lfdn s0 n) ks)’
       by (irule SUM_MAP_LT >> simp[] >> metis_tac[]) >>
  simp[]
QED

(* A pending connection makes the listener ready *)
Theorem lq_ready[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ 0 < qlen lfdn s0 n ⇒
  is_ready (gstate (EI lfdn) (EM lfdn) s0 n) (n2w lfdn)
Proof
  strip_tac >> gvs[qlen_def, lq_def, is_ready_def, AllCaseEqs()] >>
  Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).listeners (n2w lfdn)’ >> gvs[] >>
  rename1 ‘SOME q’ >> Cases_on ‘q’ >> gvs[]
QED

(* MAIN: while the measure is positive, it shrinks within four rounds *)
Theorem meas_progress:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  static_from lfdn s0 N ∧ N ≤ n ∧ 0 < meas lfdn s0 ks n ⇒
  ∃j. n < j ∧ j ≤ n + 4 ∧ meas lfdn s0 ks j < meas lfdn s0 ks n
Proof
  strip_tac >> drule_all echo_ok >> strip_tac >>
  Cases_on ‘0 < qlen lfdn s0 n’
  (* a connection is pending: it is accepted within three rounds *)
  >- (Cases_on ‘∃j. n < j ∧ j ≤ n + 2 ∧ qlen lfdn s0 j = 0’
      >- (gvs[] >> qexists_tac ‘j’ >> simp[] >> irule meas_lt >> simp[] >>
          qexists_tac ‘N’ >> simp[])
      >> gvs[] >>
      qspecl_then [‘s0’, ‘lfdn’, ‘n’] mp_tac
        (Q.GENL [‘s0’, ‘lfdn’, ‘n’] accept_soon_s) >>
      impl_tac
      >- (simp[] >> rpt strip_tac >> irule lq_ready >> simp[] >>
          first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]) >>
      strip_tac >>
      qexists_tac ‘SUC (n + i)’ >> simp[] >> irule meas_lt >> simp[] >>
      conj_tac >- (qexists_tac ‘N’ >> simp[]) >> disj1_tac >>
      ‘next_step (gstate (EI lfdn) (EM lfdn) s0 (n + i)) = []’ by simp[] >>
      drule_all qlen_step >> strip_tac >>
      ‘0 < nacc_ok (n2w lfdn)
             (ZIP (SA lfdn (EI lfdn) s0 (n + i), gres (EI lfdn) (EM lfdn) s0 (n + i)))’
        by (drule grun_ok_sock_acts >> disch_then (qspec_then ‘n + i’ strip_assume_tac) >>
            drule sock_acts_accepts >> disch_then irule >> simp[] >>
            first_x_assum (qspec_then ‘n + i’ mp_tac) >> simp[qlen_def] >>
            Cases_on ‘lq (n2w lfdn) (gstate (EI lfdn) (EM lfdn) s0 (n + i))’ >> simp[]) >>
      drule_all meas_mono >> disch_then (qspec_then ‘i’ strip_assume_tac) >> gvs[])
  (* no connection is pending: some accepted connection is ready *)
  >> gvs[meas_def] >>
  ‘∃c. MEM c ks ∧ 0 < cterm lfdn s0 n c’
    by (CCONTR_TAC >> gvs[] >>
        ‘SUM (MAP (cterm lfdn s0 n) ks) = 0’ suffices_by simp[] >>
        simp[SUM_eq_0, MEM_MAP] >> metis_tac[NOT_ZERO_LT_ZERO]) >>
  ‘¬eofr lfdn s0 c n ∧
   ∃cn. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c = SOME cn ∧
        ¬(cn.incoming = [] ∧ ¬cn.peer_closed)’
    by (gvs[cterm_def, cm_def, AllCaseEqs()] >>
        Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c’ >> gvs[] >>
        Cases_on ‘eofr lfdn s0 c n’ >> gvs[] >> rename1 ‘SOME x’ >>
        Cases_on ‘x.peer_closed’ >> gvs[] >> strip_tac >> gvs[]) >>
  (* it was accepted: the queue is empty *)
  ‘MEM c (wacc (SP lfdn (EI lfdn) s0 n))’
    by (qspecl_then [‘s0’, ‘n2w lfdn’, ‘EI lfdn’, ‘EM lfdn’] mp_tac
          (Q.GENL [‘s0’, ‘lfd’, ‘ifds’, ‘m’] grounds_known) >>
        simp[] >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
        gvs[known_def, is_conn_def, qlen_def] >> first_x_assum (qspec_then ‘c’ mp_tac) >>
        simp[] >> Cases_on ‘lq (n2w lfdn) (gstate (EI lfdn) (EM lfdn) s0 n)’ >> gvs[]) >>
  qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘n’, ‘cn’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’, ‘cn’] read_ready_soon_s) >>
  impl_tac >- gvs[eofr_def] >> strip_tac >>
  Cases_on ‘cterm lfdn s0 (n + i) c < cterm lfdn s0 n c’
  >- (‘i ≠ 0’ by (strip_tac >> gvs[]) >>
      qexists_tac ‘n + i’ >> simp[] >>
      ‘meas lfdn s0 ks (n + i) < meas lfdn s0 ks n’ suffices_by simp[meas_def] >>
      irule meas_lt >> simp[] >> conj_tac >- (qexists_tac ‘N’ >> simp[]) >>
      qexists_tac ‘c’ >> gvs[])
  (* c is still ready in round n + i, and is read: its term shrinks *)
  >> qexists_tac ‘SUC (n + i)’ >> simp[] >>
  ‘meas lfdn s0 ks (SUC (n + i)) < meas lfdn s0 ks n’ suffices_by simp[meas_def] >>
  irule meas_lt >> simp[] >> conj_tac >- (qexists_tac ‘N’ >> simp[]) >>
  qexists_tac ‘c’ >> simp[] >>
  drule_all meas_mono >> disch_then (qspec_then ‘i’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘c’ assume_tac o CONJUNCT2) >>
  ‘cterm lfdn s0 (n + i) c = cterm lfdn s0 n c’ by gvs[] >>
  ‘next_step (gstate (EI lfdn) (EM lfdn) s0 (n + i)) = []’ by simp[] >>
  drule_all cterm_step >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
  ‘¬eofr lfdn s0 c (n + i) ∧
   ∃cn2. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 (n + i)).conns c = SOME cn2 ∧
         ¬(cn2.incoming = [] ∧ ¬cn2.peer_closed)’
    by (qpat_x_assum ‘cterm _ _ (n + i) _ = _’ mp_tac >>
        simp[cterm_def] >> rw[] >> gvs[] >>
        gvs[cm_def, AllCaseEqs()] >>
        Cases_on ‘ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 (n + i)).conns c’ >> gvs[] >>
        rw[] >> gvs[] >> Cases_on ‘cn.incoming’ >> gvs[] >> rw[] >> gvs[] >>
        Cases_on ‘cn'.peer_closed’ >> gvs[] >> Cases_on ‘cn.peer_closed’ >> gvs[]) >>
  ‘0 < rdbytes c (ZIP (SA lfdn (EI lfdn) s0 (n + i), gres (EI lfdn) (EM lfdn) s0 (n + i))) ∨
   ∃k. MEM (Read c k, Got (SOME []))
           (ZIP (SA lfdn (EI lfdn) s0 (n + i), gres (EI lfdn) (EM lfdn) s0 (n + i)))’
    by (drule grun_ok_sock_acts >> disch_then (qspec_then ‘n + i’ strip_assume_tac) >>
        gvs[reads_c_def] >> drule sock_acts_reads >> disch_then irule >>
        simp[] >> metis_tac[]) >>
  gvs[] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

(* MAIN: from any round after the last arrival, the measure reaches 0 *)
Theorem meas_zero:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  static_from lfdn s0 N ⇒
  ∀n. N ≤ n ⇒ ∃n0. n ≤ n0 ∧ meas lfdn s0 ks n0 = 0
Proof
  strip_tac >>
  ‘∀v n. meas lfdn s0 ks n = v ∧ N ≤ n ⇒ ∃n0. n ≤ n0 ∧ meas lfdn s0 ks n0 = 0’
    suffices_by metis_tac[] >>
  completeInduct_on ‘v’ >> rpt strip_tac >>
  Cases_on ‘v = 0’ >- (qexists_tac ‘n’ >> gvs[]) >>
  ‘0 < meas lfdn s0 ks n’ by simp[] >>
  drule_all meas_progress >> strip_tac >>
  first_x_assum (qspec_then ‘meas lfdn s0 ks j’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘n0’ >> simp[]
QED
