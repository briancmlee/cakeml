(*
  The echo server reads every ready connection it still serves: a
  generalisation of read_soon_s (asyncM4ReadSoon) from "unread data" to
  "ready" (unread data, or the peer closed), for a connection whose EOF the
  server has not read yet.  Quiescence needs it: an unread EOF is the last
  thing a finished client leaves behind.

  MAIN: read_ready_soon_s.
*)
Theory asyncEchoReadySoon
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4Relabel
  asyncM4RelabelDist asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop
  asyncM4EchoRunOk asyncM4Sched asyncM4LiveProg asyncM4LiveWorld asyncM4ReadSoon
Libs
  preamble

(* A closed peer stays closed, round after round *)
Theorem round_closed[local]:
  grun_ok ifds m s0 ∧ ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ∧
  cn.peer_closed ⇒
  ∃cn'. ALOOKUP (gstate ifds m s0 (SUC n)).conns c = SOME cn' ∧ cn'.peer_closed
Proof
  strip_tac >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> drule_all sock_acts_conn >> disch_then (qspec_then ‘ARB’ strip_assume_tac)
  >> rename1 ‘ALOOKUP s'.conns c = SOME cn1’
  >> ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def]
  >> simp[gstate_SUC]
  >> qspecl_then [‘s'’, ‘cn1’] mp_tac (Q.GENL [‘s’, ‘cn’] tick_conn_s)
  >> simp[] >> strip_tac >> gvs[]
QED

Theorem closed_stays:
  grun_ok ifds m s0 ⇒
  ∀d cn. ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ∧ cn.peer_closed ⇒
         ∃cn'. ALOOKUP (gstate ifds m s0 (n + d)).conns c = SOME cn' ∧
               cn'.peer_closed
Proof
  strip_tac >> Induct >- simp[] >> rpt strip_tac
  >> first_x_assum drule_all >> strip_tac
  >> ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC
  >> irule round_closed >> simp[] >> metis_tac[]
QED

(* MAIN: on an accepted connection that is ready and whose EOF the server
   has not read, the server reads it in one of the next four rounds *)
Theorem read_ready_soon_s:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SP lfdn (EI lfdn) s0 n)) ∧
  ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c = SOME cn ∧
  ¬(cn.incoming = [] ∧ ¬cn.peer_closed) ∧
  (∀k. ¬MEM (Read c k, Got (SOME [])) (SP lfdn (EI lfdn) s0 n)) ⇒
  ∃i. i ≤ 3 ∧ reads_c c (SA lfdn (EI lfdn) s0 (n + i))
Proof
  rpt strip_tac >> CCONTR_TAC
  >> ‘∀i. i ≤ 3 ⇒ ¬reads_c c (SA lfdn (EI lfdn) s0 (n + i))’ by metis_tac[]
  >> qpat_x_assum ‘¬∃i. _’ kall_tac
  >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* c stays ready, and no read of c is performed *)
  >> ‘∀d. d ≤ 3 ⇒
        ∃cn'. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 (n + d)).conns c = SOME cn' ∧
              (cn'.incoming ≠ [] ∨ cn'.peer_closed) ∧
              ∀k r. MEM (Read c k, r) (SP lfdn (EI lfdn) s0 (n + d)) ⇒
                    MEM (Read c k, r) (SP lfdn (EI lfdn) s0 n)’
       by (rpt strip_tac
           >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] quiet_rounds_s)
           >> impl_tac >- simp[] >> disch_then (qspecl_then [‘d’, ‘cn’] mp_tac)
           >> impl_tac >- simp[]
           >> strip_tac >> qexists_tac ‘cn'’ >> simp[]
           >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] closed_stays)
           >> impl_tac >- simp[] >> disch_then (qspecl_then [‘d’, ‘cn’] mp_tac)
           >> rw[] >> gvs[] >> Cases_on ‘cn.incoming’ >> gvs[])
  (* so the model server sees c readable in snapshots n .. n + 2 *)
  >> ‘∀j. n ≤ j ∧ j < n + 3 ⇒
          Readable (w2n c) ∈ (EL j (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 3)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> conj_tac
           >- (‘n + (SUC j − n) = SUC j’ by simp[]
               >> qpat_x_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘SUC j − n’ mp_tac) >> simp[]
               >> strip_tac >> simp[is_ready_def])
           >> irule interest_accepted >> simp[] >> disj2_tac >> irule wacc_prefix
           >> qexists_tac ‘SP lfdn (EI lfdn) s0 n’ >> simp[]
           >> ‘j = n + (j − n)’ by simp[] >> pop_assum SUBST1_TAC >> simp[gperf_prefix])
  (* c's handler, inside the server, started at some round a ≤ n *)
  >> qspecl_then [‘MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 3))’] mp_tac
       (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] server_handler_view)
  >> impl_tac
  >- (simp[echo_fresh] >> conj_tac >- (irule prompt_ghist >> simp[])
      >> qspecl_then [‘s0’, ‘lfdn’, ‘EI lfdn’, ‘n + 3’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’] accepted_TS)
      >> impl_tac >- simp[] >> disch_then SUBST1_TAC
      >> ‘MEM c (wacc (SP lfdn (EI lfdn) s0 (n + 3)))’
           suffices_by (simp[MEM_MAP] >> metis_tac[])
      >> irule wacc_prefix >> qexists_tac ‘SP lfdn (EI lfdn) s0 n’ >> simp[gperf_prefix])
  >> strip_tac
  >> ‘∀k. k ≤ n + 3 ⇒ TAKE k (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 3))) =
                       MAP sfs (ghist (EI lfdn) (EM lfdn) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> ‘a ≤ n’
       by (qpat_x_assum ‘∀m. m ≤ LENGTH _ ∧ _ ⇒ a ≤ m’ (qspec_then ‘n’ mp_tac) >> simp[]
           >> qspecl_then [‘s0’, ‘lfdn’, ‘EI lfdn’, ‘n’] mp_tac
                (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’] accepted_TS)
           >> impl_tac >- simp[] >> disch_then SUBST1_TAC
           >> simp[MEM_MAP] >> metis_tac[])
  (* by handler_progress, the handler reads c in rounds n + 1 .. n + 3 *)
  >> qspecl_then [‘g’, ‘n − a’] mp_tac
       (Q.INST [‘fd’ |-> ‘w2n (c : word64)’] handler_progress)
  >> impl_tac
  >- (rpt conj_tac >- simp[] >- gvs[]
      >- (rpt strip_tac >> ‘j < LENGTH g’ by gvs[]
          >> qpat_x_assum ‘∀i. i < LENGTH g ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[]
          >> disch_then SUBST1_TAC
          >> qpat_x_assum ‘∀j. n ≤ j ∧ _ ⇒ _’ (qspec_then ‘a + j’ mp_tac) >> simp[])
      (* it has not seen end-of-file: c still has unread data *)
      >> qpat_x_assum ‘FILTER _ _ = trans (handler _) g’ (SUBST1_TAC o GSYM)
      >> simp[MEM_FILTER] >> strip_tac
      >> qspecl_then [‘s0’, ‘lfdn’, ‘EI lfdn’, ‘n + 3’, ‘w2n (c : word64)’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’, ‘fd’] TS_eof)
      >> simp[] >> strip_tac
      >> qpat_x_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘3’ mp_tac) >> simp[] >> strip_tac
      >> strip_tac >> qpat_x_assum ‘∀k r. MEM _ _ ⇒ _’ drule >> strip_tac
      >> metis_tac[])
  (* so the server's reads of c grew in rounds n + 1 .. n + 3 *)
  >> strip_tac >> ‘LENGTH g + a = n + 3’ by gvs[]
  >> qpat_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a’ mp_tac)
  >> qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a + 3’ mp_tac)
  >> simp[] >> rpt strip_tac
  >> ‘nreads (w2n c) (server lfdn
        (TAKE n (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 3))))).actions <
      nreads (w2n c) (server lfdn
        (TAKE (n + 3) (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 3))))).actions’
       by (simp[] >> ‘n − a + 3 = n + 3 − a’ by simp[] >> gvs[])
  >> qspecl_then [‘3’] mp_tac
       (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 3))’] nreads_step)
  >> impl_tac >- simp[] >> strip_tac
  (* a read of the model server is a read of the socket program *)
  >> ‘reads_c c (SA lfdn (EI lfdn) s0 k)’
       by (gvs[reads_c_def, gacts_def, new_actions_relabel, MEM_MAP]
           >> qexists_tac ‘bufsz’ >> qexists_tac ‘Read (w2n c)’ >> simp[sfa_def])
  >> qpat_x_assum ‘∀i. i ≤ 3 ⇒ ¬reads_c _ _’ (qspec_then ‘k − n’ mp_tac) >> simp[]
QED
