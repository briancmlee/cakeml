(*
  D26 at the M4 level: read_soon_s, read_soon_eof_s and accept_soon_s on
  the live interest list (asyncM4LiveInterest), for async-spike's echo
  layer.  The proofs are those of asyncM4ReadSoon / ReadSoonEof /
  AcceptSoon with interest_accepted replaced by live_accepted, whose extra
  hypothesis (no read of the fd has returned end-of-file) is:
   - read_soon_live: a premise (as read_soon_eof_s already had);
   - read_soon_eof_live: read_soon_eof_s's own premise;
   - accept_soon_live: a premise on the listener (the echo never reads it).
  The rounds n .. n + 3 read nothing new of c, so its end-of-file status
  carries from round n.

  MAIN: read_soon_live, read_soon_eof_live, accept_soon_live.
*)
Theory asyncM4LiveSoon
Ancestors
  asyncM4LiveAcc asyncM4ReadSoon asyncM4ReadSoonEof asyncM4AcceptSoon asyncM4LiveProg
  asyncM4LiveInterest asyncM4EchoRunOk asyncM4GTrans asyncM4GRounds asyncM4SockInv
  asyncM4SockModel asyncM4Relabel asyncM4RelabelDist asyncM4Loop asyncM3World
  ffiSpikeSocketFFI asyncM4LiveWorld asyncM4Sched asyncServer asyncServerSafety asyncTranscript asyncProgress
Libs
  preamble

Overload LV = “λlfdn. asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel (server lfdn)))”

Theorem read_soon_live:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SP lfdn (LV lfdn) s0 n)) ∧
  ALOOKUP (gstate (LV lfdn) (EM lfdn) s0 n).conns c = SOME cn ∧ cn.incoming ≠ [] ∧
  (∀k. ¬MEM (Read c k, Got (SOME [])) (SP lfdn (LV lfdn) s0 n)) ⇒
  ∃i. i ≤ 3 ∧ reads_c c (SA lfdn (LV lfdn) s0 (n + i))
Proof
  rpt strip_tac >> CCONTR_TAC
  >> ‘∀i. i ≤ 3 ⇒ ¬reads_c c (SA lfdn (LV lfdn) s0 (n + i))’ by metis_tac[]
  >> qpat_x_assum ‘¬∃i. _’ kall_tac
  >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* c's data stays unread, and no read of c is performed *)
  >> ‘∀d. d ≤ 3 ⇒
        ∃cn'. ALOOKUP (gstate (LV lfdn) (EM lfdn) s0 (n + d)).conns c = SOME cn' ∧
              cn'.incoming ≠ [] ∧
              ∀k r. MEM (Read c k, r) (SP lfdn (LV lfdn) s0 (n + d)) ⇒
                    MEM (Read c k, r) (SP lfdn (LV lfdn) s0 n)’
       by (rpt strip_tac
           >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] quiet_rounds_s)
           >> impl_tac >- simp[] >> disch_then (qspecl_then [‘d’, ‘cn’] mp_tac)
           >> impl_tac >- simp[]
           >> strip_tac >> qexists_tac ‘cn'’ >> simp[] >> strip_tac >> gvs[])
  (* so the model server sees c readable in snapshots n .. n + 2 *)
  >> ‘∀j. n ≤ j ∧ j < n + 3 ⇒
          Readable (w2n c) ∈ (EL j (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> conj_tac
           >- (‘n + (SUC j − n) = SUC j’ by simp[]
               >> qpat_x_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘SUC j − n’ mp_tac) >> simp[]
               >> strip_tac >> simp[is_ready_def])
           >> irule live_accepted >> simp[] >> reverse conj_tac
           >- (disj2_tac >> irule wacc_prefix
               >> qexists_tac ‘SP lfdn (LV lfdn) s0 n’ >> simp[]
               >> ‘j = n + (j − n)’ by simp[] >> pop_assum SUBST1_TAC >> simp[gperf_prefix])
           (* no read of c returned end-of-file: rounds n .. j read nothing new of c *)
           >> gen_tac >> strip_tac
           >> qpat_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘j − n’ mp_tac) >> impl_tac >- simp[]
           >> ‘n + (j − n) = j’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac
           >> first_x_assum drule >> strip_tac >> gvs[])
  (* c's handler, inside the server, started at some round a ≤ n *)
  >> qspecl_then [‘MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))’] mp_tac
       (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] server_handler_view)
  >> impl_tac
  >- (simp[echo_fresh] >> conj_tac >- (irule prompt_ghist >> simp[])
      >> qspecl_then [‘s0’, ‘lfdn’, ‘LV lfdn’, ‘n + 3’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’] accepted_TS)
      >> impl_tac >- simp[] >> disch_then SUBST1_TAC
      >> ‘MEM c (wacc (SP lfdn (LV lfdn) s0 (n + 3)))’
           suffices_by (simp[MEM_MAP] >> metis_tac[])
      >> irule wacc_prefix >> qexists_tac ‘SP lfdn (LV lfdn) s0 n’ >> simp[gperf_prefix])
  >> strip_tac
  >> ‘∀k. k ≤ n + 3 ⇒ TAKE k (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))) =
                       MAP sfs (ghist (LV lfdn) (EM lfdn) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> ‘a ≤ n’
       by (qpat_x_assum ‘∀m. m ≤ LENGTH _ ∧ _ ⇒ a ≤ m’ (qspec_then ‘n’ mp_tac) >> simp[]
           >> qspecl_then [‘s0’, ‘lfdn’, ‘LV lfdn’, ‘n’] mp_tac
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
      >> qspecl_then [‘s0’, ‘lfdn’, ‘LV lfdn’, ‘n + 3’, ‘w2n (c : word64)’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’, ‘fd’] TS_eof)
      >> simp[] >> strip_tac
      >> qpat_x_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘3’ mp_tac) >> simp[] >> strip_tac
      >> strip_tac >> qpat_x_assum ‘∀k r. MEM _ _ ⇒ _’ drule >> strip_tac
      >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘c’, ‘k’] mp_tac
           (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘c’, ‘k’] grounds_eof)
      >> impl_tac >- simp[] >> disch_then (qspec_then ‘n’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac >> gvs[])
  (* so the server's reads of c grew in rounds n + 1 .. n + 3 *)
  >> strip_tac >> ‘LENGTH g + a = n + 3’ by gvs[]
  >> qpat_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a’ mp_tac)
  >> qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a + 3’ mp_tac)
  >> simp[] >> rpt strip_tac
  >> ‘nreads (w2n c) (server lfdn
        (TAKE n (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))))).actions <
      nreads (w2n c) (server lfdn
        (TAKE (n + 3) (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))))).actions’
       by (simp[] >> ‘n − a + 3 = n + 3 − a’ by simp[] >> gvs[])
  >> qspecl_then [‘3’] mp_tac
       (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))’] nreads_step)
  >> impl_tac >- simp[] >> strip_tac
  (* a read of the model server is a read of the socket program *)
  >> ‘reads_c c (SA lfdn (LV lfdn) s0 k)’
       by (gvs[reads_c_def, gacts_def, new_actions_relabel, MEM_MAP]
           >> qexists_tac ‘bufsz’ >> qexists_tac ‘Read (w2n c)’ >> simp[sfa_def])
  >> qpat_x_assum ‘∀i. i ≤ 3 ⇒ ¬reads_c _ _’ (qspec_then ‘k − n’ mp_tac) >> simp[]
QED

Theorem read_soon_eof_live:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SP lfdn (LV lfdn) s0 n)) ∧
  ALOOKUP (gstate (LV lfdn) (EM lfdn) s0 n).conns c = SOME cn ∧ cn.peer_closed ∧
  (∀k. ¬MEM (Read c k, Got (SOME [])) (SP lfdn (LV lfdn) s0 n)) ⇒
  ∃i. i ≤ 3 ∧ reads_c c (SA lfdn (LV lfdn) s0 (n + i))
Proof
  rpt strip_tac >> CCONTR_TAC
  >> ‘∀i. i ≤ 3 ⇒ ¬reads_c c (SA lfdn (LV lfdn) s0 (n + i))’ by metis_tac[]
  >> qpat_x_assum ‘¬∃i. _’ kall_tac
  >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* c's data stays unread, and no read of c is performed *)
  >> ‘∀d. d ≤ 3 ⇒
        ∃cn'. ALOOKUP (gstate (LV lfdn) (EM lfdn) s0 (n + d)).conns c = SOME cn' ∧
              cn'.peer_closed ∧
              ∀k r. MEM (Read c k, r) (SP lfdn (LV lfdn) s0 (n + d)) ⇒
                    MEM (Read c k, r) (SP lfdn (LV lfdn) s0 n)’
       by (rpt strip_tac
           >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] quiet_rounds_s)
           >> impl_tac >- simp[] >> disch_then (qspecl_then [‘d’, ‘cn’] mp_tac)
           >> impl_tac >- simp[]
           >> strip_tac >> qexists_tac ‘cn'’ >> simp[]
           >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] closed_rounds_s)
           >> simp[] >> disch_then (qspec_then ‘d’ strip_assume_tac)
           >> fs[] >> gvs[])
  (* so the model server sees c readable in snapshots n .. n + 2 *)
  >> ‘∀j. n ≤ j ∧ j < n + 3 ⇒
          Readable (w2n c) ∈ (EL j (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> conj_tac
           >- (‘n + (SUC j − n) = SUC j’ by simp[]
               >> qpat_x_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘SUC j − n’ mp_tac) >> simp[]
               >> strip_tac >> simp[is_ready_def])
           >> irule live_accepted >> simp[] >> reverse conj_tac
           >- (disj2_tac >> irule wacc_prefix
               >> qexists_tac ‘SP lfdn (LV lfdn) s0 n’ >> simp[]
               >> ‘j = n + (j − n)’ by simp[] >> pop_assum SUBST1_TAC >> simp[gperf_prefix])
           (* no read of c returned end-of-file: rounds n .. j read nothing new of c *)
           >> gen_tac >> strip_tac
           >> qpat_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘j − n’ mp_tac) >> impl_tac >- simp[]
           >> ‘n + (j − n) = j’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac
           >> first_x_assum drule >> strip_tac >> gvs[])
  (* c's handler, inside the server, started at some round a ≤ n *)
  >> qspecl_then [‘MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))’] mp_tac
       (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] server_handler_view)
  >> impl_tac
  >- (simp[echo_fresh] >> conj_tac >- (irule prompt_ghist >> simp[])
      >> qspecl_then [‘s0’, ‘lfdn’, ‘LV lfdn’, ‘n + 3’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’] accepted_TS)
      >> impl_tac >- simp[] >> disch_then SUBST1_TAC
      >> ‘MEM c (wacc (SP lfdn (LV lfdn) s0 (n + 3)))’
           suffices_by (simp[MEM_MAP] >> metis_tac[])
      >> irule wacc_prefix >> qexists_tac ‘SP lfdn (LV lfdn) s0 n’ >> simp[gperf_prefix])
  >> strip_tac
  >> ‘∀k. k ≤ n + 3 ⇒ TAKE k (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))) =
                       MAP sfs (ghist (LV lfdn) (EM lfdn) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> ‘a ≤ n’
       by (qpat_x_assum ‘∀m. m ≤ LENGTH _ ∧ _ ⇒ a ≤ m’ (qspec_then ‘n’ mp_tac) >> simp[]
           >> qspecl_then [‘s0’, ‘lfdn’, ‘LV lfdn’, ‘n’] mp_tac
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
      (* it has not seen end-of-file: no such read happened before round n *)
      >> qpat_x_assum ‘FILTER _ _ = trans (handler _) g’ (SUBST1_TAC o GSYM)
      >> simp[MEM_FILTER] >> strip_tac
      >> qspecl_then [‘s0’, ‘lfdn’, ‘LV lfdn’, ‘n + 3’, ‘w2n (c : word64)’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’, ‘fd’] TS_eof)
      >> simp[] >> strip_tac
      >> qpat_x_assum ‘∀d. d ≤ 3 ⇒ _’ (qspec_then ‘3’ mp_tac) >> simp[] >> strip_tac
      >> strip_tac >> qpat_x_assum ‘∀k r. MEM _ _ ⇒ _’ drule >> metis_tac[])
  (* so the server's reads of c grew in rounds n + 1 .. n + 3 *)
  >> strip_tac >> ‘LENGTH g + a = n + 3’ by gvs[]
  >> qpat_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a’ mp_tac)
  >> qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a + 3’ mp_tac)
  >> simp[] >> rpt strip_tac
  >> ‘nreads (w2n c) (server lfdn
        (TAKE n (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))))).actions <
      nreads (w2n c) (server lfdn
        (TAKE (n + 3) (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))))).actions’
       by (simp[] >> ‘n − a + 3 = n + 3 − a’ by simp[] >> gvs[])
  >> qspecl_then [‘3’] mp_tac
       (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 3))’] nreads_step)
  >> impl_tac >- simp[] >> strip_tac
  (* a read of the model server is a read of the socket program *)
  >> ‘reads_c c (SA lfdn (LV lfdn) s0 k)’
       by (gvs[reads_c_def, gacts_def, new_actions_relabel, MEM_MAP]
           >> qexists_tac ‘bufsz’ >> qexists_tac ‘Read (w2n c)’ >> simp[sfa_def])
  >> qpat_x_assum ‘∀i. i ≤ 3 ⇒ ¬reads_c _ _’ (qspec_then ‘k − n’ mp_tac) >> simp[]
QED

Theorem accept_soon_live:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  (∀j. n < j ∧ j ≤ n + 2 ⇒
       is_ready (gstate (LV lfdn) (EM lfdn) s0 j) (n2w lfdn)) ∧
  (∀j k. ¬MEM (Read (n2w lfdn) k, Got (SOME [])) (SP lfdn (LV lfdn) s0 j)) ⇒
  ∃i. 1 ≤ i ∧ i ≤ 2 ∧
      MEM (asyncM3World$Accept (n2w lfdn)) (SA lfdn (LV lfdn) s0 (n + i))
Proof
  rpt strip_tac
  >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* the model server sees the listener readable in snapshots n, n + 1 *)
  >> ‘∀j. n ≤ j ∧ j < n + 2 ⇒
          Readable lfdn ∈ (EL j (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 2)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> qexists_tac ‘n2w lfdn’ >> simp[]
           (* the listener is in the live interest list: it is never read *)
           >> irule live_accepted >> simp[])
  >> qspecl_then [‘MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 2))’, ‘n’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’] server_accept_progress)
  >> impl_tac >- simp[prompt_ghist]
  >> ‘∀k. k ≤ n + 2 ⇒ TAKE k (MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 2))) =
                       MAP sfs (ghist (LV lfdn) (EM lfdn) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> strip_tac
  >> qspecl_then [‘2’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (LV lfdn) (EM lfdn) s0 (n + 2))’] naccepts_step)
  >> impl_tac >- simp[] >> strip_tac
  (* an accept of the model server is an accept of the socket program *)
  >> qexists_tac ‘k − n’ >> simp[]
  >> gvs[gacts_def, new_actions_relabel, MEM_MAP]
  >> qexists_tac ‘Accept lfdn’ >> simp[sfa_def]
QED
