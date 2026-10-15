(*
  The core of liveness, at the socket level: the echo server reads an
  accepted connection with unread data within four rounds (read_soon_s),
  and accepts within three rounds while connections are pending
  (accept_soon_s, in asyncM4AcceptSoon).

  The argument is the model's (asyncLiveness), transported to the event
  loop's run in the socket world: if c is not read, its data stays unread,
  so c is reported readable (it is in the interest list, asyncM4Loop), and
  by the program-level progress theorem (handler_progress, via
  server_handler_view) the server reads it; contradiction.
*)
Theory asyncM4ReadSoon
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4Relabel
  asyncM4RelabelDist asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop
  asyncM4EchoRunOk asyncM4Sched asyncM4LiveProg asyncM4LiveWorld
Libs
  preamble

(* ------------------------------------------------------------------------
   Helpers
   ------------------------------------------------------------------------ *)

Theorem gperf_prefix:
  ∀d. gperf ifds m s0 n ≼ gperf ifds m s0 (n + d)
Proof
  Induct >> simp[]
  >> ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC
  >> simp[gperf_SUC] >> irule IS_PREFIX_TRANS
  >> qexists_tac ‘gperf ifds m s0 (n + d)’ >> simp[]
QED

Theorem wacc_prefix:
  p ≼ p' ∧ MEM c (wacc p) ⇒ MEM c (wacc p')
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* The connections the model server has accepted are the ones handed out *)
Theorem accepted_TS:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  accepted (TS lfdn ifds s0 n) = MAP w2n (wacc (SP lfdn ifds s0 n))
Proof
  strip_tac >> mp_tac echo_sinv >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule echo_trans_split >> strip_tac >>
  drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
  simp[accepted_NONE]
QED

Theorem sfr_Eof:
  sfr r = Eof ⇔ r = Got (SOME [])
Proof
  Cases_on ‘r’ >> TRY (rename1 ‘Accepted o'’ >> Cases_on ‘o'’)
  >> TRY (rename1 ‘Got o'’ >> Cases_on ‘o'’) >> rw[sfr_def]
QED

(* An end-of-file the model server saw was returned by the socket world *)
Theorem TS_eof:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM (Read fd, SOME Eof) (TS lfdn ifds s0 n) ⇒
  ∃k. MEM (Read (n2w fd) k, Got (SOME [])) (SP lfdn ifds s0 n)
Proof
  strip_tac >> mp_tac echo_sinv >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule echo_trans_split >> strip_tac >>
  drule TREL_NONE >> strip_tac >> gvs[EVERY_MEM]
  >- (‘MEM (sfa (Read fd), SOME Eof) (MAP (λ(a,r). (sfa a, r)) tt1)’
        by (simp[MEM_MAP] >> qexists_tac ‘(Read fd, SOME Eof)’ >> simp[])
      >> pop_assum mp_tac >> qpat_x_assum ‘MAP _ tt1 = _’ (fn th => REWRITE_TAC[th])
      >> simp[MEM_MAP, EXISTS_PROD, sfa_def, sfr_Eof] >> metis_tac[])
  >> first_x_assum drule >> simp[]
QED

(* If a computation's reads of fd grew between rounds i and i + d, it
   emitted a read of fd in one of the rounds i+1 .. i+d *)
Theorem nreads_step:
  ∀d. nreads fd (server lfd (TAKE i h)).actions <
      nreads fd (server lfd (TAKE (i + d) h)).actions ⇒
      ∃k. i < k ∧ k ≤ i + d ∧
          MEM (Read fd) (new_actions (log_of (server lfd)) (TAKE k h))
Proof
  Induct >- simp[] >> rpt strip_tac
  >> Cases_on ‘nreads fd (server lfd (TAKE i h)).actions <
               nreads fd (server lfd (TAKE (i + d) h)).actions’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> simp[])
  >> qexists_tac ‘i + SUC d’ >> simp[]
  >> ‘i + SUC d ≤ LENGTH h’
       by (CCONTR_TAC
           >> ‘TAKE (i + SUC d) h = h ∧ TAKE (i + d) h = h’ by simp[TAKE_LENGTH_TOO_LONG]
           >> gvs[])
  >> ‘TAKE (i + SUC d) h = TAKE (i + d) h ++ [EL (i + d) h]’
       by (‘i + SUC d = SUC (i + d)’ by simp[] >> pop_assum SUBST1_TAC
           >> simp[GSYM SNOC_EL_TAKE, SNOC_APPEND])
  >> pop_assum SUBST_ALL_TAC
  >> ‘(server lfd (TAKE (i + d) h ++ [EL (i + d) h])).actions =
      (server lfd (TAKE (i + d) h)).actions ++
      new_actions (log_of (server lfd)) (TAKE (i + d) h ++ [EL (i + d) h])’
       by (qspecl_then [‘log_of (server lfd)’, ‘TAKE (i + d) h’, ‘EL (i + d) h’] mp_tac
             (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
           >> simp[log_of_def, wf_SNOC_actions, wf_server])
  >> gvs[nreads_def, FILTER_APPEND_DISTRIB] >> CCONTR_TAC
  >> ‘FILTER (λa. a = Read fd)
        (new_actions (log_of (server lfd)) (TAKE (i + d) h ++ [EL (i + d) h])) = []’
       by simp[FILTER_EQ_NIL, EVERY_MEM]
  >> gvs[]
QED

(* ------------------------------------------------------------------------
   Reads
   ------------------------------------------------------------------------ *)

(* The program of EchoSpec: the listener lfdn, polled with every connection
   handed out (asyncM4Loop) *)
Overload EI = “λlfdn. interest [n2w lfdn : word64]”
Overload EM = “λlfdn. srelabel (server lfdn)”

(* MAIN: on an accepted connection with unread data, the server reads it in
   one of the next four rounds (n .. n + 3) *)
Theorem read_soon_s:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SP lfdn (EI lfdn) s0 n)) ∧
  ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 n).conns c = SOME cn ∧ cn.incoming ≠ [] ⇒
  ∃i. i ≤ 3 ∧ reads_c c (SA lfdn (EI lfdn) s0 (n + i))
Proof
  rpt strip_tac >> CCONTR_TAC
  >> ‘∀i. i ≤ 3 ⇒ ¬reads_c c (SA lfdn (EI lfdn) s0 (n + i))’ by metis_tac[]
  >> qpat_x_assum ‘¬∃i. _’ kall_tac
  >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* c's data stays unread, and no read of c is performed *)
  >> ‘∀d. d ≤ 3 ⇒
        ∃cn'. ALOOKUP (gstate (EI lfdn) (EM lfdn) s0 (n + d)).conns c = SOME cn' ∧
              cn'.incoming ≠ [] ∧
              ∀k r. MEM (Read c k, r) (SP lfdn (EI lfdn) s0 (n + d)) ⇒
                    MEM (Read c k, r) (SP lfdn (EI lfdn) s0 n)’
       by (rpt strip_tac
           >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] quiet_rounds_s)
           >> impl_tac >- simp[] >> disch_then (qspecl_then [‘d’, ‘cn’] mp_tac)
           >> impl_tac >- simp[]
           >> strip_tac >> qexists_tac ‘cn'’ >> simp[] >> strip_tac >> gvs[])
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
      >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘c’, ‘k’] mp_tac
           (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘c’, ‘k’] grounds_eof)
      >> impl_tac >- simp[] >> disch_then (qspec_then ‘n’ mp_tac)
      >> impl_tac >- simp[] >> strip_tac >> gvs[])
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
