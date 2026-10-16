(*
  Liveness carried by the library, for the skeleton server_v over any
  vocabulary, inside any wrapper (design/34, the principled KV version).

  The loop runs a socket machine M.  For server_with, M = server_with hf;
  for the KV server, M = with_store δ s0 (server_v sockV kvh), whose store
  answers the handlers' queries.  The proofs are skeletonLive's and
  skeletonSock's, split in three:

   1. Any socket machine M (no vocabulary): the world's facts.
       - m_conn_accepted: if M keeps accepting (accepts_progress), every
         connection is eventually handed out (sw_conn_accepted, for M);
       - m_view_henv: if an accepted connection c is served by a "view"
         (a history g and a transcript function t with M's transcript on c
         equal to t of the prefixes of g), the socket world gives t its
         environment henv_t (sw_view_henv, for M and t).
   2. The per-handler obligation, through V: handler_live_v V hf out B is
      handler_live on the socket part (sproj V) of the handler's
      transcript.  (The handler's queries, if any, are answered in the next
      round: that is prompt (hf fd) g, already a hypothesis.)
   3. Wrappers: wrap_ok V W inner says W m runs m on the history inner m h,
      and shows the socket part of m.  For W (server_v V hf lfd):
      uses_ok (sv_uses_ok), accepts_progress (from sv_accept_progress) and
      the view (from sv_handler_view).

  MAIN: server_v_live; server_with_live_from_v re-derives server_with_live
  (skeletonLive) with its statement unchanged, for idV and the
  identity wrapper.
*)
Theory skeletonVLive
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  echoProgress socketWorld socketFair EchoSpec HttpGetSpec
  loopPollWorld loopRounds relabel relabelDist
  echoSockModel loopSockInv loopRoundsTrans loopPollDyn echoRunOk
  echoLiveSched echoLiveAccount echoLiveProg echoLiveWorld echoLiveReadSoon
  echoLiveQueue echoLiveAcceptSoon echoLiveDrain skeletonRunOk skeleton
  echoServerUses skeletonUses skeletonProgress skeletonSock
  skeletonLive skeletonV skeletonVProgress
Libs
  preamble

(* ------------------------------------------------------------------------
   1. Any socket machine M
   ------------------------------------------------------------------------ *)

(* A socket machine, with results of type 'mx option *)
Type smach = “: (event, echoServer$response) snapshot list ->
                (echoServer$action, 'mx option) asyncCore$outcome”

(* M keeps accepting: if the listener is readable in two snapshots in a
   row, and the world answers promptly, M accepts during those rounds *)
Definition accepts_progress_def:
  accepts_progress lfd (M : 'mx smach) ⇔
    ∀h k. prompt M h ∧ k + 2 ≤ LENGTH h ∧
          (∀j. k ≤ j ∧ j < k + 2 ⇒ Readable lfd ∈ (EL j h).ready) ⇒
          naccepts lfd (M (TAKE k h)).actions < naccepts lfd (M (TAKE (k + 2) h)).actions
End

(* sw_accept_progress says server_with keeps accepting *)
Theorem accepts_progress_server_with:
  hok hf ⇒ accepts_progress lfd (server_with hf lfd)
Proof
  rw[accepts_progress_def] >> irule sw_accept_progress >> simp[]
QED

(* If M's accepts of lfd grew between rounds i and i + d, it emitted an
   accept of lfd in one of the rounds i+1 .. i+d *)
Theorem m_naccepts_step:
  ∀d. asyncLevel1$wf (M : 'mx smach) ∧
      naccepts lfd (M (TAKE i h)).actions < naccepts lfd (M (TAKE (i + d) h)).actions ⇒
      ∃k. i < k ∧ k ≤ i + d ∧ MEM (Accept lfd) (new_actions (log_of M) (TAKE k h))
Proof
  Induct >- simp[] >> rpt strip_tac
  >> Cases_on ‘naccepts lfd (M (TAKE i h)).actions < naccepts lfd (M (TAKE (i + d) h)).actions’
  >- (first_x_assum drule_all >> strip_tac >> qexists_tac ‘k’ >> simp[])
  >> qexists_tac ‘i + SUC d’ >> simp[]
  >> ‘i + SUC d ≤ LENGTH h’
       by (CCONTR_TAC
           >> ‘TAKE (i + SUC d) h = h ∧ TAKE (i + d) h = h’ by simp[TAKE_LENGTH_TOO_LONG]
           >> gvs[])
  >> ‘TAKE (i + SUC d) h = TAKE (i + d) h ++ [EL (i + d) h]’
       by (‘i + SUC d = SUC (i + d)’ by simp[] >> pop_assum SUBST1_TAC
           >> simp[GSYM SNOC_EL_TAKE, SNOC_APPEND])
  >> pop_assum SUBST_ALL_TAC
  >> ‘(M (TAKE (i + d) h ++ [EL (i + d) h])).actions =
      (M (TAKE (i + d) h)).actions ++
      new_actions (log_of M) (TAKE (i + d) h ++ [EL (i + d) h])’
       by (qspecl_then [‘log_of M’, ‘TAKE (i + d) h’, ‘EL (i + d) h’] mp_tac
             (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
           >> simp[log_of_def, wf_SNOC_actions])
  >> gvs[naccepts_def, echoProgressTheory.count_def, FILTER_APPEND_DISTRIB] >> CCONTR_TAC
  >> ‘FILTER (λa. a = Accept lfd)
        (new_actions (log_of M) (TAKE (i + d) h ++ [EL (i + d) h])) = []’
       by simp[FILTER_EQ_NIL, EVERY_MEM]
  >> gvs[]
QED

(* While connections are pending (the listener is ready), M accepts in one
   of the next two rounds (sw_accept_soon_s, for M) *)
Theorem m_accept_soon_s:
  asyncLevel1$wf (M : 'mx smach) ∧
  accepts_progress lfdn M ∧ uses_ok lfdn M ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  (∀j. n < j ∧ j ≤ n + 2 ⇒ is_ready (gstate (EI lfdn) (srelabel M) s0 j) (n2w lfdn)) ⇒
  ∃i. 1 ≤ i ∧ i ≤ 2 ∧ MEM (loopPollWorld$Accept (n2w lfdn)) (SAg M (EI lfdn) s0 (n + i))
Proof
  rpt strip_tac
  >> ‘grun_ok (EI lfdn) (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[])
  (* M sees the listener readable in snapshots n, n + 1 *)
  >> ‘∀j. n ≤ j ∧ j < n + 2 ⇒
          Readable lfdn ∈ (EL j (MAP sfs (ghist (EI lfdn) (srelabel M) s0 (n + 2)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> qexists_tac ‘n2w lfdn’ >> simp[]
           (* the listener is in the interest list *)
           >> irule interest_accepted >> simp[])
  >> ‘prompt M (MAP sfs (ghist (EI lfdn) (srelabel M) s0 (n + 2)))’ by simp[prompt_ghist]
  >> qpat_x_assum ‘accepts_progress _ _’
       (qspecl_then [‘MAP sfs (ghist (EI lfdn) (srelabel M) s0 (n + 2))’, ‘n’] mp_tac o
        REWRITE_RULE [accepts_progress_def])
  >> impl_tac >- simp[]
  >> ‘∀k. k ≤ n + 2 ⇒ TAKE k (MAP sfs (ghist (EI lfdn) (srelabel M) s0 (n + 2))) =
                       MAP sfs (ghist (EI lfdn) (srelabel M) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> strip_tac
  >> qspecl_then [‘2’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (EI lfdn) (srelabel M) s0 (n + 2))’] m_naccepts_step)
  >> impl_tac >- simp[] >> strip_tac
  (* an accept of M is an accept of the socket program *)
  >> qexists_tac ‘k − n’ >> simp[]
  >> gvs[gacts_def, new_actions_relabel, MEM_MAP]
  >> qexists_tac ‘Accept lfdn’ >> simp[sfa_def]
QED

(* A pending connection is eventually handed out to M *)
Theorem m_queue_progress:
  asyncLevel1$wf (M : 'mx smach) ∧
  accepts_progress lfdn M ∧ uses_ok lfdn M ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k (gstate (EI lfdn) (srelabel M) s0 n) ⇒
        ∃N. MEM c (wacc (SPg M (EI lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[])
  >> completeInduct_on ‘k’ >> rpt strip_tac
  >> Cases_on ‘MEM c (wacc (SPg M (EI lfdn) s0 (n + 3)))’ >- metis_tac[]
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
  >> simp[] >> strip_tac >- metis_tac[]
  >> ‘0 < nacc (n2w lfdn) (SAg M (EI lfdn) s0 (i + n))’
       by (gvs[nacc_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >> metis_tac[])
  >> qpat_x_assum ‘∀m. m < k ⇒ _’ (qspec_then ‘k''’ mp_tac) >> impl_tac >- fs[]
  >> disch_then (qspec_then ‘SUC (i + n)’ mp_tac) >> fs[]
QED

(* MAIN: if M keeps accepting, every connection of the world is eventually
   handed out to M (sw_conn_accepted, for M) *)
Theorem m_conn_accepted:
  asyncLevel1$wf (M : 'mx smach) ∧
  accepts_progress lfdn M ∧ uses_ok lfdn M ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  is_conn (gstate (EI lfdn) (srelabel M) s0 n) c ⇒
  ∃N. MEM c (wacc (SPg M (EI lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[])
  >> qspecl_then [‘EI lfdn’, ‘srelabel M’, ‘s0’, ‘n2w lfdn’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfd’] grounds_known)
  >> simp[] >> disch_then (qspec_then ‘n’ (strip_assume_tac o CONJUNCT2))
  >> fs[known_def] >> first_x_assum drule >> strip_tac >- metis_tac[]
  >> qpat_x_assum ‘MEM c (lq _ _)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’] mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘c’] m_queue_progress)
  >> impl_tac >- fs[] >> disch_then irule
  >> qexistsl_tac [‘LENGTH l1’, ‘n’] >> simp[queued_def] >> metis_tac[]
QED

(* What a transcript function t has read from fd after j snapshots of g *)
Definition hread_t_def:
  hread_t fd t g j = CONCAT (read fd (t (TAKE j g)))
End

(* henv (skeletonLive), for a transcript function t in place of a
   handler's transcript *)
Definition henv_t_def:
  henv_t fd t g j0 D ⇔
    (∀j. j0 ≤ j ∧ j ≤ LENGTH g ⇒ hread_t fd t g j ≼ D ∨ D ≼ hread_t fd t g j) ∧
    (∀j. j0 ≤ j ∧ j < LENGTH g ∧ Readable fd ∉ (EL j g).ready ⇒
         D ≼ hread_t fd t g (SUC j)) ∧
    (∀j. j0 ≤ j ∧ j < LENGTH g ∧ MEM (Read fd, NONE) (t (TAKE j g)) ∧
         ¬(D ≼ hread_t fd t g j) ⇒
         D ≼ hread_t fd t g (SUC j) ∨
         LENGTH (hread_t fd t g j) < LENGTH (hread_t fd t g (SUC j))) ∧
    (∀j. j0 ≤ j ∧ j ≤ LENGTH g ∧ MEM (Read fd, SOME Eof) (t (TAKE j g)) ⇒
         D ≼ hread_t fd t g j)
End

Theorem henv_t_trans:
  henv fd h g j0 D ⇔ henv_t fd (trans h) g j0 D
Proof
  simp[henv_def, henv_t_def, hread_def, hread_t_def]
QED

(* gen_rounds_bytes, with HttpGetSpec's bytes *)
Theorem m_rounds_bytes:
  uses_ok lfdn M ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀c n.
    bytes_written_to c (FLAT (GENLIST (grounds_events ifds (srelabel M) s0) (SUC n))) =
      bytes (FLAT (written (w2n c) (TSg M ifds s0 n))) ∧
    bytes_read_from c (FLAT (GENLIST (grounds_events ifds (srelabel M) s0) n)) =
      bytes (FLAT (read (w2n c) (TSg M ifds s0 n)))
Proof
  rw[bytes_def] >> metis_tac[gen_rounds_bytes]
QED

(* MAIN: an accepted connection c, served by a view (g, t) from round a,
   gets its environment from the socket world: henv_t for any prefix D of
   what was sent on c by round n; and what t writes is what the loop's
   events write to c (sw_view_henv, for any M and t) *)
Theorem m_view_henv:
  uses_ok lfdn (M : 'mx smach) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  interest_covers ifds (srelabel M) s0 ∧
  MEM c (wacc (SPg M ifds s0 n)) ∧ bytes D ≼ sent_upto c n s0 ∧
  a ≤ n ∧ LENGTH g + a = N ∧
  (∀i. i < LENGTH g ⇒
       (EL i g).ready = (EL (a + i) (MAP sfs (ghist ifds (srelabel M) s0 N))).ready) ∧
  (∀j. j ≤ LENGTH g ⇒ FILTER (on_fd (w2n c)) (TSg M ifds s0 (a + j)) = t (TAKE j g)) ⇒
  henv_t (w2n c) t g (n − a) D ∧
  ∀j. j ≤ LENGTH g ⇒
    bytes (FLAT (written (w2n c) (t (TAKE j g)))) =
      bytes_written_to c (FLAT (GENLIST (grounds_events ifds (srelabel M) s0) (SUC (a + j))))
Proof
  strip_tac >>
  ‘grun_ok ifds (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[]) >>
  (* the view's reads and writes are the loop's *)
  ‘∀j. j ≤ LENGTH g ⇒
       bytes (hread_t (w2n c) t g j) = pread_all c (SPg M ifds s0 (a + j)) ∧
       bytes (FLAT (written (w2n c) (t (TAKE j g)))) =
         bytes_written_to c (FLAT (GENLIST (grounds_events ifds (srelabel M) s0) (SUC (a + j))))’
    by (rpt gen_tac >> strip_tac >> simp[hread_t_def] >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _’ (qspec_then ‘j’ mp_tac) >>
        impl_tac >- simp[] >> disch_then (SUBST1_TAC o SYM) >>
        simp[read_FILTER, written_FILTER] >>
        ‘bytes_read_from c (FLAT (GENLIST (grounds_events ifds (srelabel M) s0) (a + j))) =
         pread_all c (SPg M ifds s0 (a + j))’
          by (irule bytes_read_from_rounds >> first_assum ACCEPT_TAC) >>
        drule_all m_rounds_bytes >> strip_tac >>
        metis_tac[]) >>
  reverse conj_tac >- (rpt strip_tac >> fs[]) >>
  qabbrev_tac ‘fd = w2n (c : word64)’ >>
  ‘n2w fd = c’ by simp[Abbr ‘fd’] >>
  qabbrev_tac ‘j0 = n − a’ >>
  (* what was sent on c, round by round, against what t read *)
  ‘∀j. j ≤ LENGTH g ⇒
       ∃inc. sent_upto c (a + j) s0 = bytes (hread_t fd t g j) ++ inc ∧
             (∀cn. ALOOKUP (gstate ifds (srelabel M) s0 (a + j)).conns c = SOME cn ⇒
                   inc = cn.incoming) ∧
             (ALOOKUP (gstate ifds (srelabel M) s0 (a + j)).conns c = NONE ⇒ inc = [])’
    by (rpt strip_tac >>
        ‘∃inc. sent_upto c (a + j) s0 = pread_all c (SPg M ifds s0 (a + j)) ++ inc ∧
               (∀cn. ALOOKUP (gstate ifds (srelabel M) s0 (a + j)).conns c = SOME cn ⇒
                     inc = cn.incoming) ∧
               (ALOOKUP (gstate ifds (srelabel M) s0 (a + j)).conns c = NONE ⇒ inc = [])’
          by (irule sent_split_sw >> simp[]) >>
        qexists_tac ‘inc’ >> simp[] >> metis_tac[]) >>
  (* from round n on, D has been sent *)
  ‘∀j. j0 ≤ j ⇒ bytes D ≼ sent_upto c (a + j) s0’
    by (rpt strip_tac >> irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[] >> ‘a + j = n + (a + j − n)’ by simp[Abbr ‘j0’] >>
        pop_assum SUBST1_TAC >> simp[sent_upto_prefix]) >>
  simp[henv_t_def] >> rpt conj_tac >> rpt strip_tac
  (* what has been read and D are comparable *)
  >- (REWRITE_TAC[GSYM bytes_prefix_sw] >>
      first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      metis_tac[prefixes_is_prefix_total, IS_PREFIX_APPEND3, IS_PREFIX_TRANS])
  (* not reported readable: nothing unread at the next round *)
  >- (‘a + j < N ∧ j + 1 ≤ LENGTH g ∧ j0 ≤ j + 1’ by fs[] >>
      ‘MEM c (wacc (SPg M ifds s0 (a + j)))’
        by (irule wacc_mono >> qexists_tac ‘n’ >> fs[Abbr ‘j0’]) >>
      ‘MEM c (ifds (ghist ifds (srelabel M) s0 (a + j)))’
        by fs[interest_covers_def] >>
      ‘¬is_ready (gstate ifds (srelabel M) s0 (a + (j + 1))) c’
        by (strip_tac >> qpat_x_assum ‘Readable fd ∉ _’ mp_tac >>
            qpat_x_assum ‘∀i. i < LENGTH g ⇒ _’ (qspec_then ‘j’ mp_tac) >>
            impl_tac >- simp[] >> disch_then SUBST1_TAC >>
            simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER] >>
            qexists_tac ‘c’ >> fs[Abbr ‘fd’, ADD1]) >>
      qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j + 1’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘inc = []’
        by (Cases_on ‘ALOOKUP (gstate ifds (srelabel M) s0 (a + (j + 1))).conns c’ >> fs[] >>
            fs[is_ready_def] >> gvs[]) >>
      qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j + 1’ mp_tac) >>
      impl_tac >- simp[] >>
      qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
      qpat_x_assum ‘inc = []’ SUBST1_TAC >>
      REWRITE_TAC[APPEND_NIL, bytes_prefix_sw, ADD1])
  (* an outstanding read, with D not all read: there was unread data *)
  >- (disj2_tac >>
      ‘j ≤ LENGTH g ∧ j + 1 ≤ LENGTH g’ by fs[] >>
      ‘MEM (Read fd, NONE) (TSg M ifds s0 (a + j))’
        by (qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _’ (qspec_then ‘j’ mp_tac) >>
            impl_tac >- simp[] >> strip_tac >>
            qpat_x_assum ‘FILTER _ _ = _’ (fn th =>
              qpat_x_assum ‘MEM _ (t _)’ (mp_tac o REWRITE_RULE [GSYM th])) >>
            simp[MEM_FILTER]) >>
      ‘reads_c c (SAg M ifds s0 (a + j))’
        by (qpat_x_assum ‘n2w fd = c’ (SUBST1_TAC o SYM) >>
            irule TSg_read_none >> metis_tac[]) >>
      qpat_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘inc ≠ []’
        by (strip_tac >> qpat_x_assum ‘¬(D ≼ _)’ mp_tac >>
            REWRITE_TAC[GSYM bytes_prefix_sw] >>
            qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j’ mp_tac) >>
            impl_tac >- simp[] >>
            qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
            qpat_x_assum ‘inc = []’ SUBST1_TAC >>
            REWRITE_TAC[APPEND_NIL] >> metis_tac[]) >>
      ‘∃cn. ALOOKUP (gstate ifds (srelabel M) s0 (a + j)).conns c = SOME cn ∧
            cn.incoming ≠ []’
        by (Cases_on ‘ALOOKUP (gstate ifds (srelabel M) s0 (a + j)).conns c’ >- fs[] >>
            qpat_x_assum ‘∀cn. _ ⇒ inc = _’ (qspec_then ‘x’ mp_tac) >> simp[] >>
            strip_tac >> fs[]) >>
      drule grun_ok_sock_acts >>
      disch_then (qspec_then ‘a + j’ strip_assume_tac) >>
      drule_all sock_acts_read_nonempty >> strip_tac >>
      ‘STRLEN (hread_t fd t g j) = LENGTH (pread_all c (SPg M ifds s0 (a + j))) ∧
       STRLEN (hread_t fd t g (SUC j)) =
         LENGTH (pread_all c (SPg M ifds s0 (a + j + 1)))’
        by metis_tac[LENGTH_bytes_sw, ADD1, ADD_ASSOC] >>
      simp[GSYM ADD1, gperf_SUC] >>
      Cases_on ‘pread_all c (ZIP (gacts ifds (srelabel M) s0 (a + j),
                                  gres ifds (srelabel M) s0 (a + j)))’ >>
      fs[])
  (* after end-of-file, nothing is unread *)
  >> ‘MEM (Read fd, SOME Eof) (TSg M ifds s0 (a + j))’
    by (qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _’ (qspec_then ‘j’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_x_assum ‘FILTER _ _ = _’ (fn th =>
          qpat_x_assum ‘MEM _ (t _)’ (mp_tac o REWRITE_RULE [GSYM th])) >>
        simp[MEM_FILTER]) >>
  ‘∃k. MEM (Read c k, Got (SOME [])) (SPg M ifds s0 (a + j))’
    by (qpat_x_assum ‘n2w fd = c’ (SUBST1_TAC o SYM) >>
        irule TSg_eof >> metis_tac[]) >>
  ‘∃cn. ALOOKUP (gstate ifds (srelabel M) s0 (a + j)).conns c = SOME cn ∧ cn.incoming = []’
    by metis_tac[grounds_eof] >>
  qpat_assum ‘∀j. j ≤ LENGTH g ⇒ ∃inc. _’ (qspec_then ‘j’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘inc = []’ by metis_tac[] >>
  qpat_x_assum ‘∀j. j0 ≤ j ⇒ bytes D ≼ _’ (qspec_then ‘j’ mp_tac) >>
  impl_tac >- simp[] >>
  qpat_x_assum ‘sent_upto _ _ _ = _’ SUBST1_TAC >>
  qpat_x_assum ‘inc = []’ SUBST1_TAC >>
  REWRITE_TAC[APPEND_NIL, bytes_prefix_sw]
QED

(* ------------------------------------------------------------------------
   2. The per-handler obligation, through V
   ------------------------------------------------------------------------ *)

(* A machine over V's actions and responses, with results of type 'x option *)
Type vmach = “: (event, 'res) snapshot list -> ('act, 'x option) asyncCore$outcome”

(* handler_live, on the socket part of the handler's transcript.  A handler
   that also asks queries (as the KV handler does) has each answered in the
   next round: that is prompt (hf fd) g, already a hypothesis. *)
Definition handler_live_v_def:
  handler_live_v (V : ('act, 'k, 'q, 'res) vocab) (hf : num -> ('act, 'res, 'z) vmach) out B ⇔
    ∀fd g j0 D.
      prompt (hf fd) g ∧ henv_t fd (λq. sproj V (trans (hf fd) q)) g j0 D ∧
      j0 + B D ≤ LENGTH g ⇒
      ∃j. j ≤ LENGTH g ∧ out D ≼ written fd (sproj V (trans (hf fd) (TAKE j g)))
End

(* For the identity vocabulary, it is handler_live *)
Theorem handler_live_v_idV:
  handler_live_v idV hf out B ⇔ handler_live hf out B
Proof
  simp[handler_live_v_def, handler_live_def, henv_t_trans] >>
  ‘∀fd. (λq. trans (hf fd) q) = trans (hf fd)’ by simp[FUN_EQ_THM] >>
  simp[]
QED

(* ------------------------------------------------------------------------
   3. Wrappers
   ------------------------------------------------------------------------ *)

(* The socket actions among some actions over V *)
Definition sacts_def:
  sacts V acts = FLAT (MAP (λa. case V.sact a of SOME x => [x] | NONE => []) acts)
End

Theorem sacts_simps[simp]:
  sacts V [] = [] ∧
  sacts V (a :: as) = (case V.sact a of SOME x => [x] | NONE => []) ++ sacts V as
Proof
  simp[sacts_def]
QED

(* Wr m runs m on the history inner m h (the same snapshots, with the
   results m expects) and shows the socket part of m: its socket actions
   and the socket part of its transcript; if the world answers Wr m
   promptly, m is answered promptly *)
Definition wrap_ok_def:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, 'x) vmach -> 'y smach) inner ⇔
    ∀m h. asyncLevel1$wf m ⇒
      asyncLevel1$wf (Wr m) ∧
      (Wr m h).actions = sacts V (m (inner m h)).actions ∧
      trans (Wr m) h = sproj V (trans m (inner m h)) ∧
      (prompt (Wr m) h ⇒ prompt m (inner m h)) ∧
      LENGTH (inner m h) = LENGTH h ∧
      (∀i. i < LENGTH h ⇒ (EL i (inner m h)).ready = (EL i h).ready) ∧
      ∀j. inner m (TAKE j h) = TAKE j (inner m h)
End

Theorem sacts_idV[simp]:
  ∀acts. sacts idV acts = acts
Proof
  Induct >> simp[idV_def]
QED

(* The identity wrapper, for the identity vocabulary *)
Theorem wrap_ok_id:
  wrap_ok idV (λm. m) (λm h. h)
Proof
  rw[wrap_ok_def]
QED

(* ------------------------------------------------------------------------
   4. The skeleton inside a wrapper
   ------------------------------------------------------------------------ *)

Theorem sproj_NIL[simp]:
  sproj V [] = []
Proof
  simp[sproj_def]
QED

Theorem sproj_CONS[simp]:
  sproj V ((a, r) :: tr) =
    (case V.sact a of SOME x => [(x, OPTION_BIND r V.sres)] | NONE => []) ++ sproj V tr
Proof
  simp[sproj_def]
QED

Theorem sproj_acc_CONS:
  vocab_ok V ⇒
  sproj V ((V.acc l, r) :: tr) = (Accept l, OPTION_BIND r V.sres) :: sproj V tr
Proof
  rw[vocab_ok_def]
QED

(* Filtering the socket part is filtering the entries whose socket part
   passes *)
Theorem sproj_FILTER:
  ∀tr. FILTER P (sproj V tr) = sproj V (FILTER (λe. EXISTS P (sproj V [e])) tr)
Proof
  Induct >> simp[] >> PairCases >> simp[] >> Cases_on ‘V.sact h0’ >> rw[]
QED

(* A socket entry is on fd iff its action belongs to fd *)
Theorem on_fd_sact:
  vocab_ok V ∧ V.sact a = SOME x ⇒ (on_fd fd (x, y) ⇔ V.owner a = SOME fd)
Proof
  rw[vocab_ok_def] >> first_x_assum drule >> Cases_on ‘x’ >> rw[on_fd_def] >>
  gvs[] >> metis_tac[]
QED

Theorem sproj_FILTER_on_fd:
  vocab_ok V ⇒
  ∀tr. FILTER (on_fd fd) (sproj V tr) = sproj V (FILTER (on_fd_v V fd) tr)
Proof
  strip_tac >> Induct >> simp[] >> PairCases >> simp[] >>
  Cases_on ‘V.sact h0’ >> rw[on_fd_v_def] >> gvs[] >>
  metis_tac[on_fd_sact]
QED

Theorem naccepts_APPEND[local]:
  naccepts lfd (l1 ++ l2) = naccepts lfd l1 + naccepts lfd l2
Proof
  simp[naccepts_def, echoProgressTheory.count_def, FILTER_APPEND_DISTRIB]
QED

(* The accepts among the socket actions are the accepts through V *)
Theorem naccepts_sacts:
  vocab_ok V ⇒ ∀acts. naccepts lfd (sacts V acts) = nacceptsv V lfd acts
Proof
  strip_tac >> Induct >> simp[naccepts_APPEND] >> gen_tac >>
  Cases_on ‘V.sact h’ >> simp[]
  >- (rw[] >> fs[vocab_ok_def] >> metis_tac[NOT_SOME_NONE])
  >> ‘x = Accept lfd ⇔ h = V.acc lfd’ by (fs[vocab_ok_def] >> metis_tac[SOME_11])
  >> simp[]
QED

(* An accept belongs to no connection *)
Theorem sact_acc_owner:
  vocab_ok V ∧ V.sact a = SOME (Accept l) ⇒ V.owner a = NONE
Proof
  rw[vocab_ok_def] >> ‘a = V.acc l’ by metis_tac[] >> gvs[]
QED

(* The handler's entries have no accept, and touch no other connection *)
Theorem hv_no_acc_entries[local]:
  vocab_ok V ∧ hokv V hf ⇒
  FILTER (λe. EXISTS is_accept (sproj V [e])) (trans (hf c) hh) = []
Proof
  rw[FILTER_EQ_NIL, EVERY_MEM] >> drule_then (qspecl_then [‘c’, ‘hh’] mp_tac) hokv_own >>
  rw[EVERY_MEM] >> first_x_assum drule >> PairCases_on ‘e’ >>
  rw[on_fd_v_def] >> Cases_on ‘V.sact e0’ >> gvs[is_accept_def] >>
  metis_tac[sact_acc_owner, NOT_SOME_NONE]
QED

Theorem hv_no_touch_entries[local]:
  vocab_ok V ∧ hokv V hf ∧ g ≠ c ⇒
  FILTER (λe. EXISTS (touches g) (sproj V [e])) (trans (hf c) hh) = []
Proof
  rw[FILTER_EQ_NIL, EVERY_MEM] >> drule_then (qspecl_then [‘c’, ‘hh’] mp_tac) hokv_own >>
  rw[EVERY_MEM] >> first_x_assum drule >> PairCases_on ‘e’ >>
  rw[on_fd_v_def] >> Cases_on ‘V.sact e0’ >> gvs[touches_def, accepts_def] >>
  rw[] >> metis_tac[on_fd_sact, sact_acc_owner, SOME_11, NOT_SOME_NONE]
QED

(* MAIN: the socket part of the skeleton uses the socket API correctly:
   it accepts only on lfd, and reads or writes a connection only after it
   was handed out (server_with_uses_accepted, for any vocabulary) *)
Theorem sv_uses_ok:
  vocab_ok (V : ('act, 'k, 'q, 'res) vocab) ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ⇒
  ∀hh. accepts_on lfd (sproj V (trans (server_v V hf lfd) hh)) ∧
       ∀fd. acc_first fd (sproj V (trans (server_v V hf lfd) hh))
Proof
  strip_tac >> ‘V.sact (V.acc lfd) = SOME (Accept lfd)’ by fs[vocab_ok_def] >>
  gen_tac >> measureInduct_on ‘LENGTH hh’
  >> ONCE_REWRITE_TAC[sv_steps]
  (* wait until the listener is readable *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) hh’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘hh’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac
  >- simp[accepts_on_def, acc_first_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  (* accept *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (V.acc lfd)) K1) h2’
  >> qspecl_then [‘emit (vocab_acc V lfd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- simp[trans_emit, sproj_acc_CONS, accepts_on_def, acc_first_def, is_accept_def,
          accepts_def, on_fd_def]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, sproj_acc_CONS, sv_after_accept_def]
  >> Cases_on ‘vaccd V res’ >> simp[]
  (* no new connection: the rest of the skeleton *)
  >- (‘∀fd. ¬accepts fd (Accept lfd, V.sres res)’
        by (rw[accepts_def] >> strip_tac >> fs[vaccd_def]) >>
      first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >> strip_tac >>
      fs[accepts_on_def, acc_first_def, is_accept_def, on_fd_def])
  (* a new connection c: its handler, alongside the rest of the skeleton *)
  >> rename1 ‘vaccd V res = SOME c’
  >> ‘V.sres res = SOME (Accepted c)’ by (fs[vaccd_def] >> every_case_tac >> fs[])
  >> qabbrev_tac ‘R = right_view (hf c) (server_v V hf lfd) h2'’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’, LENGTH_views]
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[] >> strip_tac
  >> conj_tac
  >- (‘accepts_on lfd (sproj V (trans (both (hf c) (server_v V hf lfd)) h2'))’
        suffices_by simp[accepts_on_def, is_accept_def] >>
      ONCE_REWRITE_TAC[GSYM accepts_on_FILTER] >>
      ‘FILTER is_accept (sproj V (trans (both (hf c) (server_v V hf lfd)) h2')) =
       FILTER is_accept (sproj V (trans (server_v V hf lfd) R))’
        by (simp[sproj_FILTER] >> AP_TERM_TAC >> simp[Abbr ‘R’] >>
            irule trans_both_filter_right >> simp[hv_no_acc_entries]) >>
      pop_assum SUBST1_TAC >> simp[accepts_on_FILTER])
  >> gen_tac >> simp[acc_first_def, accepts_def, on_fd_def]
  >> Cases_on ‘fd = c’ >> simp[]
  >> ONCE_REWRITE_TAC[GSYM acc_first_FILTER]
  >> ‘FILTER (touches fd) (sproj V (trans (both (hf c) (server_v V hf lfd)) h2')) =
      FILTER (touches fd) (sproj V (trans (server_v V hf lfd) R))’
       by (simp[sproj_FILTER] >> AP_TERM_TAC >> simp[Abbr ‘R’] >>
           irule trans_both_filter_right >> simp[hv_no_touch_entries])
  >> pop_assum SUBST1_TAC >> simp[acc_first_FILTER]
QED

(* The wrapped skeleton uses the socket API correctly *)
Theorem uses_ok_wrap:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ⇒
  uses_ok lfd (Wr (server_v V hf lfd))
Proof
  rw[uses_ok_def] >>
  ‘asyncLevel1$wf (server_v V hf lfd)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘trans (Wr (server_v V hf lfd)) hh =
   sproj V (trans (server_v V hf lfd) (inner (server_v V hf lfd) hh))’
    by fs[wrap_ok_def] >>
  simp[] >> metis_tac[sv_uses_ok]
QED

(* The wrapped skeleton keeps accepting *)
Theorem accepts_progress_wrap:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ⇒
  accepts_progress lfd (Wr (server_v V hf lfd))
Proof
  rw[accepts_progress_def] >>
  ‘asyncLevel1$wf (server_v V hf lfd)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘∀h. (Wr (server_v V hf lfd) h).actions =
         sacts V (server_v V hf lfd (inner (server_v V hf lfd) h)).actions ∧
       (prompt (Wr (server_v V hf lfd)) h ⇒
        prompt (server_v V hf lfd) (inner (server_v V hf lfd) h)) ∧
       LENGTH (inner (server_v V hf lfd) h) = LENGTH h ∧
       (∀i. i < LENGTH h ⇒ (EL i (inner (server_v V hf lfd) h)).ready = (EL i h).ready) ∧
       ∀j. inner (server_v V hf lfd) (TAKE j h) = TAKE j (inner (server_v V hf lfd) h)’
    by fs[wrap_ok_def] >>
  simp[naccepts_sacts] >>
  qspecl_then [‘inner (server_v V hf lfd) h’, ‘k’] mp_tac sv_accept_progress >>
  simp[]
QED

(* MAIN: c, handed out by round n to the wrapped skeleton, is served by its
   own handler hf (w2n c), on a history g from the round a ≤ n in which c
   was handed out: g has the loop's ready sets, the world answers the
   handler promptly, and the loop's transcript on c is the socket part of
   the handler's (sw_view, for any vocabulary and wrapper) *)
Theorem view_wrap:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 n)) ∧ n ≤ N ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = N ∧ prompt (hf (w2n c)) g ∧
    (∀i. i < LENGTH g ⇒
         (EL i g).ready =
         (EL (a + i) (MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 N))).ready) ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd (w2n c)) (TSg (Wr (server_v V hf lfdn)) ifds s0 (a + j)) =
      sproj V (trans (hf (w2n c)) (TAKE j g))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  ‘grun_ok ifds (srelabel (Wr (server_v V hf lfdn))) s0’ by (irule gen_grun_ok >> metis_tac[]) >>
  ‘∀h. trans (Wr (server_v V hf lfdn)) h =
         sproj V (trans (server_v V hf lfdn) (inner (server_v V hf lfdn) h)) ∧
       (prompt (Wr (server_v V hf lfdn)) h ⇒
        prompt (server_v V hf lfdn) (inner (server_v V hf lfdn) h)) ∧
       LENGTH (inner (server_v V hf lfdn) h) = LENGTH h ∧
       (∀i. i < LENGTH h ⇒ (EL i (inner (server_v V hf lfdn) h)).ready = (EL i h).ready) ∧
       ∀j. inner (server_v V hf lfdn) (TAKE j h) = TAKE j (inner (server_v V hf lfdn) h)’
    by fs[wrap_ok_def] >>
  qabbrev_tac ‘H = MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 N)’ >>
  qabbrev_tac ‘IH = inner (server_v V hf lfdn) H’ >>
  ‘LENGTH H = N ∧ LENGTH IH = N’ by simp[Abbr ‘H’, Abbr ‘IH’] >>
  (* the loop's transcript, as the socket part of the skeleton's on IH *)
  ‘∀k. k ≤ N ⇒
       TSg (Wr (server_v V hf lfdn)) ifds s0 k = sproj V (trans (server_v V hf lfdn) (TAKE k IH))’
    by (rpt strip_tac >>
        ‘MAP sfs (ghist ifds (srelabel (Wr (server_v V hf lfdn))) s0 k) = TAKE k H’
          by simp[Abbr ‘H’, GSYM MAP_TAKE, ghist_TAKE] >>
        simp[Abbr ‘IH’]) >>
  ‘∀k. accepted (TSg (Wr (server_v V hf lfdn)) ifds s0 k) =
       MAP w2n (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 k))’
    by metis_tac[TSg_accepted] >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) ifds s0 N))’
    by (irule wacc_mono >> qexists_tac ‘n’ >> simp[]) >>
  ‘TSg (Wr (server_v V hf lfdn)) ifds s0 N = sproj V (trans (server_v V hf lfdn) IH)’
    by (qpat_x_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘N’ mp_tac) >>
        simp[TAKE_LENGTH_ID_rwt]) >>
  qspec_then ‘IH’ mp_tac (Q.INST [‘fd’ |-> ‘w2n (c : word64)’, ‘lfd’ |-> ‘lfdn’] sv_handler_view) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (‘fresh (TSg (Wr (server_v V hf lfdn)) ifds s0 N)’ by metis_tac[gen_fresh] >>
          pop_assum mp_tac >>
          qpat_assum ‘TSg _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
          simp[freshv_def, acceptedv_def, fresh_def])
      >- (‘prompt (Wr (server_v V hf lfdn)) H’ by simp[Abbr ‘H’, prompt_ghist] >>
          simp[Abbr ‘IH’])
      >> ‘MEM (w2n c) (accepted (TSg (Wr (server_v V hf lfdn)) ifds s0 N))’
           by (qpat_x_assum ‘∀k. accepted _ = _’ (fn th => REWRITE_TAC[th]) >>
               simp[MEM_MAP] >> metis_tac[])
      >> pop_assum mp_tac >> qpat_assum ‘TSg _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
      simp[acceptedv_def]) >>
  strip_tac >>
  ‘a ≤ n’
    by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> disch_then irule >>
        ‘TSg (Wr (server_v V hf lfdn)) ifds s0 n =
         sproj V (trans (server_v V hf lfdn) (TAKE n IH))’
          by (qpat_x_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘n’ mp_tac) >> simp[]) >>
        ‘MEM (w2n c) (accepted (TSg (Wr (server_v V hf lfdn)) ifds s0 n))’
          by (qpat_x_assum ‘∀k. accepted _ = _’ (fn th => REWRITE_TAC[th]) >>
              simp[MEM_MAP] >> metis_tac[]) >>
        pop_assum mp_tac >> qpat_assum ‘TSg _ _ _ n = _’ (fn th => REWRITE_TAC[th]) >>
        simp[acceptedv_def]) >>
  qexistsl_tac [‘a’, ‘g’] >> simp[] >> rpt strip_tac
  >- (‘a + i < N’ by simp[] >> simp[Abbr ‘IH’])
  >> qpat_x_assum ‘∀k. k ≤ N ⇒ TSg _ _ _ _ = _’ (qspec_then ‘a + j’ mp_tac) >>
  simp[] >> disch_then kall_tac >> simp[sproj_FILTER_on_fd]
QED

(* ------------------------------------------------------------------------
   5. Liveness
   ------------------------------------------------------------------------ *)

(* MAIN: the library liveness theorem, for the skeleton over any
   vocabulary V inside any wrapper Wr.  For the dynamic-interest loop in any
   fair socket world: if every handler meets handler_live_v, then for every
   connection c and every prefix D of what its client sent by round n, the
   output owed for D is eventually written to c. *)
Theorem server_v_live:
  wrap_ok (V : ('act, 'k, 'q, 'res) vocab) (Wr : ('act, 'res, unit) vmach -> 'y smach) inner ∧
  vocab_ok V ∧ hokv V (hf : num -> ('act, 'res, 'z) vmach) ∧
  handler_live_v V hf out B ∧ FLAT (out "") = "" ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼
      bytes_written_to c
        (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0) N))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (server_v V hf lfdn)’ by metis_tac[hokv_wf, wf_server_v] >>
  ‘asyncLevel1$wf (Wr (server_v V hf lfdn))’ by fs[wrap_ok_def] >>
  ‘uses_ok lfdn (Wr (server_v V hf lfdn))’ by metis_tac[uses_ok_wrap] >>
  ‘accepts_progress lfdn (Wr (server_v V hf lfdn))’ by metis_tac[accepts_progress_wrap] >>
  ‘grun_ok (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by (irule gen_grun_ok >> metis_tac[]) >>
  (* nothing owed *)
  Cases_on ‘D = ""’
  >- (qexists_tac ‘0’ >> gvs[bytes_def]) >>
  (* otherwise something was sent on c, so c is a connection by round n *)
  ‘sent_upto c n s0 ≠ []’ by (strip_tac >> Cases_on ‘D’ >> fs[bytes_def]) >>
  ‘is_conn (gstate (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  (* it is handed out at some round N0 *)
  ‘∃N0. MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (EI lfdn) s0 N0))’
    by (irule m_conn_accepted >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘n1 = n + N0’ >>
  ‘MEM c (wacc (SPg (Wr (server_v V hf lfdn)) (EI lfdn) s0 n1))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[Abbr ‘n1’]) >>
  ‘bytes D ≼ sent_upto c n1 s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[Abbr ‘n1’, sent_upto_prefix]) >>
  (* its handler's view, B D rounds past n1 *)
  qspecl_then [‘n1’, ‘n1 + B D’] mp_tac
    (Q.GENL [‘n’, ‘N’] view_wrap |> Q.INST [‘ifds’ |-> ‘EI lfdn’]) >>
  impl_tac >- simp[] >> strip_tac >>
  (* the socket world gives the handler its environment *)
  ‘interest_covers (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0’
    by simp[interest_covers_EI] >>
  ‘henv_t (w2n c) (λq. sproj V (trans (hf (w2n c)) q)) g (n1 − a) D ∧
   ∀j. j ≤ LENGTH g ⇒
     bytes (FLAT (written (w2n c) ((λq. sproj V (trans (hf (w2n c)) q)) (TAKE j g)))) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (EI lfdn) (srelabel (Wr (server_v V hf lfdn))) s0)
                        (SUC (a + j))))’
    by (irule m_view_henv >> simp[] >> qexists_tac ‘lfdn’ >> fs[]) >>
  (* so it writes out D *)
  qpat_x_assum ‘handler_live_v _ _ _ _’ (mp_tac o REWRITE_RULE [handler_live_v_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘n1 − a’, ‘D’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac ‘SUC (a + j)’ >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ bytes _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  REWRITE_TAC[bytes_prefix_sw] >>
  qpat_x_assum ‘out D ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* server_with_live's statement (skeletonLive), as the instance of
   server_v_live for idV and the identity wrapper *)
Theorem server_with_live_from_v:
  hok hf ∧ handler_live hf out B ∧ FLAT (out "") = "" ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼
      bytes_written_to c (FLAT (GENLIST (SWEV hf (EI lfdn) lfdn s0) N))
Proof
  mp_tac (Q.GENL [‘V’, ‘Wr’, ‘inner’] server_v_live
          |> Q.ISPECL [‘idV : (echoServer$action, 'k, 'q, echoServer$response) vocab’,
                       ‘λm : (echoServer$action, echoServer$response, unit) vmach. m’,
                       ‘λ(m : (echoServer$action, echoServer$response, unit) vmach)
                         (h : (event, echoServer$response) snapshot list). h’]
          |> INST_TYPE [“:'z” |-> alpha, “:'y” |-> “:unit”]) >>
  simp[wrap_ok_id, vocab_ok_idV, hokv_idV, handler_live_v_idV, GSYM server_with_eq_v]
QED
