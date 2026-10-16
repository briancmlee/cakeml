(*
  The socket-level progress facts for the generic server  server_with hf
  (any well-behaved handler, hok hf, using only the connections it was
  handed, uses_ok), run by the dynamic-interest loop in the socket world:
   - the model transcript against the world's log (TSg_split, TSg_accepted,
     TSg_eof, TSg_read_none);
   - accepts: while connections are pending the server accepts within two
     rounds, so every connection of the world is eventually handed out
     (sw_conn_accepted).
  These are spike/m4-liveness's echo proofs (echoLiveAcceptSoon,
  echoLiveReadSoon), with server lfd replaced by server_with hf lfd,
  echo_grun_ok by gen_grun_ok and server_accept_progress by
  sw_accept_progress.
*)
Theory skeletonSock
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  echoProgress socketWorld loopPollWorld loopRounds relabel
  relabelDist echoSockModel loopSockInv loopRoundsTrans loopPollDyn
  echoRunOk echoLiveSched echoLiveProg echoLiveWorld echoLiveReadSoon
  echoLiveQueue echoLiveAcceptSoon skeletonRunOk skeleton skeletonProgress
Libs
  preamble

(* ------------------------------------------------------------------------
   The model transcript against the world's log
   ------------------------------------------------------------------------ *)

Theorem TSg_split:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∃tt1 tt2. TSg m ifds s0 n = tt1 ++ tt2 ∧
            TREL tt1 (MAP (λ(a, r). (a, SOME r)) (SPg m ifds s0 n)) ∧
            TREL tt2 (MAP (λa. (a, NONE)) (SAg m ifds s0 n))
Proof
  strip_tac >> irule gen_trans_split >> metis_tac[gen_sinv]
QED

(* The connections handed out, in both vocabularies *)
Theorem TSg_accepted:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  accepted (TSg m ifds s0 n) = MAP w2n (wacc (SPg m ifds s0 n))
Proof
  strip_tac >> drule_all TSg_split >>
  disch_then (qspecl_then [‘n’, ‘ifds’] strip_assume_tac) >>
  drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
  simp[accepted_NONE]
QED

(* End-of-file in the transcript is a read that returned nothing *)
Theorem TSg_eof:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM (Read fd, SOME Eof) (TSg m ifds s0 n) ⇒
  ∃k. MEM (Read (n2w fd) k, Got (SOME [])) (SPg m ifds s0 n)
Proof
  strip_tac >> drule_all TSg_split >>
  disch_then (qspecl_then [‘n’, ‘ifds’] strip_assume_tac) >>
  drule TREL_NONE >> strip_tac >> gvs[EVERY_MEM]
  >- (‘MEM (sfa (Read fd), SOME Eof) (MAP (λ(a,r). (sfa a, r)) tt1)’
        by (simp[MEM_MAP] >> qexists_tac ‘(Read fd, SOME Eof)’ >> simp[])
      >> pop_assum mp_tac >> qpat_x_assum ‘MAP _ tt1 = _’ (fn th => REWRITE_TAC[th])
      >> simp[MEM_MAP, EXISTS_PROD, sfa_def, sfr_Eof] >> metis_tac[])
  >> first_x_assum drule >> simp[]
QED

(* An unanswered read in the transcript is a read of this round *)
Theorem TSg_read_none:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM (Read fd, NONE) (TSg m ifds s0 n) ⇒
  reads_c (n2w fd) (SAg m ifds s0 n)
Proof
  strip_tac >> drule_all TSg_split >>
  disch_then (qspecl_then [‘n’, ‘ifds’] strip_assume_tac) >>
  drule TREL_NONE >> strip_tac >> gvs[]
  >- (‘MEM (sfa (Read fd), NONE) (MAP (λ(a,r). (sfa a, r)) tt1)’
        by (simp[MEM_MAP] >> qexists_tac ‘(Read fd, NONE)’ >> simp[])
      >> pop_assum mp_tac >> qpat_x_assum ‘MAP _ tt1 = _’ (fn th => REWRITE_TAC[th])
      >> simp[MEM_MAP, EXISTS_PROD])
  >> simp[reads_c_def] >> qexists_tac ‘bufsz’
  >> qpat_x_assum ‘MAP _ tt2 = _’ (SUBST1_TAC o SYM)
  >> simp[MEM_MAP] >> qexists_tac ‘(Read fd, NONE)’ >> simp[sfa_def]
QED

(* ------------------------------------------------------------------------
   Accepts
   ------------------------------------------------------------------------ *)

(* If the server's accepts of lfd grew between rounds i and i + d, it
   emitted an accept of lfd in one of the rounds i+1 .. i+d *)
Theorem sw_naccepts_step:
  ∀d. hok hf ∧ naccepts lfd (server_with hf lfd (TAKE i h)).actions <
      naccepts lfd (server_with hf lfd (TAKE (i + d) h)).actions ⇒
      ∃k. i < k ∧ k ≤ i + d ∧
          MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) (TAKE k h))
Proof
  Induct >- simp[] >> rpt strip_tac
  >> Cases_on ‘naccepts lfd (server_with hf lfd (TAKE i h)).actions <
               naccepts lfd (server_with hf lfd (TAKE (i + d) h)).actions’
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
  >> ‘(server_with hf lfd (TAKE (i + d) h ++ [EL (i + d) h])).actions =
      (server_with hf lfd (TAKE (i + d) h)).actions ++
      new_actions (log_of (server_with hf lfd)) (TAKE (i + d) h ++ [EL (i + d) h])’
       by (qspecl_then [‘log_of (server_with hf lfd)’, ‘TAKE (i + d) h’, ‘EL (i + d) h’] mp_tac
             (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
           >> simp[log_of_def, wf_SNOC_actions, hok_wf_server_with])
  >> gvs[naccepts_def, echoProgressTheory.count_def, FILTER_APPEND_DISTRIB] >> CCONTR_TAC
  >> ‘FILTER (λa. a = Accept lfd)
        (new_actions (log_of (server_with hf lfd)) (TAKE (i + d) h ++ [EL (i + d) h])) = []’
       by simp[FILTER_EQ_NIL, EVERY_MEM]
  >> gvs[]
QED


(* MAIN: while connections are pending (the listener is ready), the server
   accepts in one of the next two rounds *)
Theorem sw_accept_soon_s:
  hok hf ∧ uses_ok lfdn (server_with hf lfdn) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  (∀j. n < j ∧ j ≤ n + 2 ⇒
       is_ready (gstate (EI lfdn) (srelabel (server_with hf lfdn)) s0 j) (n2w lfdn)) ⇒
  ∃i. 1 ≤ i ∧ i ≤ 2 ∧
      MEM (loopPollWorld$Accept (n2w lfdn)) (SAg (server_with hf lfdn) (EI lfdn) s0 (n + i))
Proof
  rpt strip_tac
  >> ‘grun_ok (EI lfdn) (srelabel (server_with hf lfdn)) s0’ by (irule gen_grun_ok >> metis_tac[])
  (* the model server sees the listener readable in snapshots n, n + 1 *)
  >> ‘∀j. n ≤ j ∧ j < n + 2 ⇒
          Readable lfdn ∈ (EL j (MAP sfs (ghist (EI lfdn) (srelabel (server_with hf lfdn)) s0 (n + 2)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> qexists_tac ‘n2w lfdn’ >> simp[]
           (* the listener is in the interest list *)
           >> irule interest_accepted >> simp[])
  >> qspecl_then [‘MAP sfs (ghist (EI lfdn) (srelabel (server_with hf lfdn)) s0 (n + 2))’, ‘n’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’] sw_accept_progress)
  >> impl_tac >- simp[prompt_ghist]
  >> ‘∀k. k ≤ n + 2 ⇒ TAKE k (MAP sfs (ghist (EI lfdn) (srelabel (server_with hf lfdn)) s0 (n + 2))) =
                       MAP sfs (ghist (EI lfdn) (srelabel (server_with hf lfdn)) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> strip_tac
  >> qspecl_then [‘2’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (EI lfdn) (srelabel (server_with hf lfdn)) s0 (n + 2))’] sw_naccepts_step)
  >> impl_tac >- simp[] >> strip_tac
  (* an accept of the model server is an accept of the socket program *)
  >> qexists_tac ‘k − n’ >> simp[]
  >> gvs[gacts_def, new_actions_relabel, MEM_MAP]
  >> qexists_tac ‘Accept lfdn’ >> simp[sfa_def]
QED

(* MAIN: a pending connection is eventually handed out to the server *)
Theorem sw_queue_progress:
  hok hf ∧ uses_ok lfdn (server_with hf lfdn) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k (gstate (EI lfdn) (srelabel (server_with hf lfdn)) s0 n) ⇒
        ∃N. MEM c (wacc (SPg (server_with hf lfdn) (EI lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (srelabel (server_with hf lfdn)) s0’ by (irule gen_grun_ok >> metis_tac[])
  >> completeInduct_on ‘k’ >> rpt strip_tac
  >> Cases_on ‘MEM c (wacc (SPg (server_with hf lfdn) (EI lfdn) s0 (n + 3)))’ >- metis_tac[]
  (* not handed out by round n + 3: still pending in rounds n .. n + 3 *)
  >> ‘∀d. d ≤ 3 ⇒ ∃k'. queued (n2w lfdn) c k' (gstate (EI lfdn) (srelabel (server_with hf lfdn)) s0 (n + d)) ∧
                       k' ≤ k’
       by (rpt strip_tac
           >> qspecl_then [‘EI lfdn’, ‘srelabel (server_with hf lfdn)’, ‘s0’, ‘n’, ‘n2w lfdn’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘l’, ‘c’] rounds_queued)
           >> simp[] >> disch_then (qspecl_then [‘d’, ‘k’] mp_tac) >> simp[]
           >> strip_tac >- (‘MEM c (wacc (SPg (server_with hf lfdn) (EI lfdn) s0 (n + 3)))’
                              suffices_by metis_tac[]
                            >> irule wacc_mono >> qexists_tac ‘d + n’ >> simp[])
           >> metis_tac[])
  (* so the server accepts in round n + 1 or n + 2 *)
  >> qspecl_then [‘s0’, ‘lfdn’, ‘n’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘n’] sw_accept_soon_s)
  >> impl_tac
  >- (simp[] >> rpt strip_tac
      >> first_x_assum (qspec_then ‘j − n’ mp_tac) >> simp[] >> strip_tac
      >> ‘n + (j − n) = j’ by simp[] >> gvs[] >> metis_tac[queued_ready])
  >> strip_tac
  (* which moves c forward *)
  >> first_assum (qspec_then ‘i’ mp_tac) >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘EI lfdn’, ‘srelabel (server_with hf lfdn)’, ‘s0’, ‘n2w lfdn’, ‘c’, ‘k'’, ‘n + i’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘l’, ‘c’, ‘k’, ‘n’] round_queued)
  >> simp[] >> strip_tac >- metis_tac[]
  >> ‘0 < nacc (n2w lfdn) (SAg (server_with hf lfdn) (EI lfdn) s0 (i + n))’
       by (gvs[nacc_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >> metis_tac[])
  >> qpat_x_assum ‘∀m. m < k ⇒ _’ (qspec_then ‘k''’ mp_tac) >> impl_tac >- fs[]
  >> disch_then (qspec_then ‘SUC (i + n)’ mp_tac) >> fs[]
QED

(* MAIN: every connection of the world is eventually handed out to the
   server *)
Theorem sw_conn_accepted:
  hok hf ∧ uses_ok lfdn (server_with hf lfdn) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  is_conn (gstate (EI lfdn) (srelabel (server_with hf lfdn)) s0 n) c ⇒
  ∃N. MEM c (wacc (SPg (server_with hf lfdn) (EI lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (srelabel (server_with hf lfdn)) s0’ by (irule gen_grun_ok >> metis_tac[])
  >> qspecl_then [‘EI lfdn’, ‘srelabel (server_with hf lfdn)’, ‘s0’, ‘n2w lfdn’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfd’] grounds_known)
  >> simp[] >> disch_then (qspec_then ‘n’ (strip_assume_tac o CONJUNCT2))
  >> fs[known_def] >> first_x_assum drule >> strip_tac >- metis_tac[]
  >> qpat_x_assum ‘MEM c (lq _ _)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’] mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘c’] sw_queue_progress)
  >> impl_tac >- fs[] >> disch_then irule
  >> qexistsl_tac [‘LENGTH l1’, ‘n’] >> simp[queued_def] >> metis_tac[]
QED
