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
