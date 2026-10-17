(*
  D26: the echo reads only handles it was handed (honest-ffi's
  reads_accepted, the server half of S1_live / live_held).  On any history,
  every Read the echo server emits is on a handle some earlier snapshot
  returned as Accepted.  In the model (asyncServerSafety's server_echoes,
  without its freshness hypothesis): every fd the server touches is one it
  accepted; the transcript's responses are snapshot results; and the
  socket vocabulary (srelabel) maps reads and accepts one to one.

  MAIN: echo_reads_accepted.
*)
Theory honestEchoReadsAcc
Ancestors
  asyncServerSafety asyncTranscript asyncServer asyncLevel2 asyncLevel1 asyncCore
  asyncM4SockModel asyncM4Relabel asyncM4RelabelDist asyncM3World
Libs
  preamble

(* ------------------------------------------------------------------------
   Transcripts
   ------------------------------------------------------------------------ *)

Theorem zipr_NIL[local]:
  ∀as. zipr as [] = MAP (λa. (a, NONE)) as
Proof
  Induct >> simp[zipr_def]
QED

Theorem zipr_mem_some[local]:
  ∀as rs. MEM (a, SOME r) (zipr as rs) ⇒ MEM r rs
Proof
  Induct >> simp[zipr_def] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[zipr_NIL, MEM_MAP] >>
  rw[] >> gvs[]
QED

(* A response in the transcript is a snapshot's result *)
Theorem trans_resp:
  MEM (a, SOME r) (trans m h) ⇒ ∃s. MEM s h ∧ MEM r s.results
Proof
  rw[trans_def, MEM_FLAT, MEM_GENLIST, round_trans_def] >>
  drule zipr_mem_some >> rw[responses_at_def] >> metis_tac[EL_MEM]
QED

(* This round's new actions are in the transcript, unanswered *)
Theorem new_trans:
  MEM a (new_actions (log_of m) h) ⇒ MEM (a, NONE) (trans m h)
Proof
  rw[trans_def, MEM_FLAT, MEM_GENLIST, round_trans_def] >>
  qexists_tac ‘zipr (new_actions (log_of m) h) []’ >>
  simp[zipr_NIL, MEM_MAP] >>
  qexists_tac ‘LENGTH h’ >> simp[responses_at_def, zipr_NIL]
QED

Theorem accepted_resp:
  MEM fd (accepted (trans m h)) ⇒ ∃s. MEM s h ∧ MEM (Accepted fd) s.results
Proof
  rw[accepted_def, MEM_FLAT, MEM_MAP] >>
  rename1 ‘MEM p (trans m h)’ >> PairCases_on ‘p’ >> gvs[] >>
  Cases_on ‘p0’ >> gvs[] >> Cases_on ‘p1’ >> gvs[] >>
  rename1 ‘MEM (_, SOME x) _’ >> Cases_on ‘x’ >> gvs[] >>
  drule trans_resp >> simp[]
QED

(* ------------------------------------------------------------------------
   The model server: it touches only fds it accepted
   ------------------------------------------------------------------------ *)

Theorem EXISTS_FILTER[local]:
  ∀l. EXISTS P l ⇔ FILTER P l ≠ []
Proof
  Induct >> rw[]
QED

Theorem handler_no_accept[local]:
  FILTER is_accept (trans (handler fd) h) = []
Proof
  qspecl_then [‘fd’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes)
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> gvs[on_fd_def, is_accept_def]
QED

Theorem handler_only_fd[local]:
  g ≠ fd ⇒ FILTER (on_fd g) (trans (handler fd) h) = []
Proof
  qspecl_then [‘fd’, ‘h’] mp_tac (Q.GEN ‘fd’ handler_echoes)
  >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac
  >> first_x_assum drule >> gvs[on_fd_def]
QED

(* MAIN (model): server_echoes' second half, on any history *)
Theorem server_touches_accepted:
  ∀h fd. EXISTS (on_fd fd) (trans (server lfd) h) ⇒
         MEM fd (accepted (trans (server lfd) h))
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’
  >> ONCE_REWRITE_TAC[server_unfold]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable lfd) K0) h’
  >> qspecl_then [‘readable lfd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (Accept lfd)) K1) h2’
  >> qspecl_then [‘emit (Accept lfd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- simp[trans_emit]
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’]
  >> reverse (Cases_on ‘res’) >> simp[]
  >> TRY (rpt strip_tac >> first_x_assum (qspec_then ‘h2'’ mp_tac) >> simp[] >> NO_TAC)
  >> rename1 ‘Accepted fd’
  >> qabbrev_tac ‘L = left_view (handler fd) (server lfd) h2'’
  >> qabbrev_tac ‘R = right_view (handler fd) (server lfd) h2'’
  >> ‘LENGTH R < LENGTH h1 + (LENGTH h2' + 1)’ by simp[Abbr ‘R’]
  >> ‘accepted (trans (both (handler fd) (server lfd)) h2') =
      accepted (trans (server lfd) R)’
       by (ONCE_REWRITE_TAC[GSYM accepted_FILTER] >> AP_TERM_TAC
           >> simp[Abbr ‘R’] >> irule trans_both_filter_right
           >> simp[handler_no_accept])
  >> ‘∀g. g ≠ fd ⇒
          FILTER (on_fd g) (trans (both (handler fd) (server lfd)) h2') =
          FILTER (on_fd g) (trans (server lfd) R)’
       by (rpt strip_tac >> simp[Abbr ‘R’] >> irule trans_both_filter_right
           >> simp[handler_only_fd])
  >> rpt strip_tac >> Cases_on ‘fd' = fd’ >> simp[]
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[] >> disch_then irule
  >> gvs[EXISTS_FILTER]
QED

(* ------------------------------------------------------------------------
   The socket vocabulary
   ------------------------------------------------------------------------ *)

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

(* MAIN: honest-ffi's reads_accepted for the echo *)
Theorem echo_reads_accepted:
  ∀hh h k. MEM (Read h k) (new_actions (log_of (srelabel (server lfdn))) hh) ⇒
           ∃s. MEM s hh ∧ MEM (Accepted (SOME h)) s.results
Proof
  rw[new_actions_relabel, MEM_MAP] >>
  qpat_x_assum ‘Read _ _ = sfa _’ (assume_tac o SYM) >>
  drule sfa_read >> strip_tac >> gvs[] >>
  drule new_trans >> strip_tac >>
  ‘EXISTS (on_fd fd) (trans (server lfdn) (MAP sfs hh))’
    by (simp[EXISTS_MEM] >> first_x_assum (irule_at Any) >> simp[on_fd_def]) >>
  drule server_touches_accepted >> strip_tac >>
  drule accepted_resp >> rw[MEM_MAP] >>
  gvs[snap_map_def, MEM_MAP] >>
  qpat_x_assum ‘Accepted _ = sfr _’ (assume_tac o SYM) >>
  drule sfr_accepted >> strip_tac >> gvs[] >>
  first_x_assum (irule_at Any) >> simp[]
QED
