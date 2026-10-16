(*
  A variant of the library's per-handler obligation, for handlers whose
  output owed for D is only known up to how it is split into writes (echo
  writes back whatever chunks it reads): handler_live_flat compares the
  concatenations.  handler_live implies it, and server_with_live_flat is
  server_with_live for it (design/34 §2.3).

  Also generic helpers for proving handler obligations:
   - hread_mono: what a handler has read only grows;
   - new_action_unanswered: an action of the current round is unanswered
     in the transcript;
   - nreads_step_wf: if a computation's reads of fd grew, it emitted a read
     of fd in one of those rounds.
*)
Theory skeletonLiveFlat
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words string
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  echoProgress socketWorld socketFair EchoSpec HttpGetSpec
  loopRounds loopRoundsTrans echoLiveProg echoLiveReadSoon echoLiveDrain
  echoLiveSched echoLiveAccount echoLiveAcceptSoon
  skeletonRunOk skeleton skeletonProgress skeletonSock echoClosedLoop
  skeletonLive
Libs
  preamble

(* The per-handler obligation, up to how the output is split into writes *)
Definition handler_live_flat_def:
  handler_live_flat hf out B ⇔
    ∀fd g j0 D.
      prompt (hf fd) g ∧ henv fd (hf fd) g j0 D ∧ j0 + B D ≤ LENGTH g ⇒
      ∃j. j ≤ LENGTH g ∧ FLAT (out D) ≼ FLAT (written fd (trans (hf fd) (TAKE j g)))
End

Theorem handler_live_flat_of_live:
  handler_live hf out B ⇒ handler_live_flat hf out B
Proof
  rw[handler_live_def, handler_live_flat_def] >> first_x_assum drule_all >>
  strip_tac >> qexists_tac ‘j’ >> simp[] >>
  qpat_x_assum ‘out D ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* MAIN: sw_accepted_live for handler_live_flat *)
Theorem sw_accepted_live_flat:
  hok hf ∧ handler_live_flat hf out B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  interest_covers ifds (SWM hf lfdn) s0 ∧
  MEM c (wacc (SWP hf ifds lfdn s0 n)) ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼ bytes_written_to c (FLAT (GENLIST (SWEV hf ifds lfdn s0) N))
Proof
  strip_tac >>
  ‘∃a g. a ≤ n ∧ LENGTH g + a = n + B D ∧ prompt (hf (w2n c)) g ∧
         henv (w2n c) (hf (w2n c)) g (n − a) D ∧
         ∀j. j ≤ LENGTH g ⇒
           bytes (FLAT (written (w2n c) (trans (hf (w2n c)) (TAKE j g)))) =
             bytes_written_to c (FLAT (GENLIST (SWEV hf ifds lfdn s0) (SUC (a + j))))’
    by (‘n ≤ n + B D’ by simp[] >> assume_tac (REWRITE_RULE [bytes_def] (GEN_ALL sw_view_henv)) >>
        fs[bytes_def] >> metis_tac[]) >>
  qpat_x_assum ‘handler_live_flat _ _ _’ (mp_tac o REWRITE_RULE [handler_live_flat_def]) >>
  disch_then (qspecl_then [‘w2n c’, ‘g’, ‘n − a’, ‘D’] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  qexists_tac ‘SUC (a + j)’ >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  qpat_x_assum ‘CONCAT (out D) ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >>
  rw[bytes_def] >> metis_tac[MAP_APPEND]
QED

(* MAIN: server_with_live for handler_live_flat *)
Theorem server_with_live_flat:
  hok hf ∧ handler_live_flat hf out B ∧ FLAT (out "") = "" ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ∧ bytes D ≼ sent_upto c n s0 ⇒
  ∃N. bytes (FLAT (out D)) ≼
      bytes_written_to c (FLAT (GENLIST (SWEV hf (EI lfdn) lfdn s0) N))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (SWM hf lfdn) s0’ by metis_tac[grun_ok_sw] >>
  ‘uses_ok lfdn (server_with hf lfdn)’ by metis_tac[uses_ok_sw] >>
  Cases_on ‘D = ""’
  >- (qexists_tac ‘0’ >> gvs[bytes_def]) >>
  ‘sent_upto c n s0 ≠ []’ by (strip_tac >> Cases_on ‘D’ >> fs[bytes_def]) >>
  ‘is_conn (SWG hf (EI lfdn) lfdn s0 n) c’
    by (drule_all grounds_acct >> disch_then (qspecl_then [‘c’, ‘n’] mp_tac) >>
        simp[acct_def, is_conn_def] >> CASE_TAC >> simp[]) >>
  ‘∃N0. MEM c (wacc (SWP hf (EI lfdn) lfdn s0 N0))’
    by (irule sw_conn_accepted >> simp[] >> metis_tac[]) >>
  ‘MEM c (wacc (SWP hf (EI lfdn) lfdn s0 (n + N0)))’
    by (irule wacc_mono >> qexists_tac ‘N0’ >> simp[]) >>
  ‘bytes D ≼ sent_upto c (n + N0) s0’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c n s0’ >>
        simp[sent_upto_prefix]) >>
  irule (Q.INST [‘n’ |-> ‘n + N0 : num’, ‘ifds’ |-> ‘EI lfdn’] sw_accepted_live_flat) >>
  simp[interest_covers_EI] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Helpers for handler obligations
   ------------------------------------------------------------------------ *)

Theorem read_zipr_NIL_flat[local]:
  ∀acts. read fd (zipr acts []) = []
Proof
  Induct >> simp[zipr_def] >> Cases >> simp[]
QED

Theorem read_trans_SNOC:
  read fd (trans m h) ≼ read fd (trans m (h ++ [s]))
Proof
  ‘trans m h = FLAT (GENLIST (round_trans m h) (LENGTH h)) ++
               zipr (new_actions (log_of m) h) []’
    by (REWRITE_TAC[trans_def, GENLIST, SNOC_APPEND, FLAT_APPEND, FLAT, APPEND_NIL] >>
        simp[round_trans_def, responses_at_def]) >>
  pop_assum SUBST1_TAC >> simp[trans_SNOC, read_zipr_NIL_flat] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]
QED

(* MAIN (helper): what a handler has read only grows *)
Theorem hread_mono:
  ∀k j. j ≤ k ⇒ hread fd h g j ≼ hread fd h g k
Proof
  Induct >- simp[] >> rpt strip_tac >>
  Cases_on ‘j = SUC k’ >- simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘hread fd h g k’ >> simp[] >>
  Cases_on ‘k < LENGTH g’
  >- (‘TAKE (SUC k) g = TAKE k g ++ [EL k g]’ by simp[GSYM SNOC_EL_TAKE, SNOC_APPEND] >>
      simp[hread_def] >> irule (iffRL IS_PREFIX_APPEND) >>
      qspecl_then [‘fd’, ‘h’, ‘TAKE k g’, ‘EL k g’] mp_tac
        (Q.GENL [‘fd’, ‘m’, ‘h’, ‘s’] read_trans_SNOC) >>
      rw[IS_PREFIX_APPEND] >> simp[] >> metis_tac[]) >>
  simp[hread_def, TAKE_LENGTH_TOO_LONG]
QED

(* MAIN (helper): an action of the current round is unanswered *)
Theorem new_action_unanswered:
  MEM a (new_actions (log_of m) h) ⇒ MEM (a, NONE) (trans m h)
Proof
  rw[trans_def, MEM_FLAT, MEM_GENLIST] >>
  qexists_tac ‘zipr (new_actions (log_of m) h) []’ >>
  conj_tac >- (qexists_tac ‘LENGTH h’ >> simp[round_trans_def, responses_at_def]) >>
  pop_assum mp_tac >> qspec_tac (‘new_actions (log_of m) h’, ‘l’) >>
  Induct >> simp[zipr_def] >> metis_tac[]
QED

(* MAIN (helper): if m's reads of fd grew between rounds i and i + d, it
   emitted a read of fd in one of the rounds i+1 .. i+d *)
Theorem nreads_step_wf:
  ∀d. wf m ∧ nreads fd (m (TAKE i h)).actions < nreads fd (m (TAKE (i + d) h)).actions ⇒
      ∃k. i < k ∧ k ≤ i + d ∧ MEM (Read fd) (new_actions (log_of m) (TAKE k h))
Proof
  Induct >- simp[] >> rpt strip_tac >>
  Cases_on ‘nreads fd (m (TAKE i h)).actions < nreads fd (m (TAKE (i + d) h)).actions’
  >- (first_x_assum drule_all >> strip_tac >> qexists_tac ‘k’ >> simp[]) >>
  qexists_tac ‘i + SUC d’ >> simp[] >>
  ‘i + SUC d ≤ LENGTH h’
    by (CCONTR_TAC >>
        ‘TAKE (i + SUC d) h = h ∧ TAKE (i + d) h = h’ by simp[TAKE_LENGTH_TOO_LONG] >>
        gvs[]) >>
  ‘TAKE (i + SUC d) h = TAKE (i + d) h ++ [EL (i + d) h]’
    by (‘i + SUC d = SUC (i + d)’ by simp[] >> pop_assum SUBST1_TAC >>
        simp[GSYM SNOC_EL_TAKE, SNOC_APPEND]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘(m (TAKE (i + d) h ++ [EL (i + d) h])).actions =
   (m (TAKE (i + d) h)).actions ++
   new_actions (log_of m) (TAKE (i + d) h ++ [EL (i + d) h])’
    by (qspecl_then [‘log_of m’, ‘TAKE (i + d) h’, ‘EL (i + d) h’] mp_tac
          (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix) >>
        simp[log_of_def, wf_SNOC_actions]) >>
  gvs[nreads_def, FILTER_APPEND_DISTRIB] >> CCONTR_TAC >>
  ‘FILTER (λa. a = Read fd)
     (new_actions (log_of m) (TAKE (i + d) h ++ [EL (i + d) h])) = []’
    by simp[FILTER_EQ_NIL, EVERY_MEM] >>
  gvs[]
QED
