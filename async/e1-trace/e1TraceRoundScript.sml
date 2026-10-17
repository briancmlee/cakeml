(*
  The shared E1 trace layer (m4-server's part (c)): prefixes INSIDE a
  round.  A finite prefix of start ++ rounds either lies in the start or
  is sandwiched between two consecutive round boundaries (round_sandwich);
  and an episode's sent and received bytes (ep_io, any selector) only grow
  along prefixes (ep_io_mono).  So at a mid-round prefix, episode j has
  sent at most what it has sent by the end of the round, and received at
  least what it had received by the start of the round: the clauses of a
  per-prefix claim reduce to the round boundaries of e1TraceRead /
  moonshotSentGlue.
*)
Theory e1TraceRound
Ancestors
  l0sysEpisodes rich_list
Libs
  preamble

(* Episodes' bytes grow along prefixes *)
Theorem ep_io_mono:
  ∀xs ys opn n. xs ≼ ys ⇒ ep_io sel j opn n xs ≼ ep_io sel j opn n ys
Proof
  Induct >- simp[ep_io_def] >>
  rpt gen_tac >> Cases_on ‘ys’ >> simp[ep_io_def] >> strip_tac >> gvs[] >>
  CASE_TAC >> simp[] >> TRY (PairCases_on ‘x’ >> simp[])
QED

Theorem l0_ep_sent_mono:
  xs ≼ ys ⇒ l0_ep_sent j xs ≼ l0_ep_sent j ys
Proof
  simp[l0_ep_sent_def, ep_io_mono]
QED

Theorem l0_ep_recvd_mono:
  xs ≼ ys ⇒ l0_ep_recvd j xs ≼ l0_ep_recvd j ys
Proof
  simp[l0_ep_recvd_def, ep_io_mono]
QED

Theorem rounds_prefix_SUC:
  pre ++ FLAT (GENLIST f n) ≼ pre ++ FLAT (GENLIST f (SUC n))
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

Theorem rounds_prefix_mono:
  i ≤ n ⇒ pre ++ FLAT (GENLIST f i) ≼ pre ++ FLAT (GENLIST f n)
Proof
  Induct_on ‘n’ >> simp[] >> rpt strip_tac >>
  Cases_on ‘i = SUC n’ >- simp[] >>
  ‘i ≤ n’ by simp[] >> first_x_assum drule >>
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND, IS_PREFIX_APPEND] >> strip_tac >>
  rename1 ‘_ = _ ++ l’ >> qexists_tac ‘l ++ f n’ >> simp[]
QED

(* A prefix within n rounds is in the start, or between rounds i and i + 1 *)
Theorem round_sandwich:
  ∀n. evs ≼ pre ++ FLAT (GENLIST f n) ⇒
      evs ≼ pre ∨
      ∃i. i < n ∧ pre ++ FLAT (GENLIST f i) ≼ evs ∧ evs ≼ pre ++ FLAT (GENLIST f (SUC i))
Proof
  Induct >- simp[] >> strip_tac >>
  Cases_on ‘evs ≼ pre ++ FLAT (GENLIST f n)’
  >- (first_x_assum drule >> strip_tac >> simp[] >> disj2_tac >>
      qexists_tac ‘i’ >> simp[]) >>
  disj2_tac >> qexists_tac ‘n’ >> simp[] >>
  ‘pre ++ FLAT (GENLIST f n) ≼ pre ++ FLAT (GENLIST f (SUC n))’
    by simp[rounds_prefix_SUC] >>
  metis_tac[prefixes_is_prefix_total]
QED
