(*
  SQ part (1): once L1 fetches nothing more, it drains.  On the PF run,
  if from some round on the fetch log is empty, then eventually, for good,
  no connection waits to be handed out, and every fd L1 holds has an empty
  inbox and no pending end-of-file — given the server facts that make it
  so: S2 (a pending connection is accepted), S3w (an inbox no longer
  fetched empties) and that an fd at end-of-file is eventually read (its
  read auto-closes it, taking it out of L1's table).

  Without fetches the table's fds and the end-of-file list only shrink
  (once nothing waits to be handed out), so each finite set settles.

  MAIN: pf_drain.
*)
Theory honestL1BQuietDrain
Ancestors
  pred_set honestL0 honestL0World honestL1Model honestL1PFModel honestL1PFLive
  honestL1PFConnRun honestL1PFRound honestL1PFS4w honestL1BSettle honestL1BFetchStop
Libs
  preamble

(* ------------------------------------------------------------------------
   Without fetches, no end-of-file appears
   ------------------------------------------------------------------------ *)

Theorem pdo_eof_sub:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ ∀f. MEM f ps'.eof ⇒ MEM f ps.eof
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[set_inb_def, MEM_FILTER] >>
  PairCases_on ‘z’ >> gvs[MEM_FILTER]
QED

Theorem pacts_eof_sub:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ ∀f. MEM f ps'.eof ⇒ MEM f ps.eof
Proof
  Induct >> simp[pacts_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> metis_tac[pdo_eof_sub]
QED

Theorem fetch_eof_sub:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ log = [] ⇒
    ∀f. MEM f ps'.eof ⇒ MEM f ps.eof
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >> gvs[AllCaseEqs()]
  >> TRY (res_tac >> NO_TAC)
  >> Cases_on ‘l0_res_of out’ >> gvs[AllCaseEqs()]
  >> TRY (qpat_x_assum ‘(λ(ps1,fl). _) _ = _’ mp_tac >> rw[] >> gvs[AllCaseEqs()])
  >> TRY (Cases_on ‘e = E_MFILE’) >> gvs[] >> res_tac >> fs[]
QED

Theorem stall_step_fields[local,simp]:
  (stall_step hfs ob log ps).eof = ps.eof ∧ (stall_step hfs ob log ps).inb = ps.inb ∧
  (stall_step hfs ob log ps).acq = ps.acq
Proof
  simp[stall_step_def]
QED

Theorem tail_eof_sub:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ log = [] ⇒
  ∀f. MEM f ps'.eof ⇒ MEM f ps.eof
Proof
  rw[pf_tail_def, AllCaseEqs()] >> gvs[] >>
  drule fetch_eof_sub >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Without fetches, an empty inbox stays empty
   ------------------------------------------------------------------------ *)

Theorem pdo_inb_nil:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ inb_of ps f = [] ⇒ inb_of ps' f = []
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[inb_of_set_inb] >>
  TRY (PairCases_on ‘z’) >> gvs[inb_of_def] >> rw[] >> gvs[]
QED

Theorem pacts_inb_nil:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ inb_of ps f = [] ⇒ inb_of ps' f = []
Proof
  Induct >> simp[pacts_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> metis_tac[pdo_inb_nil]
QED

Theorem fetch_inb_nil:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ log = [] ∧ inb_of ps f = [] ⇒
    inb_of ps' f = []
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >> gvs[AllCaseEqs()]
  >> TRY (res_tac >> NO_TAC)
  >> Cases_on ‘l0_res_of out’ >> gvs[AllCaseEqs()]
  >> TRY (qpat_x_assum ‘(λ(ps1,fl). _) _ = _’ mp_tac >> rw[] >> gvs[AllCaseEqs()])
  >> TRY (Cases_on ‘e = E_MFILE’) >> gvs[]
  >> first_x_assum (drule_then irule) >> fs[inb_of_def]
QED

Theorem tail_inb_nil:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ log = [] ∧
  inb_of ps f = [] ⇒ inb_of ps' f = []
Proof
  rw[pf_tail_def, AllCaseEqs()] >> gvs[] >>
  drule fetch_inb_nil >> simp[] >> disch_then irule >> fs[inb_of_def]
QED

(* ------------------------------------------------------------------------
   One round of the run
   ------------------------------------------------------------------------ *)

Theorem round_split[local]:
  run_ok lfd pol ifds m w0 ⇒
  ∃rs evs w1 ps1 rdy tevs.
    pacts lfd (rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)
      (new_actions (log_of m) (rhist lfd pol ifds m w0 k)) = SOME (rs, evs, (w1, ps1)) ∧
    pf_tail lfd pol (ifds (rhist lfd pol ifds m w0 k)) (w1, ps1) =
      SOME (rdy, (rworld lfd pol ifds m w0 (SUC k), rstate lfd pol ifds m w0 (SUC k)),
            rlog lfd pol ifds m w0 k, tevs)
Proof
  strip_tac >> drule prun_round' >>
  disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  gvs[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >> metis_tac[]
QED

Theorem round_eof_sub:
  run_ok lfd pol ifds m w0 ∧ rlog lfd pol ifds m w0 k = [] ∧
  MEM f (rstate lfd pol ifds m w0 (SUC k)).eof ⇒ MEM f (rstate lfd pol ifds m w0 k).eof
Proof
  strip_tac >> drule (Q.GEN ‘k’ round_split) >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule tail_eof_sub >> simp[] >> disch_then drule >> strip_tac >>
  drule pacts_eof_sub >> metis_tac[]
QED

Theorem round_inb_nil:
  run_ok lfd pol ifds m w0 ∧ rlog lfd pol ifds m w0 k = [] ∧
  inb_of (rstate lfd pol ifds m w0 k) f = [] ⇒ inb_of (rstate lfd pol ifds m w0 (SUC k)) f = []
Proof
  strip_tac >> drule (Q.GEN ‘k’ round_split) >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  fs[] >> ‘inb_of ps1 f = []’ by (drule pacts_inb_nil >> fs[]) >>
  drule tail_inb_nil >> fs[]
QED

Theorem round_tbl_sub:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  (rstate lfd pol ifds m w0 k).acq = [] ∧
  MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl) ⇒
  MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl)
Proof
  strip_tac >> drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘ALL_DISTINCT (MAP SND (rstate lfd pol ifds m w0 k).b.tbl)’
    by fs[honestL1PFRefineTheory.pown_def, ALL_DISTINCT_APPEND] >>
  drule (Q.GEN ‘k’ round_split) >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule tail_noeof >> strip_tac >>
  drule_all pacts_noeof >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The drain
   ------------------------------------------------------------------------ *)

(* Eventually, uniformly over a finite set *)
Theorem finite_eventually[local]:
  ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ ∃n:num. ∀k. n ≤ k ⇒ P x k) ⇒
      ∃N:num. ∀x k. x ∈ s ∧ N ≤ k ⇒ P x k
Proof
  Induct_on ‘FINITE’ >> rw[] >>
  first_assum (qspec_then ‘e’ mp_tac) >> impl_tac >- simp[] >>
  disch_then (qx_choose_then ‘n1’ assume_tac) >>
  ‘∃N. ∀x k. x ∈ s ∧ N ≤ k ⇒ P x k’ by (first_x_assum irule >> metis_tac[]) >>
  qexists_tac ‘MAX n1 N’ >> rw[] >> gvs[MAX_LE]
QED

(* MAIN: the drain *)
Theorem pf_drain:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  S2 lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  (∀n f. n0 ≤ n ∧ (∀k. n ≤ k ⇒ (rstate lfd pol ifds m w0 k).acq = []) ∧
         MEM f (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∧
         MEM f (rstate lfd pol ifds m w0 n).eof ∧ inb_of (rstate lfd pol ifds m w0 n) f = [] ⇒
         ∃n'. n ≤ n' ∧ ¬MEM f (MAP SND (rstate lfd pol ifds m w0 n').b.tbl)) ∧
  (∀n. n0 ≤ n ⇒ rlog lfd pol ifds m w0 n = []) ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
       (rstate lfd pol ifds m w0 n).acq = [] ∧
       ∀h f. ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ⇒
             inb_of (rstate lfd pol ifds m w0 n) f = [] ∧ ¬MEM f (rstate lfd pol ifds m w0 n).eof
Proof
  strip_tac >>
  qabbrev_tac ‘st = rstate lfd pol ifds m w0’ >>
  (* nothing more waits to be handed out *)
  ‘∃N1. n0 ≤ N1 ∧ ∀k. N1 ≤ k ⇒ (st k).acq = []’
    by (simp[Abbr ‘st’] >> irule acq_empty >> simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]) >>
  (* the table's fds only shrink, so they settle *)
  qabbrev_tac ‘TT = λk. set (MAP SND (st k).b.tbl)’ >>
  ‘∀k. N1 ≤ k ⇒ TT (SUC k) ⊆ TT k’
    by (rw[Abbr ‘TT’, SUBSET_DEF] >> qunabbrev_tac ‘st’ >> irule round_tbl_sub >> simp[]) >>
  ‘∃KK. N1 ≤ KK ∧ ∀k. KK ≤ k ⇒ CARD (TT k) = CARD (TT KK)’
    by (qspecl_then [‘λk. CARD (TT k)’, ‘N1’] mp_tac (Q.GENL [‘f’, ‘K0’] noninc_stable) >>
        simp[] >> impl_tac >- (rw[] >> irule CARD_SUBSET >> simp[Abbr ‘TT’]) >> simp[]) >>
  ‘∀d. TT (KK + d) = TT KK’
    by (Induct >> simp[] >>
        ‘TT (SUC (KK + d)) ⊆ TT (KK + d)’ by simp[] >>
        ‘CARD (TT (SUC (KK + d))) = CARD (TT (KK + d))’
          by (first_assum (qspec_then ‘SUC (KK + d)’ mp_tac) >>
              first_x_assum (qspec_then ‘KK + d’ mp_tac) >> simp[]) >>
        ‘FINITE (TT (KK + d))’ by simp[Abbr ‘TT’] >>
        metis_tac[SUBSET_EQ_CARD, ADD_CLAUSES, SUBSET_FINITE]) >>
  ‘∀k. KK ≤ k ⇒ TT k = TT KK’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘k − KK’ mp_tac) >> simp[]) >>
  (* each fd held from then on drains, for good *)
  ‘∀f. f ∈ TT KK ⇒ ∃n. ∀k. n ≤ k ⇒ inb_of (st k) f = [] ∧ ¬MEM f (st k).eof’
    by (rpt strip_tac >>
        ‘∃n'. KK ≤ n' ∧ inb_of (st n') f = []’
          by (qpat_x_assum ‘S3w _ _ _ _ _’ (mp_tac o REWRITE_RULE [S3w_def]) >>
              disch_then (qspecl_then [‘KK’, ‘f’] mp_tac) >> simp[Abbr ‘st’] >>
              impl_tac >- (rw[] >> fs[GSYM rlog_def, fetched_def]) >> rw[]) >>
        ‘∀d. inb_of (st (n' + d)) f = []’
          by (Induct >> simp[ADD_CLAUSES] >> qunabbrev_tac ‘st’ >>
              irule round_inb_nil >> ‘d + n' = n' + d’ by simp[] >> fs[] >>
              qpat_x_assum ‘∀n. n0 ≤ n ⇒ _’ irule >> simp[]) >>
        qexists_tac ‘n'’ >> rpt strip_tac
        >- (first_x_assum (qspec_then ‘k − n'’ mp_tac) >> simp[]) >>
        ‘inb_of (st k) f = []’ by (first_x_assum (qspec_then ‘k − n'’ mp_tac) >> simp[]) >>
        ‘f ∈ TT k’ by simp[] >>
        qpat_x_assum ‘∀n f. n0 ≤ n ∧ _ ⇒ _’ (qspecl_then [‘k’, ‘f’] mp_tac) >>
        impl_tac >- fs[Abbr ‘TT’, Abbr ‘st’] >> strip_tac >>
        ‘TT n'' = TT KK’ by simp[] >>
        fs[Abbr ‘TT’, Abbr ‘st’]) >>
  ‘FINITE (TT KK)’ by simp[Abbr ‘TT’] >>
  qspecl_then [‘λf k. inb_of (st k) f = [] ∧ ¬MEM f (st k).eof’, ‘TT KK’] mp_tac
    (Q.GEN ‘P’ finite_eventually) >>
  simp[] >> strip_tac >>
  qexists_tac ‘MAX N KK’ >> rpt strip_tac >> fs[MAX_LE] >>
  TRY (qpat_x_assum ‘∀k. N1 ≤ k ⇒ _’ irule >> simp[] >> NO_TAC) >>
  ‘MEM (h, f) (st n).b.tbl’ by metis_tac[ALOOKUP_MEM] >>
  ‘MEM f (MAP SND (st n).b.tbl)’ by (simp[MEM_MAP] >> qexists_tac ‘(h, f)’ >> simp[]) >>
  ‘f ∈ TT n’ by (qunabbrev_tac ‘TT’ >> simp[] >> metis_tac[]) >>
  ‘f ∈ TT KK’ by metis_tac[] >> metis_tac[]
QED
