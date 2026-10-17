(*
  S4w from the server's side (moonshot step 8 (b)): if, from some round
  on, every Write on a handle of f carries no bytes, then S4w holds for f,
  for every hw.  The proof needs only the write timeout (D23): f's outbox
  never grows again, a round that leaves it non-empty and no shorter adds
  one to f's stall count, and at pf_sendwait the outbox is dropped; so it
  reaches [] and stays there.
*)
Theory honestL1PFS4w
Ancestors
  honestL1PFOutLive honestL1PFDead honestL1PFFlush honestL1PFOut
  honestL1PFConnRun honestL1PFConn honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFInv honestL1Inv
  honestL1PFModel honestL1Steps honestL1Props honestL1Model
  honestL0WorldInv honestL0Rely honestL0World honestL0 socketV2FFI asyncCore
Libs
  preamble

(* f's stall count (0 when it has none) *)
Definition scount_def:
  scount (ps : l1p) f = case ALOOKUP ps.stalls f of NONE => 0 | SOME n => n
End

(* ------------------------------------------------------------------------
   One round's tail: f's outbox does not grow, and a tail that leaves it
   non-empty and no shorter raises f's stall count by one
   ------------------------------------------------------------------------ *)

Theorem outbox_of_forget:
  outbox_of (forget g b) f = if f = g then [] else outbox_of b f
Proof
  simp[forget_def, outbox_of_set_outbox] >> rw[outbox_of_def]
QED

Theorem l1_reap_le:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ⇒
    (outbox_of b' f = outbox_of b f ∨ outbox_of b' f = []) ∧
    (MEM f b'.closing ⇒ MEM f b.closing) ∧ b'.tbl = b.tbl
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> gvs[l1_close_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  gvs[outbox_of_forget, forget_def, set_outbox_def, MEM_FILTER] >> rw[] >> gvs[]
QED

Theorem stall_step_up:
  MEM f (MAP SND ps.b.tbl ++ ps.b.closing) ∧ MEM f hfs ∧
  outbox_of ps.b f ≠ [] ∧ ¬(LENGTH (outbox_of ps.b f) < LENGTH (ob f)) ∧
  ¬MEM f (stall_drops hfs ob log ps) ⇒
  MEM (f, scount ps f + 1) (stall_step hfs ob log ps).stalls
Proof
  strip_tac >>
  qabbrev_tac ‘held = λf. MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing’ >>
  qabbrev_tac ‘hs0 = FILTER (λ(f, n). held f) ps.stalls ++
                     MAP (λf. (f, 0n)) (nub (FILTER (λf. held f ∧ ¬MEM f (MAP FST ps.stalls)) hfs))’ >>
  qabbrev_tac ‘G = λ(f, n). if MEM (FReset f) log then (f, pf_sendwait)
                            else if outbox_of ps.b f = [] ∨
                                    LENGTH (outbox_of ps.b f) < LENGTH (ob f) then (f, 0)
                            else (f, n + 1)’ >>
  ‘(stall_step hfs ob log ps).stalls = FILTER (λ(f, n). n < pf_sendwait) (MAP G hs0) ∧
   stall_drops hfs ob log ps = MAP FST (FILTER (λ(f, n). pf_sendwait ≤ n) (MAP G hs0))’
    by simp[stall_step_def, stall_drops_def, Abbr ‘G’, Abbr ‘hs0’, Abbr ‘held’] >>
  ‘held f’ by (qpat_x_assum ‘MEM f (_ ++ _)’ mp_tac >> simp[Abbr ‘held’]) >>
  ‘MEM (f, scount ps f) hs0’
    by (simp[Abbr ‘hs0’, scount_def] >> Cases_on ‘ALOOKUP ps.stalls f’ >>
        gvs[ALOOKUP_NONE, MEM_FILTER, MEM_MAP, MEM_nub] >>
        imp_res_tac ALOOKUP_MEM >> simp[]) >>
  ‘MEM (G (f, scount ps f)) (MAP G hs0)’ by (irule MEM_MAP_f >> first_assum ACCEPT_TAC) >>
  ‘G (f, scount ps f) =
   (f, if MEM (FReset f) log then pf_sendwait else scount ps f + 1)’
    by (simp[Abbr ‘G’] >> rw[] >> fs[]) >>
  qpat_x_assum ‘¬MEM f (stall_drops _ _ _ _)’ mp_tac >>
  qpat_x_assum ‘stall_drops _ _ _ _ = _’ (fn th => rewrite_tac[th]) >>
  qpat_x_assum ‘(stall_step _ _ _ _).stalls = _’ (fn th => rewrite_tac[th]) >>
  simp[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> strip_tac >>
  qabbrev_tac ‘v = if MEM (FReset f) log then pf_sendwait else scount ps f + 1’ >>
  ‘¬(pf_sendwait ≤ v)’
    by (strip_tac >> first_x_assum (qspec_then ‘v’ mp_tac) >> asm_rewrite_tac[] >>
        simp[] >> qexistsl [‘f’, ‘scount ps f’] >> asm_rewrite_tac[] >>
        qpat_x_assum ‘G _ = _’ (fn th => rewrite_tac[GSYM th])) >>
  ‘v = if MEM (FReset f) log then pf_sendwait else scount ps f + 1’ by simp[Abbr ‘v’] >>
  ‘v = scount ps f + 1’
    by (Cases_on ‘MEM (FReset f) log’ >>
        qpat_x_assum ‘¬(pf_sendwait ≤ v)’ mp_tac >> qpat_x_assum ‘v = _’ mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum ‘v = if _ then _ else _’ kall_tac >>
  qpat_x_assum ‘Abbrev (v = _)’ kall_tac >>
  qpat_x_assum ‘v = scount ps f + 1’ SUBST_ALL_TAC >>
  conj_tac >- (qpat_x_assum ‘¬(_ ≤ _)’ mp_tac >> simp[]) >>
  qexistsl [‘f’, ‘scount ps f’] >> asm_rewrite_tac[] >>
  qpat_x_assum ‘G _ = _’ (fn th => rewrite_tac[GSYM th])
QED

Theorem tail_le:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒
  LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps.b f) ∧
  (MEM f (MAP SND ps'.b.tbl ++ ps'.b.closing) ∧ outbox_of ps'.b f ≠ [] ∧
   LENGTH (outbox_of ps'.b f) = LENGTH (outbox_of ps.b f) ⇒
   MEM (f, scount ps f + 1) ps'.stalls)
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l1_flush_le >> disch_then (qspec_then ‘f’ assume_tac) >>
  drule l1_flush_fields >> strip_tac >>
  drule pf_fetch_b >> strip_tac >> drule pf_fetch_stalls >> strip_tac >> gvs[] >>
  qabbrev_tac ‘dl = stall_drops (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  ‘outbox_of ps3.b f = (if MEM f dl then [] else outbox_of ps3'.b f) ∧
   ps3.b.tbl = ps3'.b.tbl ∧ ps3.b.closing = ps3'.b.closing’
    by simp[Abbr ‘ps3’, Abbr ‘dl’, stall_step_drops, honestL1PFModelTheory.FOLDL_drop_out] >>
  drule l1_reap_le >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  (conj_tac >- (Cases_on ‘MEM f dl’ >> gvs[])) >>
  rpt strip_tac >> TRY (gvs[] >> NO_TAC) >>
  ‘¬MEM f dl’ by (strip_tac >> gvs[]) >>
  ‘MEM f (pf_held ps3')’ by (gvs[pf_held_def] >> metis_tac[]) >>
  ‘scount ps3' f = scount ps f’ by simp[scount_def] >>
  qspecl_then [‘f’, ‘ps3'’, ‘pf_held ps3'’, ‘outbox_of ps.b’, ‘log’]
    mp_tac (Q.GENL [‘f’, ‘ps’, ‘hfs’, ‘ob’, ‘log’] stall_step_up) >>
  (impl_tac >- (gvs[Abbr ‘dl’] >> gvs[pf_held_def])) >>
  simp[Abbr ‘ps3’]
QED

(* ------------------------------------------------------------------------
   One round's actions: f's outbox grows only by a Write on a handle that
   names f at the start or at the end of the round.  A handle the round
   takes for f (an Accept of f from acq) is still f's at the end: f has no
   input yet, so no Read in the round can end it
   ------------------------------------------------------------------------ *)

(* f's handle h is clean: f has no input and h was numbered before nxt *)
Definition hclean_def:
  hclean lfd (ps : l1p) h f ⇔
    ALOOKUP ps.b.tbl h = SOME f ∧ ¬MEM f ps.eof ∧ inb_of ps f = [] ∧
    ∃i. i < ps.b.nxt ∧ h = l1hdl lfd i
End

(* What acq's fds are like (from pown at a round's start) *)
Definition ainv_def:
  ainv (ps : l1p) ⇔
    ALL_DISTINCT ps.acq ∧
    ∀g. MEM g ps.acq ⇒ ¬MEM g ps.eof ∧ inb_of ps g = [] ∧ ¬MEM g (MAP SND ps.b.tbl)
End

Theorem pown_ainv:
  pown lfd ps ⇒ ainv ps
Proof
  rw[pown_def, ainv_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem inb_of_set_inb:
  inb_of (set_inb g bs ps) f = if f = g then bs else inb_of ps f
Proof
  rw[set_inb_def, inb_of_def, ALOOKUP_ADELKEY] >> every_case_tac >> gvs[]
QED

Theorem l1hdl_fresh:
  i < j ∧ j + 1 < dimword (:64) ⇒ hdl lfd i ≠ hdl lfd j
Proof
  rpt strip_tac >> ‘i = j’ suffices_by simp[] >>
  irule (SIMP_RULE (srw_ss()) [] l1hdl_11) >>
  qexists_tac ‘lfd’ >> simp[SIMP_RULE (srw_ss()) [] l1hdln_lt] >> fs[]
QED

Theorem pdo_keep:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ hclean lfd ps h f ⇒
  hclean lfd ps' h f
Proof
  simp[hclean_def] >> strip_tac >> gvs[] >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  gvs[l1_close_def, l1do_def, AllCaseEqs(), forget_def, set_outbox_def, after_send_def,
      ALOOKUP_ADELKEY, MEM_FILTER, inb_of_set_inb, SIMP_RULE (srw_ss()) [] l1hdln_lt] >>
  every_case_tac >> gvs[] >>
  rpt conj_tac >> TRY (qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
  rpt strip_tac >> gvs[] >>
  rename1 ‘hdl l _ = hdl l i’ >>
  ‘hdl l i ≠ hdl l ps.b.nxt’ by (irule l1hdl_fresh >> simp[]) >> gvs[]
QED

Theorem pacts_keep:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ hclean lfd ps h f ⇒
    hclean lfd ps' h f
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  metis_tac[pdo_keep]
QED

Theorem pdo_ainv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ ainv ps ⇒
  ainv ps' ∧
  ∀h g. ALOOKUP ps'.b.tbl h = SOME g ∧ ALOOKUP ps.b.tbl h ≠ SOME g ⇒ hclean lfd ps' h g
Proof
  simp[ainv_def] >> strip_tac >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  gvs[l1_close_def, l1do_def, AllCaseEqs(), forget_def, set_outbox_def, after_send_def,
      ALOOKUP_ADELKEY, MEM_FILTER, inb_of_set_inb] >>
  every_case_tac >> gvs[] >>
  rpt conj_tac >> rpt strip_tac >> gvs[hclean_def, inb_of_def, set_inb_def, ALOOKUP_ADELKEY] >>
  every_case_tac >> gvs[] >>
  TRY (qexists_tac ‘ps.b.nxt’ >> simp[] >> NO_TAC) >>
  imp_res_tac MEM_SND_ADELKEY_sub >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, FORALL_PROD] >> metis_tac[pairTheory.PAIR]
QED

Theorem pdo_out_le:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧
  (∀h bs. a = Write h bs ∧ ALOOKUP ps.b.tbl h = SOME f ⇒ bs = []) ⇒
  LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps.b f)
Proof
  strip_tac >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  gvs[l1_close_def, l1do_def, AllCaseEqs(), outbox_of_forget, set_inb_def] >>
  TRY (simp[outbox_of_def] >> NO_TAC) >>
  rename1 ‘ALOOKUP _ c = SOME g’ >> Cases_on ‘g = f’ >> gvs[after_send_def] >>
  every_case_tac >> rw[outbox_of_set_outbox] >> simp[outbox_of_def]
QED

Theorem pacts_out_le:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ ainv ps ∧
    (∀h bs. MEM (Write h bs) acts ∧
            (ALOOKUP ps.b.tbl h = SOME f ∨ ALOOKUP ps'.b.tbl h = SOME f) ⇒ bs = []) ⇒
    LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps.b f)
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo _ _ a = SOME (_, (w1, ps1), _)’ >>
  drule_all pdo_ainv >> strip_tac >>
  ‘LENGTH (outbox_of ps1.b f) ≤ LENGTH (outbox_of ps.b f)’
    by (irule pdo_out_le >> metis_tac[]) >>
  ‘LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps1.b f)’
    suffices_by metis_tac[LESS_EQ_TRANS] >>
  first_x_assum irule >> simp[] >>
  reverse conj_tac >- (goal_assum drule) >>
  rpt strip_tac >> TRY (metis_tac[]) >>
  Cases_on ‘ALOOKUP ps.b.tbl h = SOME f’ >- metis_tac[] >>
  ‘hclean lfd ps1 h f’ by metis_tac[] >>
  drule_all pacts_keep >> simp[hclean_def] >> metis_tac[]
QED

Theorem tail_tbl:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒ ps'.b.tbl = ps.b.tbl
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l1_flush_fields >> strip_tac >>
  drule pf_fetch_b >> strip_tac >>
  drule l1_reap_le >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  gvs[stall_step_drops, honestL1PFModelTheory.FOLDL_drop_out]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

(* Round k's Writes on f's handles (at its start or end) carry no bytes *)
Definition wclean_def:
  wclean lfd pol ifds m w0 f k ⇔
    ∀h bs. MEM (Write h bs) (racts lfd pol ifds m w0 k) ∧
           (ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME f ∨
            ALOOKUP (rstate lfd pol ifds m w0 (SUC k)).b.tbl h = SOME f) ⇒ bs = []
End

Theorem round_le:
  oassm lfd pol ifds m w0 ∧ wclean lfd pol ifds m w0 f k ⇒
  LENGTH (outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f) ≤
    LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b f) ∧
  (outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f ≠ [] ∧
   LENGTH (outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f) =
     LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b f) ⇒
   scount (rstate lfd pol ifds m w0 (SUC k)) f = scount (rstate lfd pol ifds m w0 k) f + 1)
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule_all run_rel >> disch_then (qspec_then ‘SUC k’ strip_assume_tac) >>
  drule_all run_rel >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  drule tail_le >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  drule tail_tbl >> strip_tac >>
  ‘LENGTH (outbox_of ws11.b f) ≤ LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b f)’
    by (irule pacts_out_le >> simp[] >>
        qpat_x_assum ‘wclean _ _ _ _ _ _ _’ mp_tac >> simp[wclean_def, racts_def] >>
        strip_tac >> rpt conj_tac >>
        TRY (irule pown_ainv >> qexists_tac ‘lfd’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
        TRY (rpt strip_tac >> first_x_assum irule >> gvs[] >> NO_TAC) >>
        metis_tac[]) >>
  conj_tac >- simp[] >>
  strip_tac >>
  ‘MEM (f, scount ws11 f + 1) (rstate lfd pol ifds m w0 (SUC k)).stalls’
    by (first_x_assum irule >> simp[] >>
        qpat_x_assum ‘out_rel _ (rworld _ _ _ _ _ (SUC k)) _ _’ mp_tac >>
        simp[out_rel_def, okeys_def] >> metis_tac[]) >>
  ‘scount ws11 f = scount (rstate lfd pol ifds m w0 k) f’
    by (drule pacts_stalls >> simp[scount_def]) >>
  ‘ALL_DISTINCT (MAP FST (rstate lfd pol ifds m w0 (SUC k)).stalls)’
    by metis_tac[run_window_inv] >>
  ‘ALOOKUP (rstate lfd pol ifds m w0 (SUC k)).stalls f = SOME (scount ws11 f + 1)’
    by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
  qabbrev_tac ‘s0 = scount (rstate lfd pol ifds m w0 k) f’ >> gvs[scount_def]
QED

Theorem run_scount_lt:
  run_ok lfd pol ifds m w0 ⇒ ∀k. scount (rstate lfd pol ifds m w0 k) f < pf_sendwait
Proof
  strip_tac >> Cases
  >- simp[rstate_def, prun_0, pinit_def, scount_def, pf_sendwait_def] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  drule pround_stalls >> strip_tac >>
  simp[scount_def] >> CASE_TAC >- simp[pf_sendwait_def] >>
  imp_res_tac ALOOKUP_MEM >> res_tac
QED

Definition olen_def:
  olen lfd pol ifds m w0 f k = LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b f)
End

Theorem run_olen_mono:
  oassm lfd pol ifds m w0 ∧ (∀k. n0 ≤ k ⇒ wclean lfd pol ifds m w0 f k) ⇒
  ∀d k. n0 ≤ k ⇒ olen lfd pol ifds m w0 f (k + d) ≤ olen lfd pol ifds m w0 f k
Proof
  strip_tac >> Induct >> rpt strip_tac >> simp[] >>
  irule LESS_EQ_TRANS >> qexists_tac ‘olen lfd pol ifds m w0 f (k + d)’ >> simp[] >>
  simp[ADD_CLAUSES, olen_def] >> irule (cj 1 round_le) >> simp[]
QED

(* With the outbox stuck at a non-empty length, the stall count rises
   each round *)
Theorem run_stuck_scount:
  oassm lfd pol ifds m w0 ∧ (∀k. n0 ≤ k ⇒ wclean lfd pol ifds m w0 f k) ∧ n0 ≤ k ∧
  0 < olen lfd pol ifds m w0 f k ⇒
  ∀d. (∀e. e ≤ d ⇒ olen lfd pol ifds m w0 f (k + e) = olen lfd pol ifds m w0 f k) ⇒
      d ≤ scount (rstate lfd pol ifds m w0 (k + d)) f
Proof
  strip_tac >> Induct >> simp[] >> strip_tac >>
  ‘d ≤ scount (rstate lfd pol ifds m w0 (k + d)) f’
    by (first_x_assum irule >> rpt strip_tac >>
        first_x_assum (qspec_then ‘e’ mp_tac) >> simp[]) >>
  ‘olen lfd pol ifds m w0 f (k + SUC d) = olen lfd pol ifds m w0 f k ∧
   olen lfd pol ifds m w0 f (k + d) = olen lfd pol ifds m w0 f k’
    by (‘k + SUC d = SUC d + k’ by simp[] >> ‘k + d = d + k’ by simp[] >>
        ntac 2 (pop_assum (fn th => rewrite_tac[th])) >>
        conj_tac >> first_x_assum irule >> simp[]) >>
  qspecl_then [‘k + d’] mp_tac (Q.GEN ‘k’ round_le) >>
  impl_tac >- (simp[] >> first_x_assum irule >> simp[]) >>
  gvs[olen_def, ADD_CLAUSES] >> strip_tac >>
  ‘outbox_of (rstate lfd pol ifds m w0 (SUC (d + k))).b f ≠ []’
    by (strip_tac >> gvs[]) >>
  gvs[]
QED

Theorem run_out_empty:
  oassm lfd pol ifds m w0 ∧ (∀k. n0 ≤ k ⇒ wclean lfd pol ifds m w0 f k) ⇒
  ∀k. n0 ≤ k ⇒ ∃k'. k ≤ k' ∧ olen lfd pol ifds m w0 f k' = 0
Proof
  strip_tac >>
  ‘∀l k. n0 ≤ k ∧ olen lfd pol ifds m w0 f k = l ⇒
         ∃k'. k ≤ k' ∧ olen lfd pol ifds m w0 f k' = 0’ suffices_by metis_tac[] >>
  completeInduct_on ‘l’ >> rpt strip_tac >>
  Cases_on ‘l = 0’ >- (qexists_tac ‘k’ >> gvs[]) >>
  ‘∃d. olen lfd pol ifds m w0 f (k + d) < l’
    suffices_by (strip_tac >>
                 first_x_assum (qspec_then ‘olen lfd pol ifds m w0 f (k + d)’ mp_tac) >>
                 simp[] >> disch_then (qspec_then ‘k + d’ mp_tac) >> simp[] >>
                 strip_tac >> qexists_tac ‘k'’ >> simp[]) >>
  CCONTR_TAC >> gvs[NOT_LESS] >>
  ‘∀e. olen lfd pol ifds m w0 f (k + e) = olen lfd pol ifds m w0 f k’
    by (gen_tac >> first_x_assum (qspec_then ‘e’ assume_tac) >>
        ‘e + k = k + e’ by simp[] >> pop_assum (fn th => fs[th]) >>
        qspecl_then [‘n0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’] mp_tac
          (Q.GENL [‘n0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’] run_olen_mono) >>
        simp[] >> disch_then (qspecl_then [‘e’, ‘k’] mp_tac) >> simp[]) >>
  ‘pf_sendwait ≤ scount (rstate lfd pol ifds m w0 (k + pf_sendwait)) f’
    by (irule run_stuck_scount >> rpt conj_tac >> TRY (qexists_tac ‘n0’) >> fs[]) >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  drule run_scount_lt >> disch_then (qspecl_then [‘f’, ‘k + pf_sendwait’] mp_tac) >>
  simp[]
QED

(* MAIN (moonshot step 8 (b)): S4w from the server's side.  If, once f is
   no longer fetched, the Writes on f's handles eventually carry no bytes,
   then S4w holds for f, for every hw: the write timeout empties f's
   outbox, and nothing refills it *)
Theorem S4w_of_stop:
  oassm lfd pol ifds m w0 ∧
  (∀n. (∀k. n ≤ k ⇒ ¬fetched_at lfd pol ifds m w0 k f) ⇒
       ∃n0. n ≤ n0 ∧
            ∀k h bs. n0 ≤ k ∧ MEM (Write h bs) (racts lfd pol ifds m w0 k) ∧
                     (ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME f ∨
                      ALOOKUP (rstate lfd pol ifds m w0 (SUC k)).b.tbl h = SOME f) ⇒
                     bs = []) ⇒
  S4w lfd pol hw ifds m w0 f
Proof
  strip_tac >> simp[S4w_def] >> rpt strip_tac >>
  qpat_x_assum ‘∀n. _ ⇒ ∃n0. _’ (qspec_then ‘n’ mp_tac) >>
  impl_tac >- fs[fetched_at_def] >>
  strip_tac >>
  ‘∀k. n0 ≤ k ⇒ wclean lfd pol ifds m w0 f k’
    by (rw[wclean_def] >> first_x_assum irule >> qexistsl [‘h’, ‘k’] >> fs[]) >>
  drule run_out_empty >> disch_then drule >> disch_then (qspec_then ‘n0’ mp_tac) >> simp[] >>
  strip_tac >> qexists_tac ‘k'’ >> simp[] >> rpt strip_tac
  >- (‘olen lfd pol ifds m w0 f (k' + (n'' − k')) ≤ olen lfd pol ifds m w0 f k'’
        by (irule run_olen_mono >> simp[] >> qexists_tac ‘n0’ >> simp[]) >>
      gvs[olen_def])
  >> first_x_assum irule >> qexistsl [‘h’, ‘n''’] >> fs[racts_def]
QED

(* ------------------------------------------------------------------------
   S4 over feeds (design/45 §2.3, as revised): two L2 obligations per
   program give S4g (the proxy's route) or, with S3w and feeds = identity,
   S4w (the servers' route)
   ------------------------------------------------------------------------ *)

(* Round k reads g: g's inbox is not empty at the round's start, and an
   action of the round reads a handle of g *)
Definition read_at_def:
  read_at lfd pol ifds m w0 k g ⇔
    inb_of (rstate lfd pol ifds m w0 k) g ≠ [] ∧
    ∃h n. MEM (Read h n) (racts lfd pol ifds m w0 k) ∧
          ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME g
End

(* L2 obligation: once f's feeders are no longer read, f's writes
   eventually carry no bytes (the "eventually" absorbs a reply lag) *)
Definition writes_follow_feeds_def:
  writes_follow_feeds lfd pol ifds m w0 (feeds : num -> word64 -> word64 -> bool) ⇔
    ∀n f. (∀k g. n ≤ k ∧ feeds k g f ⇒ ¬read_at lfd pol ifds m w0 k g) ⇒
          ∃n0. n ≤ n0 ∧ ∀k. n0 ≤ k ⇒ wclean lfd pol ifds m w0 f k
End

(* L2 obligation: a feeder of an outbox over hw at a round's start is not
   read in that round *)
Definition pauses_feeders_def:
  pauses_feeders lfd pol hw ifds m w0 (feeds : num -> word64 -> word64 -> bool) ⇔
    ∀k g f. feeds k g f ∧ hw < LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b f) ⇒
            ¬read_at lfd pol ifds m w0 k g
End

(* S4g: f's outbox is ≤ hw infinitely often (no hypothesis on the peer:
   the write timeout drops an outbox that does not shrink) *)
Definition S4g_def:
  S4g lfd pol hw ifds m w0 f ⇔
    ∀n. ∃n'. n ≤ n' ∧ LENGTH (outbox_of (rstate lfd pol ifds m w0 n').b f) ≤ hw
End

(* MAIN (step 8, the proxy's route) *)
Theorem S4g_from_feeds:
  oassm lfd pol ifds m w0 ∧ writes_follow_feeds lfd pol ifds m w0 feeds ∧
  pauses_feeders lfd pol hw ifds m w0 feeds ⇒
  ∀f. S4g lfd pol hw ifds m w0 f
Proof
  strip_tac >> rw[S4g_def] >> CCONTR_TAC >> gvs[NOT_LESS_EQUAL] >>
  qpat_x_assum ‘writes_follow_feeds _ _ _ _ _ _’
    (qspecl_then [‘n’, ‘f’] mp_tac o REWRITE_RULE [writes_follow_feeds_def]) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum ‘pauses_feeders _ _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [pauses_feeders_def]) >>
      disch_then (qspecl_then [‘k’, ‘g’, ‘f’] mp_tac) >> simp[] >>
      first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]) >>
  strip_tac >>
  drule run_out_empty >> disch_then drule >> disch_then (qspec_then ‘n0’ mp_tac) >>
  simp[olen_def] >> rpt strip_tac >>
  qpat_x_assum ‘∀n'. _ ∨ _’ (qspec_then ‘k'’ mp_tac) >> gvs[]
QED

Theorem pf_fetch_inb:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ¬fetched f log ⇒
    inb_of ps' f = inb_of ps f
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[AllCaseEqs()]) >>
  first_x_assum drule >> gvs[fetched_def, inb_of_set_inb] >> rw[] >> gvs[inb_of_def]
QED

Theorem pdo_inb:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ inb_of ps f = [] ⇒ inb_of ps' f = []
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[inb_of_set_inb] >>
  TRY (PairCases_on ‘z’) >> gvs[inb_of_def] >> rw[] >> gvs[]
QED

Theorem pacts_inb:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ inb_of ps f = [] ⇒
    inb_of ps' f = []
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  metis_tac[pdo_inb]
QED

(* With f no longer fetched, an empty inbox stays empty *)
Theorem run_inb_empty:
  run_ok lfd pol ifds m w0 ∧ inb_of (rstate lfd pol ifds m w0 n) f = [] ∧
  (∀k. n ≤ k ⇒ ¬fetched_at lfd pol ifds m w0 k f) ⇒
  ∀d. inb_of (rstate lfd pol ifds m w0 (n + d)) f = []
Proof
  strip_tac >> Induct >> simp[] >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘n + d’] strip_assume_tac) >>
  ‘¬fetched f (rlog lfd pol ifds m w0 (n + d))’
    by (first_x_assum (qspec_then ‘n + d’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs()] >> strip_tac >> gvs[ADD_CLAUSES] >>
  PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pacts_inb >> strip_tac >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule pf_fetch_inb >> disch_then (qspec_then ‘f’ mp_tac) >> simp[] >>
  qpat_x_assum ‘_ = rstate _ _ _ _ _ _’ (SUBST1_TAC o SYM) >>
  simp[inb_of_def, stall_step_def]
QED

(* MAIN (step 8, the servers' route): replies only, and S3w *)
Theorem S4w_of_feeds:
  oassm lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  writes_follow_feeds lfd pol ifds m w0 (λk g f. g = f) ⇒
  ∀f. S4w lfd pol hw ifds m w0 f
Proof
  rpt strip_tac >> irule S4w_of_stop >> simp[] >> rpt strip_tac >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  qpat_x_assum ‘S3w _ _ _ _ _’ (qspecl_then [‘n’, ‘f’] mp_tac o REWRITE_RULE [S3w_def]) >>
  impl_tac >- fs[fetched_at_def] >> strip_tac >>
  ‘∀d. inb_of (rstate lfd pol ifds m w0 (n' + d)) f = []’
    by (irule run_inb_empty >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum ‘writes_follow_feeds _ _ _ _ _ _’
    (qspecl_then [‘n'’, ‘f’] mp_tac o REWRITE_RULE [writes_follow_feeds_def]) >>
  impl_tac
  >- (rw[read_at_def] >> first_x_assum (qspec_then ‘k - n'’ mp_tac) >> simp[]) >>
  strip_tac >> qexists_tac ‘n0’ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> simp[wclean_def] >> metis_tac[]
QED
