(*
  L3-09 (S2): the blocking L1 refines the prefetching L1 (design note
  L3-09 §2).

  The blocking run in the world w0 is matched by the PF run in the world
  reindex tr w0, whose choices and environment see, at each PF history h',
  the blocking history tr h'.  The translation tr is read off the blocking
  run: walking a PF history call by call, a call made where the blocking
  run polls blocking (bwait: after how many more steps that poll returns)
  stands for the k+1 non-blocking polls the PF run makes there, the k empty
  ones and the last; every other call stands for itself.

  This file: the translation (trw, btr), and the facts about the blocking
  run it needs (its histories grow, so a history determines its round).

  MAIN: trw_append, brun_hist_unique.
*)
Theory honestL1BRefine
Ancestors
  honestL1BLift honestL1BHist honestL1BPoll honestL1BModel honestL0Reindex
  honestL1PFModel honestL1Model honestL0World honestL0 asyncCore
Libs
  preamble


(* ------------------------------------------------------------------------
   The walk
   ------------------------------------------------------------------------ *)

(* The blocking call a non-blocking poll stands for *)
Definition unblk_def:
  unblk ((n, conf, bytes) : lcall) = (n, (1w : word8) :: TL conf, bytes)
End

(* trw bw H xs: the blocking history the PF calls xs stand for, after the
   blocking history H.  bw H: NONE, the blocking run's next call after H is
   the PF run's; SOME NONE, it is a blocking poll that never returns;
   SOME (SOME k), a blocking poll that returns after k more steps *)
Definition trw_def:
  trw (bw : lcall list -> num option option) H [] = H ∧
  trw bw H (c :: rest) =
    case bw H of
    | NONE => trw bw (H ++ [c]) rest
    | SOME NONE => H
    | SOME (SOME k) =>
        if LENGTH rest < k then H else trw bw (H ++ [unblk c]) (DROP k rest)
Termination
  WF_REL_TAC ‘measure (LENGTH o SND o SND)’ >> rw[LENGTH_DROP]
End

(* The walk over xs from H ends cleanly at H' *)
Inductive trs:
[~nil:]
  trs bw H [] H
[~call:]
  bw H = NONE ∧ trs bw (H ++ [c]) xs H' ⇒ trs bw H (c :: xs) H'
[~poll:]
  bw H = SOME (SOME k) ∧ LENGTH ys = k ∧ trs bw (H ++ [unblk c]) xs H' ⇒
  trs bw H (c :: (ys ++ xs)) H'
End

Theorem trw_append:
  ∀H xs H'. trs bw H xs H' ⇒ ∀zs. trw bw H (xs ++ zs) = trw bw H' zs
Proof
  Induct_on ‘trs’ >> rw[trw_def] >>
  ‘DROP (LENGTH ys) (ys ++ xs ++ zs) = xs ++ zs’ by REWRITE_TAC[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem trs_snoc_call:
  ∀H xs H'. trs bw H xs H' ⇒ bw H' = NONE ⇒ trs bw H (xs ++ [c]) (H' ++ [c])
Proof
  Induct_on ‘trs’ >> rw[] >> fs[trs_rules] >>
  TRY (irule trs_call >> fs[trs_rules] >> NO_TAC) >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> irule trs_poll >> fs[]
QED

Theorem trs_append:
  ∀H xs H'. trs bw H xs H' ⇒ ∀ys H''. trs bw H' ys H'' ⇒ trs bw H (xs ++ ys) H''
Proof
  Induct_on ‘trs’ >> rw[] >> fs[trs_rules] >>
  TRY (irule trs_call >> fs[trs_rules] >> NO_TAC) >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> irule trs_poll >> fs[]
QED

(* Calls after which the walk sees no blocking poll stand for themselves *)
Theorem trw_calls:
  ∀cs H. (∀n. n < LENGTH cs ⇒ bw (H ++ TAKE n cs) = NONE) ⇒ trw bw H cs = H ++ cs
Proof
  Induct >> rw[trw_def] >>
  ‘bw H = NONE’ by (first_assum (qspec_then ‘0’ mp_tac) >> REWRITE_TAC[TAKE_0, APPEND_NIL, prim_recTheory.LESS_0]) >> simp[] >>
  ‘H ++ h::cs = (H ++ [h]) ++ cs’ by simp[] >> pop_assum SUBST1_TAC >>
  first_x_assum irule >> rw[] >>
  first_x_assum (qspec_then ‘SUC n’ mp_tac) >> simp[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

Theorem trs_calls:
  ∀cs H. (∀n. n < LENGTH cs ⇒ bw (H ++ TAKE n cs) = NONE) ⇒ trs bw H cs (H ++ cs)
Proof
  Induct >> rw[trs_rules] >>
  irule trs_call >>
  ‘bw H = NONE’ by (first_assum (qspec_then ‘0’ mp_tac) >> REWRITE_TAC[TAKE_0, APPEND_NIL, prim_recTheory.LESS_0]) >> simp[] >>
  ‘H ++ h::cs = (H ++ [h]) ++ cs’ by simp[] >> pop_assum SUBST1_TAC >>
  first_x_assum irule >> rw[] >>
  first_x_assum (qspec_then ‘SUC n’ mp_tac) >> simp[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

(* ------------------------------------------------------------------------
   The blocking run: idle rounds, and histories that grow
   ------------------------------------------------------------------------ *)

(* The round after kept, from L1 state ps, polls blocking *)
Definition bidle_def:
  bidle lfd hw ifds bz m kept ps ⇔
    new_actions (log_of m) kept = [] ∧ ¬bz kept ∧ pf_idle lfd hw ps (ifds kept)
End

Theorem pacts_nil[simp]:
  pacts lfd ws [] = SOME ([], [], ws)
Proof
  simp[pacts_def]
QED

Theorem brounds_SUC_BRun:
  brounds lfd hw ifds bz m ws0 (SUC n) = SOME (BRun h' ws' evs' logs') ⇒
  ∃h ws evs logs snap log revs.
    brounds lfd hw ifds bz m ws0 n = SOME (BRun h ws evs logs) ∧
    bround lfd hw (¬bz h) (ifds h) ws (new_actions (log_of m) h) =
      SOME (BRound snap ws' log revs) ∧
    h' = h ++ [snap] ∧ evs' = evs ++ revs ∧ logs' = logs ++ [log]
Proof
  simp[brounds_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  Cases_on ‘r’ >> gvs[]
QED

Theorem brounds_hist_lt:
  ∀n' n h ws evs logs h' ws' evs' logs'.
    brounds lfd hw ifds bz m ws0 n = SOME (BRun h ws evs logs) ∧
    brounds lfd hw ifds bz m ws0 n' = SOME (BRun h' ws' evs' logs') ∧ n < n' ⇒
    LENGTH (FST ws).hist < LENGTH (FST ws').hist
Proof
  Induct >> rw[] >> drule brounds_SUC_BRun >> strip_tac >>
  PairCases_on ‘ws''’ >> PairCases_on ‘ws'’ >>
  drule bround_hgrows >> rw[hgrows_def] >> gvs[] >>
  Cases_on ‘n = n'’ >> gvs[] >>
  first_x_assum (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >> simp[]
QED

Theorem brun_hist_unique:
  ∀n h ws evs logs n' h' ws' evs' logs'.
  brounds lfd hw ifds bz m ws0 n = SOME (BRun h ws evs logs) ∧
  brounds lfd hw ifds bz m ws0 n' = SOME (BRun h' ws' evs' logs') ∧
  (FST ws).hist = (FST ws').hist ⇒
  n = n' ∧ h = h' ∧ ws = ws' ∧ evs = evs' ∧ logs = logs'
Proof
  rpt strip_tac >>
  ‘n = n'’ by (CCONTR_TAC >> ‘n < n' ∨ n' < n’ by decide_tac >>
               imp_res_tac brounds_hist_lt >> gvs[]) >>
  gvs[]
QED

(* ------------------------------------------------------------------------
   The blocking run's waits, and the translation
   ------------------------------------------------------------------------ *)

(* At the blocking history H, the blocking run starts an idle round, whose
   blocking poll waits this long (pollb_wait) *)
Definition bwait_def:
  bwait lfd hw ifds bz m ws0 H =
    if ∃n kept w ps evs logs.
         brounds lfd hw ifds bz m ws0 n = SOME (BRun kept (w, ps) evs logs) ∧
         w.hist = H ∧ bidle lfd hw ifds bz m kept ps
    then SOME (@k. ∃n kept w ps evs logs.
                 brounds lfd hw ifds bz m ws0 n = SOME (BRun kept (w, ps) evs logs) ∧
                 w.hist = H ∧ bidle lfd hw ifds bz m kept ps ∧
                 k = pollb_wait (pf_poll_set lfd hw ps (ifds kept)) w)
    else NONE
End

(* The translation of PF histories to blocking histories *)
Definition btr_def:
  btr lfd hw ifds bz m ws0 h' =
    trw (bwait lfd hw ifds bz m ws0) (FST ws0).hist (DROP (LENGTH (FST ws0).hist) h')
End

Theorem bwait_at:
  brounds lfd hw ifds bz m ws0 n = SOME (BRun kept (w, ps) evs logs) ⇒
  bwait lfd hw ifds bz m ws0 w.hist =
    if bidle lfd hw ifds bz m kept ps
    then SOME (pollb_wait (pf_poll_set lfd hw ps (ifds kept)) w)
    else NONE
Proof
  strip_tac >>
  ‘∀n' kept' w' ps' evs' logs'.
     brounds lfd hw ifds bz m ws0 n' = SOME (BRun kept' (w', ps') evs' logs') ∧
     w'.hist = w.hist ⇒ kept' = kept ∧ w' = w ∧ ps' = ps’
    by (rpt strip_tac >>
        qspecl_then [‘n’, ‘kept’, ‘(w, ps)’, ‘evs’, ‘logs’,
                     ‘n'’, ‘kept'’, ‘(w', ps')’, ‘evs'’, ‘logs'’] mp_tac brun_hist_unique >>
        simp[]) >>
  ‘(∃n kept' w' ps' evs' logs'.
      brounds lfd hw ifds bz m ws0 n = SOME (BRun kept' (w', ps') evs' logs') ∧
      w'.hist = w.hist ∧ bidle lfd hw ifds bz m kept' ps') ⇔
   bidle lfd hw ifds bz m kept ps’
    by (eq_tac >> rpt strip_tac
        >- (first_x_assum drule >> simp[] >> strip_tac >> gvs[])
        >> qexistsl_tac [‘n’, ‘kept’, ‘w’, ‘ps’, ‘evs’, ‘logs’] >> simp[]) >>
  ‘∀k. (∃n kept' w' ps' evs' logs'.
          brounds lfd hw ifds bz m ws0 n = SOME (BRun kept' (w', ps') evs' logs') ∧
          w'.hist = w.hist ∧ bidle lfd hw ifds bz m kept' ps' ∧
          k = pollb_wait (pf_poll_set lfd hw ps' (ifds kept')) w') ⇔
       bidle lfd hw ifds bz m kept ps ∧ k = pollb_wait (pf_poll_set lfd hw ps (ifds kept)) w’
    by (gen_tac >> eq_tac >> rpt strip_tac
        >- (first_x_assum drule >> simp[] >> strip_tac >> gvs[])
        >- (first_x_assum drule >> simp[] >> strip_tac >> gvs[])
        >> qexistsl_tac [‘n’, ‘kept’, ‘w’, ‘ps’, ‘evs’, ‘logs’] >> simp[]) >>
  simp[bwait_def] >> rw[]
QED

Theorem bwait_between:
  brounds lfd hw ifds bz m ws0 n = SOME (BRun kept (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m ws0 (SUC n) = SOME (BRun kept' (w', ps') evs' logs') ∧
  LENGTH w.hist < LENGTH H ∧ LENGTH H < LENGTH w'.hist ⇒
  bwait lfd hw ifds bz m ws0 H = NONE
Proof
  rw[bwait_def] >> CCONTR_TAC >> gvs[] >>
  rename1 ‘brounds _ _ _ _ _ _ j = SOME (BRun _ (w2, _) _ _)’ >>
  ‘j < SUC n ∨ j = SUC n ∨ SUC n < j’ by decide_tac >> gvs[]
  >- (‘j < n ∨ j = n’ by decide_tac >> gvs[] >>
      drule_then (drule_then drule) (Q.SPECL [‘n’, ‘j’] brounds_hist_lt) >> simp[])
  >> drule_then (drule_then drule) (Q.SPECL [‘j’, ‘SUC n’] brounds_hist_lt) >> simp[]
QED
