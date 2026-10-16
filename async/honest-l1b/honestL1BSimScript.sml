(*
  L3-09 (S2), the simulation: every round of the blocking run is matched
  by rounds of the PF run in the reindexed world reindex (btr ..) w0
  (honestL1BRefine).  A round that is not idle is the same PF round, in
  the lifted world; an idle round, whose blocking poll returns after k
  more steps, is k idle PF rounds (an empty poll each, nothing else) and
  the PF round whose poll finds what the blocking poll found.

  The server is told nothing in an idle PF round (an empty snapshot), so
  the server's histories differ: the PF run's has the empty snapshots the
  blocking run skips.  bquiet: the server ignores an empty snapshot where
  it has nothing to do and is not busy (for the event-level program,
  quiet_nb); sfor: the two histories are the same to the server.

  The events differ the same way (evrel): the blocking poll's event stands
  for k empty polls and the non-blocking poll that found the same.

  MAIN: l1b_refines_pf.
*)
Theory honestL1BSim
Ancestors
  honestL1BRefine honestL1BLift honestL1BHist honestL1BPoll honestL1BModel
  honestL0Reindex honestL1PFModel honestL1Model honestL0World honestL0
  asyncCore asyncM3World ffi
Libs
  preamble

(* ------------------------------------------------------------------------
   The server's histories
   ------------------------------------------------------------------------ *)

Overload esnap = “ssnap [] [] : (word64, sresp) snapshot”

Definition bquiet_def:
  bquiet m (ifds : (word64, sresp) snapshot list -> word64 list) bz ⇔
    ∀h k. new_actions (log_of m) h = [] ∧ ¬bz h ⇒
          new_actions (log_of m) (h ++ [esnap] ++ k) = new_actions (log_of m) (h ++ k) ∧
          ifds (h ++ [esnap] ++ k) = ifds (h ++ k) ∧
          bz (h ++ [esnap] ++ k) = bz (h ++ k)
End

Definition sfor_def:
  sfor m (ifds : (word64, sresp) snapshot list -> word64 list) bz full kept ⇔
    ∀k. new_actions (log_of m) (full ++ k) = new_actions (log_of m) (kept ++ k) ∧
        ifds (full ++ k) = ifds (kept ++ k) ∧ bz (full ++ k) = bz (kept ++ k)
End

Theorem sfor_refl[simp]:
  sfor m ifds bz h h
Proof
  simp[sfor_def]
QED

Theorem sfor_now:
  sfor m ifds bz full kept ⇒
  new_actions (log_of m) full = new_actions (log_of m) kept ∧
  ifds full = ifds kept ∧ bz full = bz kept
Proof
  rw[sfor_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]
QED

Theorem sfor_snoc:
  sfor m ifds bz full kept ⇒ sfor m ifds bz (full ++ [s]) (kept ++ [s])
Proof
  rw[sfor_def] >> first_x_assum (qspec_then ‘s :: k’ mp_tac) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem sfor_skip:
  bquiet m ifds bz ∧ sfor m ifds bz full kept ∧
  new_actions (log_of m) kept = [] ∧ ¬bz kept ⇒
  sfor m ifds bz (full ++ [esnap]) kept
Proof
  rw[sfor_def, bquiet_def] >> first_x_assum (qspec_then ‘esnap :: k’ mp_tac) >>
  first_x_assum drule_all >> disch_then (qspec_then ‘k’ mp_tac) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem sfor_skips:
  ∀i full. bquiet m ifds bz ∧ sfor m ifds bz full kept ∧
           new_actions (log_of m) kept = [] ∧ ¬bz kept ⇒
           sfor m ifds bz (full ++ REPLICATE i esnap) kept
Proof
  Induct >> rw[] >>
  first_x_assum (qspec_then ‘full ++ [esnap]’ mp_tac) >>
  impl_tac >- (simp[] >> irule sfor_skip >> simp[]) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

(* ------------------------------------------------------------------------
   The events
   ------------------------------------------------------------------------ *)

(* An empty non-blocking poll of fes *)
Definition epoll_def:
  epoll fes ev ⇔
    ∃x. ev = IO_event (ExtCall «sys_poll») (poll_conf fes)
               (ZIP (REPLICATE (13 + LENGTH fes) 0w, poll_out x fes)) ∧
        ¬any_revents x fes
End

(* evrel pevs bevs: the PF run's events pevs, the blocking run's bevs *)
Inductive evrel:
[~nil:]
  evrel [] []
[~snoc:]
  evrel xs ys ⇒ evrel (xs ++ [e]) (ys ++ [e])
[~poll:]
  evrel xs ys ∧ EVERY (epoll fes) es ⇒
  evrel (xs ++ es ++ [IO_event (ExtCall «sys_poll») (poll_conf fes) bs])
        (ys ++ [IO_event (ExtCall «sys_poll») (pollb_conf fes) bs])
End

Theorem evrel_append:
  ∀zs xs ys. evrel xs ys ⇒ evrel (xs ++ zs) (ys ++ zs)
Proof
  ho_match_mp_tac SNOC_INDUCT >> rw[SNOC_APPEND] >>
  REWRITE_TAC[APPEND_ASSOC] >> irule evrel_snoc >> simp[]
QED

(* ------------------------------------------------------------------------
   The round's shape
   ------------------------------------------------------------------------ *)

Theorem pf_after_pevs:
  pf_after lfd hw hs ps fes (rv, w1, pevs) =
    OPTION_MAP (λ(rdy, ws, log, evs). (rdy, ws, log, pevs ++ evs))
               (pf_after lfd hw hs ps fes (rv, w1, []))
Proof
  simp[pf_after_def] >> every_case_tac >> simp[]
QED

Theorem pf_poll_set_small:
  EVERY (λ(f, e). e < 256) (pf_poll_set lfd hw ps hs)
Proof
  simp[pf_poll_set_def, EVERY_MEM, MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS,
       FORALL_PROD] >>
  rw[] >> TRY (PairCases_on ‘y’ >> gvs[] >> NO_TAC) >>
  pop_assum mp_tac >> every_case_tac >> rw[] >> simp[]
QED

(* A round of the blocking run: not idle, it is the PF round; idle, it is
   its blocking poll and the PF round's tail after it *)
Theorem bround_cases:
  bround lfd hw (¬bz h) (ifds h) (w, ps) (new_actions (log_of m) h) =
    SOME (BRound snap ws' log revs) ⇒
  (¬bidle lfd hw ifds bz m h ps ∧
   ∃rs evs1 w1 ps1 rdy tevs.
     pacts lfd (w, ps) (new_actions (log_of m) h) = SOME (rs, evs1, (w1, ps1)) ∧
     pf_tail lfd hw (ifds h) (w1, ps1) = SOME (rdy, ws', log, tevs) ∧
     snap = ssnap rdy rs ∧ revs = evs1 ++ tevs) ∨
  (bidle lfd hw ifds bz m h ps ∧
   ∃out w2 ev rdy tevs.
     sys_pollb (pf_poll_set lfd hw ps (ifds h)) w = SOME (INL (out, w2, ev)) ∧
     pf_after lfd hw (ifds h) ps (pf_poll_set lfd hw ps (ifds h))
       (poll_revents (pf_poll_set lfd hw ps (ifds h)) out, w2, []) = SOME (rdy, ws', log, tevs) ∧
     snap = ssnap rdy [] ∧ revs = ev :: tevs)
Proof
  rw[bround_def, AllCaseEqs()] >> gvs[bidle_def] >>
  TRY (Cases_on ‘new_actions (log_of m) h = []’ >> gvs[] >> NO_TAC) >>
  fs[Once pf_after_pevs] >> gvs[] >> PairCases_on ‘z’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   The translation after a clean walk
   ------------------------------------------------------------------------ *)

Theorem btr_after:
  (FST ws0).hist ≼ hp ∧
  trs (bwait lfd hw ifds bz m ws0) (FST ws0).hist (DROP (LENGTH (FST ws0).hist) hp) H ⇒
  ∀zs. btr lfd hw ifds bz m ws0 (hp ++ zs) = trw (bwait lfd hw ifds bz m ws0) H zs
Proof
  rw[btr_def] >>
  ‘DROP (LENGTH (FST ws0).hist) (hp ++ zs) = DROP (LENGTH (FST ws0).hist) hp ++ zs’
    by (fs[IS_PREFIX_APPEND] >> REWRITE_TAC[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  simp[] >> drule trw_append >> simp[]
QED

(* ------------------------------------------------------------------------
   PF rounds in the lifted world
   ------------------------------------------------------------------------ *)

(* A round that is not idle *)
Theorem pround_lift:
  pacts lfd (w, ps) acts = SOME (rs, evs1, (w1, ps1)) ∧
  pf_tail lfd hw hs (w1, ps1) = SOME (rdy, (w', ps'), log, tevs) ∧
  tr_from tr hp w.hist (LENGTH evs1 + LENGTH tevs) ⇒
  pround lfd hw hs (lift tr hp w, ps) acts =
    SOME (ssnap rdy rs, (lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ps'), log, evs1 ++ tevs)
Proof
  strip_tac >> imp_res_tac hgrows_pacts >> imp_res_tac hgrows_tail >>
  qspecl_then [‘w’, ‘w1’, ‘w'’, ‘LENGTH evs1’, ‘LENGTH tevs’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- simp[]) >> strip_tac >>
  ‘tr_from tr hp w.hist (LENGTH evs1)’
    by (irule tr_from_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all lift_pacts >> strip_tac >>
  drule_all lift_tail >> strip_tac >>
  simp[pround_def]
QED

Theorem poll_chunks_one:
  LENGTH l ≤ 4096 ⇒ poll_chunks l = [l]
Proof
  simp[Once poll_chunks_def]
QED

Overload pcall = “λfes. («sys_poll», poll_conf fes, REPLICATE (13 + LENGTH fes) (0w : word8))”

(* An idle round whose poll reports nothing *)
Theorem pround_idle_lift:
  fes = pf_poll_set lfd hw ps hs ∧ pf_idle lfd hw ps hs ∧ tr hp = u.hist ∧
  sys_poll fes u = SOME (out, u', ev) ∧ rv_quiet (poll_revents fes out) ⇒
  pround lfd hw hs (lift tr hp u, ps) [] = SOME (esnap, (lift tr (hp ++ [pcall fes]) u', ps), [], [ev])
Proof
  strip_tac >> gvs[] >>
  ‘LENGTH (pf_poll_set lfd hw ps hs) ≤ 4096’ by fs[pf_idle_def] >>
  drule_then assume_tac lift_do >>
  simp[pround_def, pf_tail_after, poll_chunks_one, l1_polls_def] >>
  fs[sys_poll_def] >>
  ‘EVERY (λ(f, r). ¬r.rin ∧ ¬r.rout ∧ ¬r.rerr ∧ ¬r.rhup)
     (poll_revents (pf_poll_set lfd hw ps hs) out)’ by fs[rv_quiet_def] >>
  drule_all pf_after_idle >> simp[ssnap_def]
QED

Theorem lift_after0:
  pf_after lfd hw hs ps fes (rv, w1, []) = SOME (rdy, (w', ps'), log, evs) ∧
  tr_from tr hp w1.hist (LENGTH evs) ⇒
  pf_after lfd hw hs ps fes (rv, lift tr hp w1, []) =
    SOME (rdy, (lift tr (hp ++ DROP (LENGTH w1.hist) w'.hist) w', ps'), log, evs)
Proof
  strip_tac >> irule lift_after >> simp[]
QED

(* The round whose poll finds what the blocking poll found *)
Theorem pround_wake_lift:
  fes = pf_poll_set lfd hw ps hs ∧ pf_idle lfd hw ps hs ∧ tr hp = u.hist ∧
  sys_poll fes u = SOME (out, w2 with hist := u.hist ++ [pcall fes], ev) ∧
  pf_after lfd hw hs ps fes (poll_revents fes out, w2, []) = SOME (rdy, (w', ps'), log, tevs) ∧
  tr_from tr (hp ++ [pcall fes]) w2.hist (LENGTH tevs) ⇒
  pround lfd hw hs (lift tr hp u, ps) [] =
    SOME (ssnap rdy [], (lift tr (hp ++ [pcall fes] ++ DROP (LENGTH w2.hist) w'.hist) w', ps'),
          log, ev :: tevs)
Proof
  strip_tac >> gvs[] >>
  ‘LENGTH (pf_poll_set lfd hw ps hs) ≤ 4096’ by fs[pf_idle_def] >>
  drule_then assume_tac lift_do >>
  simp[pround_def, pf_tail_after, poll_chunks_one, l1_polls_def] >>
  fs[sys_poll_def] >>
  drule_all lift_after0 >> strip_tac >>
  ONCE_REWRITE_TAC[pf_after_pevs] >> simp[]
QED

Theorem REPLICATE_SNOC_CONS[local]:
  ∀i. REPLICATE i x ++ [x] = x :: REPLICATE i x
Proof
  Induct >> simp[]
QED

Theorem REPLICATE_SNOC_CONS_APP[local]:
  l ++ REPLICATE i x ++ [x] = l ++ x :: REPLICATE i x
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, REPLICATE_SNOC_CONS]
QED

(* MAIN: while the blocking poll waits, the PF run polls and finds nothing *)
Theorem pf_idle_rounds:
  ∀i. fes = pf_poll_set lfd hw ps (ifds h) ∧
      bquiet m ifds bz ∧ bidle lfd hw ifds bz m h ps ∧ sfor m ifds bz full h ∧
      prounds lfd hw ifds m ws0 N = SOME (full, (lift tr hp w, ps), evs, logs) ∧
      poll_ok fes ∧
      (pollb_wait fes w = NONE ∨ ∃k. pollb_wait fes w = SOME k ∧ i ≤ k) ∧
      (∀j. j ≤ i ⇒ tr (hp ++ REPLICATE j (pcall fes)) = w.hist) ⇒
      ∃es. prounds lfd hw ifds m ws0 (N + i) =
             SOME (full ++ REPLICATE i esnap,
                   (lift tr (hp ++ REPLICATE i (pcall fes)) (l0_ticks «sys_poll» i w), ps),
                   evs ++ es, logs ++ REPLICATE i []) ∧
           EVERY (epoll fes) es ∧ LENGTH es = i
Proof
  Induct >- (rw[] >> simp[l0_ticks_def]) >>
  rpt strip_tac >>
  (first_x_assum (drule_at (Pos (el 5))) >> rpt (disch_then drule) >>
   impl_tac >- (rw[] >> fs[])) >> strip_tac >>
  ‘∃out. sys_poll fes (l0_ticks «sys_poll» i w) =
           SOME (out, l0_ticks «sys_poll» (SUC i) w with hist := w.hist ++ [pcall fes],
                 IO_event (ExtCall «sys_poll») (poll_conf fes)
                   (ZIP (REPLICATE (13 + LENGTH fes) 0w, out))) ∧
         rv_quiet (poll_revents fes out) ∧ ∃x. out = poll_out x fes ∧ ¬any_revents x fes’
    by (irule sys_poll_idle >> fs[]) >>
  ‘sfor m ifds bz (full ++ REPLICATE i esnap) h’ by (irule sfor_skips >> fs[bidle_def]) >>
  drule sfor_now >> strip_tac >>
  ‘tr (hp ++ REPLICATE i (pcall fes)) = (l0_ticks «sys_poll» i w).hist’ by simp[] >>
  ‘pf_idle lfd hw ps (ifds h) ∧ new_actions (log_of m) h = []’ by fs[bidle_def] >>
  drule_all pround_idle_lift >> strip_tac >>
  qexists_tac ‘es ++ [IO_event (ExtCall «sys_poll») (poll_conf fes)
                        (ZIP (REPLICATE (13 + LENGTH fes) 0w, out))]’ >>
  qpat_x_assum ‘fes = _’ SUBST_ALL_TAC >>
  gvs[ADD_CLAUSES, prounds_def, REPLICATE_SNOC_CONS_APP, epoll_def] >>
  qexists_tac ‘x’ >> simp[]
QED
