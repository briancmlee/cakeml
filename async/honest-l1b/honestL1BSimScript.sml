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
    ∃x. ev = IO_event (ExtCall «sys_poll») [0w]
               (ZIP (poll_buf fes, poll_out x (poll_buf fes))) ∧
        ¬any_revents x (pfes fes)
End

(* evrel pevs bevs: the PF run's events pevs, the blocking run's bevs *)
Inductive evrel:
[~nil:]
  evrel [] []
[~snoc:]
  evrel xs ys ⇒ evrel (xs ++ [e]) (ys ++ [e])
[~poll:]
  evrel xs ys ∧ EVERY (epoll fes) es ⇒
  evrel (xs ++ es ++ [IO_event (ExtCall «sys_poll») [0w] bs])
        (ys ++ [IO_event (ExtCall «sys_poll») pollb_conf bs])
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

Overload pcall = “λfes. («sys_poll», [0w : word8], poll_buf fes)”

(* An idle round whose poll reports nothing *)
Theorem pround_idle_lift:
  fes = pf_poll_set lfd hw ps hs ∧ pf_idle lfd hw ps hs ∧ tr hp = u.hist ∧
  sys_poll fes u = SOME (out, u', ev) ∧ rv_quiet (poll_revents fes out) ⇒
  pround lfd hw hs (lift tr hp u, ps) [] = SOME (esnap, (lift tr (hp ++ [pcall fes]) u', ps), [], [ev])
Proof
  strip_tac >> gvs[] >>
  drule_then assume_tac lift_do_buf >>
  simp[pround_def, pf_tail_after, l1_polls_def] >>
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
  sys_poll fes u = SOME (out, w2 with hist := hh, ev) ∧
  pf_after lfd hw hs ps fes (poll_revents fes out, w2, []) = SOME (rdy, (w', ps'), log, tevs) ∧
  tr_from tr (hp ++ [pcall fes]) w2.hist (LENGTH tevs) ⇒
  pround lfd hw hs (lift tr hp u, ps) [] =
    SOME (ssnap rdy [], (lift tr (hp ++ [pcall fes] ++ DROP (LENGTH w2.hist) w'.hist) w', ps'),
          log, ev :: tevs)
Proof
  strip_tac >> gvs[] >>
  drule_then assume_tac lift_do_buf >>
  simp[pround_def, pf_tail_after, l1_polls_def] >>
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
                 IO_event (ExtCall «sys_poll») [0w]
                   (ZIP (poll_buf fes, out))) ∧
         rv_quiet (poll_revents fes out) ∧ ∃x. out = poll_out x (poll_buf fes) ∧ ¬any_revents x (pfes fes)’
    by (irule sys_poll_idle >> fs[]) >>
  ‘sfor m ifds bz (full ++ REPLICATE i esnap) h’ by (irule sfor_skips >> fs[bidle_def]) >>
  drule sfor_now >> strip_tac >>
  ‘tr (hp ++ REPLICATE i (pcall fes)) = (l0_ticks «sys_poll» i w).hist’ by simp[] >>
  ‘pf_idle lfd hw ps (ifds h) ∧ new_actions (log_of m) h = []’ by fs[bidle_def] >>
  drule_all pround_idle_lift >> strip_tac >>
  qexists_tac ‘es ++ [IO_event (ExtCall «sys_poll») [0w]
                        (ZIP (poll_buf fes, out))]’ >>
  qpat_x_assum ‘fes = _’ SUBST_ALL_TAC >>
  gvs[ADD_CLAUSES, prounds_def, REPLICATE_SNOC_CONS_APP, epoll_def] >>
  qexists_tac ‘x’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The translation around a blocking poll, and inside a round
   ------------------------------------------------------------------------ *)

Theorem trw_reps:
  bw H = SOME (SOME k) ⇒
  (∀j. j ≤ k ⇒ trw bw H (REPLICATE j c) = H) ∧
  (∀zs. trw bw H (REPLICATE (SUC k) c ++ zs) = trw bw (H ++ [unblk c]) zs)
Proof
  rw[]
  >- (Cases_on ‘j’ >> simp[trw_def])
  >> simp[trw_def, DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem sys_pollb_hist:
  sys_pollb fes w = SOME (INL (out, w2, ev)) ⇒
  w2.hist = w.hist ++ [(«sys_poll», pollb_conf, poll_buf fes)]
Proof
  rw[sys_pollb_def, l0_ffi_fn_def, AllCaseEqs()] >> simp[]
QED

Theorem unblk_pcall:
  unblk (pcall fes) = («sys_poll», pollb_conf, poll_buf fes)
Proof
  simp[unblk_def, pollb_conf_def]
QED

Theorem lift_reindex:
  lift tr v.hist v = reindex tr v
Proof
  simp[lift_def, reindex_def, l0world_component_equality]
QED

(* No blocking poll starts strictly inside a round, nor at its start if
   the round is not idle *)
Theorem bwait_none_in_round:
  brounds lfd hw ifds bz m ws0 n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m ws0 (SUC n) = SOME (BRun h' (w', ps') evs' logs') ∧
  (pre ≠ [] ∨ ¬bidle lfd hw ifds bz m h ps) ∧
  LENGTH w.hist + LENGTH pre + LENGTH cs ≤ LENGTH w'.hist ⇒
  ∀j. j < LENGTH cs ⇒ bwait lfd hw ifds bz m ws0 (w.hist ++ pre ++ TAKE j cs) = NONE
Proof
  rpt strip_tac >>
  (Cases_on ‘pre = [] ∧ j = 0’
   >- (gvs[] >> qpat_x_assum ‘brounds _ _ _ _ _ _ n = _’ (assume_tac o MATCH_MP bwait_at) >> fs[]) >>
   drule_then (drule_then irule) bwait_between >>
   ‘LENGTH (TAKE j cs) = j’ by simp[LENGTH_TAKE] >>
   simp[] >> Cases_on ‘pre’ >> fs[])
QED

(* ------------------------------------------------------------------------
   The simulation
   ------------------------------------------------------------------------ *)

(* After the blocking run's history kept, in state (w, ps), with events evs:
   the PF run in the reindexed world has reached the same L1 state, in the
   lifted world, with a history the server cannot tell from kept and events
   evrel-related to evs *)
Definition binv_at_def:
  binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs kept w ps evs ⇔
    prounds lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) N =
      SOME (full, (lift (btr lfd hw ifds bz m (w0, ps0)) (w0.hist ++ xs) w, ps), pevs, plogs) ∧
    trs (bwait lfd hw ifds bz m (w0, ps0)) w0.hist xs w.hist ∧
    sfor m ifds bz full kept ∧ evrel pevs evs
End

Definition binv_def:
  binv lfd hw ifds bz m w0 ps0 kept w ps evs ⇔
    ∃N full xs pevs plogs. binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs kept w ps evs
End

Theorem btr_walk:
  trs (bwait lfd hw ifds bz m (w0, ps0)) w0.hist xs H ⇒
  ∀zs. btr lfd hw ifds bz m (w0, ps0) (w0.hist ++ xs ++ zs) =
       trw (bwait lfd hw ifds bz m (w0, ps0)) H zs
Proof
  rw[btr_def] >> REWRITE_TAC[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  drule trw_append >> simp[]
QED

Theorem binv_start:
  binv lfd hw ifds bz m w0 ps0 [] w0 ps0 []
Proof
  rw[binv_def, binv_at_def] >> qexistsl_tac [‘0’, ‘[]’, ‘[]’, ‘[]’, ‘[]’] >>
  simp[prounds_def, lift_reindex, trs_rules, evrel_rules]
QED

(* The calls of a round that is not idle, or after its blocking poll,
   stand for themselves *)
Theorem tr_from_round:
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BRun h' (w', ps') evs' logs') ∧
  (pre ≠ [] ∨ ¬bidle lfd hw ifds bz m h ps) ∧
  LENGTH w.hist + LENGTH pre + L ≤ LENGTH w'.hist ∧
  (∀zs. tr (hp ++ zs) = trw (bwait lfd hw ifds bz m (w0, ps0)) (w.hist ++ pre) zs) ⇒
  tr_from tr hp (w.hist ++ pre) L ∧
  ∀cs. LENGTH cs ≤ L ⇒
       trs (bwait lfd hw ifds bz m (w0, ps0)) (w.hist ++ pre) cs (w.hist ++ pre ++ cs)
Proof
  strip_tac >>
  ‘∀cs j. LENGTH cs ≤ L ∧ j < LENGTH cs ⇒
          bwait lfd hw ifds bz m (w0, ps0) (w.hist ++ pre ++ TAKE j cs) = NONE’
    by (rpt strip_tac >> irule bwait_none_in_round >> simp[] >>
        qexistsl_tac [‘evs’, ‘evs'’, ‘h’, ‘h'’, ‘logs’, ‘logs'’, ‘n’, ‘ps’, ‘ps'’, ‘w'’] >> fs[]) >>
  rw[tr_from_def] >> TRY (irule trw_calls) >> TRY (irule trs_calls) >>
  rpt strip_tac >> qpat_assum ‘∀cs j. _’ (fn th => irule th) >> simp[]
QED

Theorem tr_from_after:
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BRun h' (w', ps') evs' logs') ∧
  pre ≠ [] ∧
  LENGTH w.hist + LENGTH pre + L ≤ LENGTH w'.hist ∧
  (∀zs. tr (hp ++ zs) = trw (bwait lfd hw ifds bz m (w0, ps0)) (w.hist ++ pre) zs) ⇒
  tr_from tr hp (w.hist ++ pre) L ∧
  ∀cs. LENGTH cs ≤ L ⇒
       trs (bwait lfd hw ifds bz m (w0, ps0)) (w.hist ++ pre) cs (w.hist ++ pre ++ cs)
Proof
  strip_tac >>
  ‘∀cs j. LENGTH cs ≤ L ∧ j < LENGTH cs ⇒
          bwait lfd hw ifds bz m (w0, ps0) (w.hist ++ pre ++ TAKE j cs) = NONE’
    by (rpt strip_tac >> irule bwait_none_in_round >> simp[] >>
        qexistsl_tac [‘evs’, ‘evs'’, ‘h’, ‘h'’, ‘logs’, ‘logs'’, ‘n’, ‘ps’, ‘ps'’, ‘w'’] >> fs[]) >>
  rw[tr_from_def] >> TRY (irule trw_calls) >> TRY (irule trs_calls) >>
  rpt strip_tac >> qpat_assum ‘∀cs j. _’ (fn th => irule th) >> simp[]
QED

(* A round that is not idle: the PF round, in the lifted world *)
Theorem binv_plain:
  binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs h w ps evs ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) =
    SOME (BRun (h ++ [ssnap rdy rs]) (w', ps') (evs ++ (evs1 ++ tevs)) logs') ∧
  ¬bidle lfd hw ifds bz m h ps ∧
  pacts lfd (w, ps) (new_actions (log_of m) h) = SOME (rs, evs1, (w1, ps1)) ∧
  pf_tail lfd hw (ifds h) (w1, ps1) = SOME (rdy, (w', ps'), log, tevs) ⇒
  binv_at lfd hw ifds bz m w0 ps0 (SUC N) (full ++ [ssnap rdy rs])
    (xs ++ DROP (LENGTH w.hist) w'.hist) (pevs ++ (evs1 ++ tevs)) (plogs ++ [log])
    (h ++ [ssnap rdy rs]) w' ps' (evs ++ (evs1 ++ tevs))
Proof
  rw[binv_at_def] >>
  qabbrev_tac ‘tr = btr lfd hw ifds bz m (w0, ps0)’ >>
  imp_res_tac hgrows_pacts >> imp_res_tac hgrows_tail >>
  ‘hgrows w w' (LENGTH evs1 + LENGTH tevs)’ by metis_tac[hgrows_trans] >>
  ‘∃cs. w'.hist = w.hist ++ cs ∧ LENGTH cs = LENGTH evs1 + LENGTH tevs’ by fs[hgrows_def] >>
  ‘∀zs. tr (w0.hist ++ xs ++ zs) = trw (bwait lfd hw ifds bz m (w0, ps0)) w.hist zs’
    by (unabbrev_all_tac >> drule btr_walk >> simp[]) >>
  mp_tac (Q.INST [‘pre’ |-> ‘[] : lcall list’,
                  ‘L’ |-> ‘LENGTH (evs1 : io_event list) + LENGTH (tevs : io_event list)’,
                  ‘hp’ |-> ‘w0.hist ++ xs’, ‘h'’ |-> ‘h ++ [ssnap rdy rs]’,
                  ‘evs'’ |-> ‘(evs : io_event list) ++ evs1 ++ tevs’] tr_from_round) >>
  (impl_tac >- (unabbrev_all_tac >> fs[])) >>
  strip_tac >> fs[] >>
  drule_all pround_lift >> strip_tac >>
  drule sfor_now >> strip_tac >>
  qpat_assum ‘w'.hist = _’ (fn th => REWRITE_TAC[th, DROP_LENGTH_APPEND]) >>
  rpt conj_tac
  >- (simp[prounds_def] >> gvs[DROP_LENGTH_APPEND] >> REWRITE_TAC[APPEND_ASSOC])
  >- (irule trs_append >> goal_assum drule >> simp[])
  >- (irule sfor_snoc >> simp[])
  >> REWRITE_TAC[GSYM APPEND_ASSOC] >> irule evrel_append >> simp[]
QED

(* An idle round: k idle PF rounds, then the PF round whose poll finds
   what the blocking poll found *)
Theorem binv_idle:
  bquiet m ifds bz ∧
  binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs h w ps evs ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) =
    SOME (BRun (h ++ [ssnap rdy []]) (w', ps') (evs ++ (ev :: tevs)) logs') ∧
  bidle lfd hw ifds bz m h ps ∧
  sys_pollb (pf_poll_set lfd hw ps (ifds h)) w = SOME (INL (out, w2, ev)) ∧
  pf_after lfd hw (ifds h) ps (pf_poll_set lfd hw ps (ifds h))
    (poll_revents (pf_poll_set lfd hw ps (ifds h)) out, w2, []) = SOME (rdy, (w', ps'), log, tevs) ⇒
  ∃k es.
    pollb_wait (pf_poll_set lfd hw ps (ifds h)) w = SOME k ∧
    EVERY (epoll (pf_poll_set lfd hw ps (ifds h))) es ∧ LENGTH es = k ∧
    ev = IO_event (ExtCall «sys_poll») (pollb_conf)
           (ZIP (poll_buf (pf_poll_set lfd hw ps (ifds h)), out)) ∧
    binv_at lfd hw ifds bz m w0 ps0 (SUC (N + k))
      (full ++ REPLICATE k esnap ++ [ssnap rdy []])
      (xs ++ REPLICATE k (pcall (pf_poll_set lfd hw ps (ifds h))) ++
       [pcall (pf_poll_set lfd hw ps (ifds h))] ++ DROP (LENGTH w2.hist) w'.hist)
      (pevs ++ es ++
       (IO_event (ExtCall «sys_poll») [0w]
          (ZIP (poll_buf (pf_poll_set lfd hw ps (ifds h)), out)) :: tevs))
      (plogs ++ REPLICATE k [] ++ [log]) (h ++ [ssnap rdy []]) w' ps' (evs ++ (ev :: tevs))
Proof
  REWRITE_TAC[binv_at_def] >> rpt strip_tac >>
  qabbrev_tac ‘tr = btr lfd hw ifds bz m (w0, ps0)’ >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw ps (ifds h)’ >>
  ‘pf_idle lfd hw ps (ifds h) ∧ new_actions (log_of m) h = [] ∧ ¬bz h’ by fs[bidle_def] >>
  ‘poll_ok fes’
    by simp[] >>
  ‘∃k. pollb_wait fes w = SOME k’
    by (Cases_on ‘pollb_wait fes w’ >> simp[] >>
        mp_tac (Q.SPECL [‘fes’, ‘w’] (Q.GENL [‘fes’, ‘u’] (cj 1 sys_pollb_wait))) >> simp[]) >>
  drule (cj 2 sys_pollb_wait) >> strip_tac >> gvs[] >>
  ‘fes = pf_poll_set lfd hw ps (ifds h)’ by simp[Abbr ‘fes’] >>
  ‘bwait lfd hw ifds bz m (w0, ps0) w.hist = SOME (SOME k)’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n = _’ (mp_tac o MATCH_MP bwait_at) >>
        asm_rewrite_tac[] >> qpat_x_assum ‘fes = _’ (fn th => REWRITE_TAC[GSYM th]) >>
        asm_rewrite_tac[]) >>
  ‘∀zs. tr (w0.hist ++ xs ++ zs) = trw (bwait lfd hw ifds bz m (w0, ps0)) w.hist zs’
    by (simp[Abbr ‘tr’] >> drule btr_walk >> simp[]) >>
  drule (Q.INST [‘c’ |-> ‘pcall fes’] trw_reps) >> disch_then (strip_assume_tac o Q.SPEC ‘fes’) >>
  ‘v.hist = w.hist ++ [unblk (pcall fes)]’
    by (qpat_assum ‘sys_pollb _ _ = _’ (assume_tac o MATCH_MP sys_pollb_hist) >>
        pop_assum SUBST1_TAC >> REWRITE_TAC[unblk_pcall]) >>
  (* the k idle PF rounds *)
  ‘∀j. j ≤ k ⇒ tr (w0.hist ++ xs ++ REPLICATE j (pcall fes)) = w.hist’
    by (rpt strip_tac >> qpat_assum ‘∀zs. tr _ = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘∀j. j ≤ k ⇒ _’ irule >> simp[]) >>
  mp_tac (Q.INST [‘ws0’ |-> ‘(reindex tr w0, ps0)’, ‘hp’ |-> ‘w0.hist ++ xs’,
                  ‘evs’ |-> ‘pevs : io_event list’, ‘logs’ |-> ‘plogs : fetched list list’]
            (Q.SPEC ‘k’ pf_idle_rounds)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (REWRITE_TAC[poll_ok_T] >> NO_TAC) >>
                disj2_tac >> qexists_tac ‘k’ >>
                qpat_assum ‘pollb_wait fes w = SOME k’ (fn th => REWRITE_TAC[th, LESS_EQ_REFL]))) >>
  strip_tac >>
  (* the round after the blocking poll *)
  drule hgrows_after >> strip_tac >>
  qpat_x_assum ‘hgrows v w' _’ (strip_assume_tac o REWRITE_RULE[hgrows_def]) >>
  ‘LENGTH tevs = LENGTH cs’ by (qpat_x_assum ‘LENGTH tevs = _’ mp_tac >> simp[]) >>
  ‘[unblk (pcall fes)] ≠ []’ by simp[] >>
  ‘LENGTH w.hist + LENGTH [unblk (pcall fes)] + LENGTH tevs ≤ LENGTH w'.hist’
    by (qpat_assum ‘w'.hist = _’ SUBST1_TAC >> qpat_assum ‘v.hist = _’ SUBST1_TAC >>
        qpat_assum ‘LENGTH tevs = LENGTH cs’ SUBST1_TAC >> simp[]) >>
  ‘∀zs. tr (w0.hist ++ xs ++ REPLICATE (SUC k) (pcall fes) ++ zs) =
        trw (bwait lfd hw ifds bz m (w0, ps0)) (w.hist ++ [unblk (pcall fes)]) zs’
    by (gen_tac >>
        qpat_assum ‘∀zs. tr _ = _’ (qspec_then ‘REPLICATE (SUC k) (pcall fes) ++ zs’ mp_tac) >>
        REWRITE_TAC[APPEND_ASSOC] >> disch_then SUBST1_TAC >>
        qpat_assum ‘∀zs. trw _ _ (_ ++ zs) = _’ (fn th => REWRITE_TAC[th])) >>
  drule_all tr_from_after >> strip_tac >>
  (* the wake-up round in the PF run *)
  ‘tr (w0.hist ++ xs ++ REPLICATE k (pcall fes)) = (l0_ticks «sys_poll» k w).hist’
    by (REWRITE_TAC[ticks_hist_ch] >> qpat_assum ‘∀j. j ≤ k ⇒ tr _ = _’ irule >> simp[]) >>
  ‘tr_from tr (w0.hist ++ xs ++ REPLICATE k (pcall fes) ++ [pcall fes]) v.hist (LENGTH tevs)’
    by (REWRITE_TAC[REPLICATE_SNOC_CONS_APP] >> qpat_assum ‘v.hist = _’ SUBST1_TAC >>
        qpat_assum ‘tr_from _ _ _ _’ mp_tac >> REWRITE_TAC[REPLICATE]) >>
  qpat_assum ‘fes = _’ (fn th => assume_tac th) >>
  drule_all pround_wake_lift >> strip_tac >>
  ‘sfor m ifds bz (full ++ REPLICATE k esnap) h’
    by (irule sfor_skips >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule sfor_now >> strip_tac >>
  ‘DROP (LENGTH v.hist) w'.hist = cs’
    by (qpat_assum ‘w'.hist = _’ SUBST1_TAC >> REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  qexists_tac ‘es’ >>
  qpat_assum ‘LENGTH es = k’ (fn th => REWRITE_TAC[th]) >>
  qpat_assum ‘fes = _’ (fn th => REWRITE_TAC[GSYM th]) >>
  qpat_assum ‘DROP _ _ = cs’ (fn th => REWRITE_TAC[th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (REWRITE_TAC[] >> NO_TAC)
  >- (REWRITE_TAC[prounds_def] >>
      qpat_assum ‘prounds _ _ _ _ _ (N + k) = _’ (fn th => REWRITE_TAC[th]) >>
      rpt (CHANGED_TAC (REWRITE_TAC[pairTheory.pair_case_def, optionTheory.option_case_def] >> BETA_TAC)) >>
      qpat_assum ‘new_actions _ (full ++ _) = _’ (fn th => REWRITE_TAC[th]) >>
      qpat_assum ‘new_actions _ h = []’ (fn th => REWRITE_TAC[th]) >>
      qpat_assum ‘ifds (full ++ _) = _’ (fn th => REWRITE_TAC[th]) >>
      qpat_assum ‘pround _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
      rpt (CHANGED_TAC (REWRITE_TAC[pairTheory.pair_case_def, optionTheory.option_case_def] >> BETA_TAC)) >>
      qpat_assum ‘DROP _ _ = cs’ (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[APPEND_ASSOC])
  >- (REWRITE_TAC[GSYM APPEND_ASSOC] >> irule trs_append >> qexists_tac ‘w.hist’ >>
      conj_tac >- first_assum ACCEPT_TAC >>
      REWRITE_TAC[APPEND_ASSOC, REPLICATE_SNOC_CONS] >> REWRITE_TAC[APPEND] >>
      irule trs_poll >> REWRITE_TAC[LENGTH_REPLICATE] >>
      qpat_assum ‘bwait _ _ _ _ _ _ w.hist = _’ (fn th => REWRITE_TAC[th]) >>
      conj_tac >- (qexists_tac ‘k’ >> REWRITE_TAC[]) >>
      qpat_assum ‘w'.hist = _’ SUBST1_TAC >> qpat_assum ‘v.hist = _’ SUBST1_TAC >>
      qpat_assum ‘∀cs. LENGTH cs ≤ LENGTH tevs ⇒ _’ irule >>
      qpat_assum ‘LENGTH tevs = LENGTH cs’ (fn th => REWRITE_TAC[th, LESS_EQ_REFL]))
  >- (irule sfor_snoc >> first_assum ACCEPT_TAC)
  >> ‘∀(e : io_event) l. e :: l = [e] ++ l’ by REWRITE_TAC[APPEND] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  REWRITE_TAC[APPEND_ASSOC, APPEND_NIL] >> irule evrel_append >>
  irule evrel_poll >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexists_tac ‘fes’ >> first_assum ACCEPT_TAC
QED

(* MAIN, (S2): every round of the blocking run is matched by the PF run in
   the reindexed world: the same L1 state, the lifted world, a history the
   server cannot tell from the blocking run's, and evrel-related events *)
Theorem l1b_refines_pf:
  bquiet m ifds bz ⇒
  ∀n kept w ps evs logs.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun kept (w, ps) evs logs) ⇒
    binv lfd hw ifds bz m w0 ps0 kept w ps evs
Proof
  strip_tac >> Induct >- (rw[brounds_def] >> simp[binv_start]) >>
  rpt strip_tac >> drule brounds_SUC_BRun >> strip_tac >>
  PairCases_on ‘ws’ >> first_x_assum drule >> REWRITE_TAC[binv_def] >> strip_tac >>
  drule bround_cases >> strip_tac >> gvs[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  REWRITE_TAC[binv_def, GSYM APPEND_ASSOC, APPEND]
  >- (drule_all binv_plain >> strip_tac >> metis_tac[])
  >> drule_all binv_idle >> strip_tac >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Asleep: the PF run polls and finds nothing, for ever
   ------------------------------------------------------------------------ *)

Theorem trw_never:
  bw H = SOME NONE ⇒ ∀zs. trw bw H zs = H
Proof
  strip_tac >> Cases >> simp[trw_def]
QED

Theorem brounds_BSlept:
  ∀n h evs cb.
    brounds lfd hw ifds bz m ws0 n = SOME (BSlept h evs cb) ⇒
    ∃n0 w ps evs0 logs revs.
      brounds lfd hw ifds bz m ws0 n0 = SOME (BRun h (w, ps) evs0 logs) ∧
      bround lfd hw (¬bz h) (ifds h) (w, ps) (new_actions (log_of m) h) =
        SOME (BAsleep revs cb) ∧
      evs = evs0 ++ revs
Proof
  Induct >> simp[brounds_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> rw[]
  >> TRY (first_x_assum drule >> strip_tac >> metis_tac[] >> NO_TAC)
  >> PairCases_on ‘ws’ >> metis_tac[]
QED

Theorem bround_asleep:
  bround lfd hw (¬bz h) (ifds h) (w, ps) (new_actions (log_of m) h) = SOME (BAsleep revs cb) ⇒
  bidle lfd hw ifds bz m h ps ∧ revs = [] ∧
  sys_pollb (pf_poll_set lfd hw ps (ifds h)) w = SOME (INR cb)
Proof
  rw[bround_def, AllCaseEqs()] >> gvs[bidle_def]
QED

Theorem sys_pollb_INR:
  sys_pollb fes w = SOME (INR cb) ⇒ cb = (pollb_conf, poll_buf fes)
Proof
  rw[sys_pollb_def, AllCaseEqs()]
QED

(* MAIN, (S2) asleep: when the blocking run sleeps in a poll of fes, the PF
   run in the reindexed world polls fes and finds nothing, for ever *)
Theorem l1b_asleep_pf:
  bquiet m ifds bz ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BSlept kept evs cb) ⇒
  ∃fes N full xs pevs plogs w ps.
    cb = (pollb_conf, poll_buf fes) ∧
    sfor m ifds bz full kept ∧ evrel pevs evs ∧
    ∀i. ∃es.
      prounds lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) (N + i) =
        SOME (full ++ REPLICATE i esnap,
              (lift (btr lfd hw ifds bz m (w0, ps0)) (w0.hist ++ xs ++ REPLICATE i (pcall fes))
                    (l0_ticks «sys_poll» i w), ps),
              pevs ++ es, plogs ++ REPLICATE i []) ∧
      EVERY (epoll fes) es ∧ LENGTH es = i
Proof
  strip_tac >> drule brounds_BSlept >> strip_tac >>
  drule bround_asleep >> strip_tac >>
  ‘evs = evs0’ by (qpat_x_assum ‘evs = _’ SUBST1_TAC >> qpat_assum ‘revs = []’ SUBST1_TAC >>
                   REWRITE_TAC[APPEND_NIL]) >>
  qpat_x_assum ‘evs = _ ++ _’ kall_tac >> pop_assum SUBST_ALL_TAC >>
  ‘binv lfd hw ifds bz m w0 ps0 kept w ps evs0’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n0 = _’ mp_tac >>
        qpat_assum ‘bquiet _ _ _’ (fn th => REWRITE_TAC[MATCH_MP l1b_refines_pf th])) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[binv_def, binv_at_def]) >>
  qabbrev_tac ‘tr = btr lfd hw ifds bz m (w0, ps0)’ >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw ps (ifds kept)’ >>
  ‘fes = pf_poll_set lfd hw ps (ifds kept)’ by simp[Abbr ‘fes’] >>
  ‘cb = (pollb_conf, poll_buf fes)’
    by (qpat_assum ‘sys_pollb _ _ = _’ (mp_tac o MATCH_MP sys_pollb_INR) >>
        qpat_assum ‘fes = _’ (fn th => REWRITE_TAC[GSYM th])) >>
  ‘pf_idle lfd hw ps (ifds kept)’
    by (qpat_assum ‘bidle _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[bidle_def])) >>
  ‘poll_ok fes’
    by simp[] >>
  ‘pollb_wait fes w = NONE’
    by (mp_tac (Q.SPECL [‘fes’, ‘w’] (Q.GENL [‘fes’, ‘u’] (cj 1 sys_pollb_wait))) >>
        disch_then (SUBST1_TAC o GSYM) >>
        qpat_assum ‘cb = _’ (SUBST1_TAC o GSYM) >> first_assum ACCEPT_TAC) >>
  ‘bwait lfd hw ifds bz m (w0, ps0) w.hist = SOME NONE’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n0 = _’ (mp_tac o MATCH_MP bwait_at) >>
        qpat_assum ‘bidle _ _ _ _ _ _ _’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘fes = _’ (fn th => REWRITE_TAC[GSYM th]) >>
        qpat_assum ‘pollb_wait _ _ = _’ (fn th => REWRITE_TAC[th])) >>
  ‘∀j. tr (w0.hist ++ xs ++ REPLICATE j (pcall fes)) = w.hist’
    by (rpt strip_tac >> qunabbrev_tac ‘tr’ >>
        qpat_assum ‘trs _ _ _ _’ (mp_tac o MATCH_MP btr_walk) >>
        disch_then (fn th => REWRITE_TAC[th]) >>
        drule trw_never >> disch_then (fn th => REWRITE_TAC[th])) >>
  qexistsl_tac [‘fes’, ‘N’, ‘full’, ‘xs’, ‘pevs’, ‘plogs’, ‘w’, ‘ps’] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >>
  mp_tac (Q.INST [‘ws0’ |-> ‘(reindex tr w0, ps0)’, ‘hp’ |-> ‘w0.hist ++ xs’, ‘h’ |-> ‘kept’,
                  ‘evs’ |-> ‘pevs : io_event list’, ‘logs’ |-> ‘plogs : fetched list list’]
            (Q.SPEC ‘i’ pf_idle_rounds)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                TRY (disj1_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
                rpt strip_tac >> qpat_assum ‘∀j. tr _ = _’ (fn th => REWRITE_TAC[th]))) >>
  REWRITE_TAC[]
QED
