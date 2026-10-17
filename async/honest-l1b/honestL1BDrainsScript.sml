(*
  L3-09 (S3): D(c) (drains, #153 821835ed2: once the program sends no more
  on c, c empties) transfers from the blocking trace to the PF trace.  A PF
  prefix is anchored at a blocking prefix bp with the same non-poll events
  (its world is bp's after some steps of time, which change no sends and
  add nothing in flight).  The PF image of a blocking extension of bp
  either extends the PF prefix or stops short of it by polls only
  (image_cmp), so the PF trace's "no more sends" gives the blocking
  trace's, and the blocking trace's empty channel shows on the PF image or
  already on the PF prefix.

  MAIN: drains_transfer.
*)
Theory honestL1BDrains
Ancestors
  honestL1BFaith honestL1BTransfer honestL1BChan honestL1BCorr honestL1BObs honestL1BRuns
  honestL1BReplay honestL1BSim honestL1BRefine honestL1BPoll honestL1BModel
  honestL1BStmts honestL0Reindex honestL0Part honestL1PFRound honestL1Model
  honestL0World honestL0 llist
Libs
  preamble

Theorem sys_poll_chans:
  sys_poll fes x = SOME (out, x', ev) ⇒ x'.chans = (l0_tick «sys_poll» x).chans
Proof
  rw[sys_poll_def] >> drule l0_do_buf_cases >> rw[] >>
  gvs[l0_call_def, AllCaseEqs()]
QED

(* The blocking poll's world, as steps of time *)
Theorem pollb_chans:
  poll_ok fes ∧ pollb_wait fes w = SOME k ∧ sys_pollb fes w = SOME (INL (out, v, ev)) ⇒
  v.chans = (l0_ticks «sys_poll» (SUC k) w).chans
Proof
  strip_tac >> drule (cj 2 sys_pollb_wait) >> strip_tac >> gvs[] >>
  drule sys_poll_chans >> simp[tick_ticks]
QED

Theorem world_at_mono_dmono:
  world_at w0 a = SOME x ∧ world_at w0 (a ++ b) = SOME y ⇒ dmono c x y
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >> gvs[] >> metis_tac[replay_dmono]
QED

Theorem brounds_evs_mono:
  ∀m' m h ws e logs h' ws' e' logs'.
    brounds lfd hw ifds bz mm ws0 m = SOME (BRun h ws e logs) ∧
    brounds lfd hw ifds bz mm ws0 m' = SOME (BRun h' ws' e' logs') ∧ m ≤ m' ⇒ e ≼ e'
Proof
  Induct >> rw[] >- gvs[] >>
  Cases_on ‘m = SUC m'’ >> gvs[] >>
  drule brounds_SUC_BRun >> strip_tac >> gvs[] >>
  ‘e ≼ evs’ by (first_x_assum (qspecl_then [‘m’, ‘h’, ‘ws’, ‘e’, ‘logs’] mp_tac) >> simp[]) >>
  fs[IS_PREFIX_APPEND] >> qexists_tac ‘l ++ revs’ >> simp[]
QED

Theorem brounds_after_slept:
  ∀m'. brounds lfd hw ifds bz mm ws0 m = SOME (BSlept h evs cb) ∧ m ≤ m' ⇒
       brounds lfd hw ifds bz mm ws0 m' = SOME (BSlept h evs cb)
Proof
  Induct >> rw[] >> Cases_on ‘m = SUC m'’ >> gvs[] >> simp[brounds_def]
QED

(* When the blocking run falls asleep after the round with events bp, its
   prefixes are bp's *)
Theorem asleep_prefixes:
  brounds lfd hw ifds bz mm ws0 n0 = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm ws0 (SUC n0) = SOME (BSlept h' evs' cb) ∧
  bpre lfd hw ifds bz mm ws0 bevs ⇒ bevs ≼ bp
Proof
  strip_tac >>
  ‘evs' = bp’
    by (qpat_x_assum ‘brounds _ _ _ _ _ _ (SUC n0) = _’ mp_tac >>
        simp[brounds_def, AllCaseEqs()] >> rw[] >> drule bround_asleep >> rw[] >> simp[]) >>
  gvs[bpre_def]
  >- (Cases_on ‘n ≤ n0’
      >- (irule IS_PREFIX_TRANS >> qexists_tac ‘evs’ >> simp[] >>
          irule brounds_evs_mono >> metis_tac[])
      >> ‘brounds lfd hw ifds bz mm ws0 n = SOME (BSlept h' bp cb)’
           by (irule brounds_after_slept >> qexists_tac ‘SUC n0’ >> simp[]) >> gvs[])
  >> Cases_on ‘SUC n0 ≤ n’
  >- (‘brounds lfd hw ifds bz mm ws0 n = SOME (BSlept h' bp cb)’
        by (irule brounds_after_slept >> qexists_tac ‘SUC n0’ >> simp[]) >> gvs[])
  >> ‘brounds lfd hw ifds bz mm ws0 n0 = SOME (BSlept h'' evs cb')’
       by (irule brounds_after_slept >> qexists_tac ‘n’ >> simp[]) >> gvs[]
QED

Theorem pf_after_evs:
  pf_after lfd hw hs ps fes (rv, w1, pevs) = SOME (rdy, ws, log, tevs) ⇒ ∃r. tevs = pevs ++ r
Proof
  rw[pf_after_def, AllCaseEqs()] >> simp[]
QED

(* An idle round that does not fail polls a well-formed set *)
Theorem idle_poll_ok:
  brounds lfd hw ifds bz mm ws0 n = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm ws0 (SUC n) ≠ NONE ∧ bidle lfd hw ifds bz mm h ps ⇒
  poll_ok (pf_poll_set lfd hw ps (ifds h))
Proof
  simp[]
QED

(* The blocking prefix just after an idle round's poll returns *)
Theorem idle_wake_pre:
  l0_rely w0 ∧
  brounds lfd hw ifds bz mm (w0, ps0) n = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm (w0, ps0) (SUC n) ≠ NONE ∧ bidle lfd hw ifds bz mm h ps ∧
  pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = SOME k ⇒
  ∃ev v. bpre lfd hw ifds bz mm (w0, ps0) (bp ++ [ev]) ∧ world_at w0 (bp ++ [ev]) = SOME v ∧
         v.chans = (l0_ticks «sys_poll» (SUC k) wb).chans
Proof
  strip_tac >> drule_all idle_poll_ok >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw ps (ifds h)’ >>
  ‘world_at w0 bp = SOME wb ∧ l0_rely wb’ by metis_tac[bworld] >>
  drule (cj 2 sys_pollb_wait) >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘sys_pollb fes wb = SOME (INL (out, v, evb))’ >>
  qexistsl_tac [‘evb’, ‘v’] >> rpt conj_tac
  >- (Cases_on ‘pf_after lfd hw (ifds h) ps fes (poll_revents fes out, v, [evb])’
      >- (qpat_x_assum ‘brounds _ _ _ _ _ _ (SUC n) ≠ NONE’ mp_tac >>
          fs[bidle_def] >> simp[brounds_def, bround_def])
      >> rename1 ‘SOME r’ >> PairCases_on ‘r’ >>
      drule pf_after_evs >> strip_tac >>
      irule bpre_round >> qexistsl_tac [‘bp ++ evb :: r’, ‘h ++ [ssnap r0 []]’,
                                        ‘logs ++ [r3]’, ‘SUC n’, ‘(r1, r2)’] >>
      conj_tac
      >- (fs[bidle_def] >> qunabbrev_tac ‘evb’ >> qunabbrev_tac ‘fes’ >>
          simp[brounds_def, bround_def])
      >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[])
  >- (REWRITE_TAC[world_at_append] >> asm_rewrite_tac[optionTheory.OPTION_BIND_def] >>
      BETA_TAC >> drule rplays_pollb >> simp[rplays_def])
  >> irule pollb_chans >> metis_tac[]
QED

(* An idle round whose poll never returns: the run sleeps after it *)
Theorem idle_asleep:
  brounds lfd hw ifds bz mm ws0 n = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm ws0 (SUC n) ≠ NONE ∧ bidle lfd hw ifds bz mm h ps ∧
  pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = NONE ⇒
  ∃cb. brounds lfd hw ifds bz mm ws0 (SUC n) = SOME (BSlept h bp cb)
Proof
  strip_tac >> drule_all idle_poll_ok >> strip_tac >>
  ‘sys_pollb (pf_poll_set lfd hw ps (ifds h)) wb =
     SOME (INR (pollb_conf, poll_buf (pf_poll_set lfd hw ps (ifds h))))’
    by metis_tac[sys_pollb_wait] >>
  fs[bidle_def] >> simp[brounds_def, bround_def]
QED

(* A blocking prefix's channels are a PF prefix's *)
Theorem b_reach:
  bquiet m ifds bz ∧ l0_rely w0 ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  bpre lfd hw ifds bz m (w0, ps0) bq ∧ world_at w0 bq = SOME wq ⇒
  ∃pp w. LPREFIX (fromList pp) io_p ∧
         world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp = SOME w ∧
         w.chans = wq.chans
Proof
  strip_tac >> drule_all b2p >> strip_tac >> gvs[ptrace_def] >>
  qexistsl_tac [‘pp’, ‘lift (btr lfd hw ifds bz m (w0, ps0)) hp wb’] >> simp[]
QED

(* ------------------------------------------------------------------------
   Steps of time and polls: a channel stays, its sends stay, and its bytes
   in flight do not grow
   ------------------------------------------------------------------------ *)

Definition pmono_def:
  pmono c (u : l0world) (u' : l0world) ⇔
    c < LENGTH u.chans ⇒
    c < LENGTH u'.chans ∧ (EL c u'.chans).sent = (EL c u.chans).sent ∧
    (EL c u'.chans).inflight ≤ (EL c u.chans).inflight
End

Theorem pmono_refl[simp]:
  pmono c u u
Proof
  simp[pmono_def]
QED

Theorem pmono_trans:
  pmono c u1 u2 ∧ pmono c u2 u3 ⇒ pmono c u1 u3
Proof
  rw[pmono_def] >> fs[] >> rfs[] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem pmono_hist[simp]:
  pmono c u (u' with hist := h) ⇔ pmono c u u'
Proof
  simp[pmono_def]
QED

Theorem deliver_sent[local]:
  c < LENGTH w.chans ⇒ (EL c (l0_deliver w a).chans).sent = (EL c w.chans).sent
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >>
  simp[upd_lchan_def, EL_LUPDATE, EL_APPEND1] >> rw[break_lchan_def]
QED

Theorem deliver_len_ge[local]:
  c < LENGTH w.chans ⇒ c < LENGTH (l0_deliver w a).chans
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> simp[upd_lchan_def]
QED

Theorem FOLDL_deliver_sent[local]:
  ∀as w. c < LENGTH w.chans ⇒
         c < LENGTH (FOLDL l0_deliver w as).chans ∧
         (EL c (FOLDL l0_deliver w as).chans).sent = (EL c w.chans).sent
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then ‘l0_deliver w h’ mp_tac) >>
  simp[deliver_len_ge, deliver_sent]
QED

Theorem tick_pmono:
  pmono c w (l0_tick nm w)
Proof
  rw[pmono_def]
  >- simp[l0_tick_def, FOLDL_deliver_sent]
  >- simp[l0_tick_def, FOLDL_deliver_sent]
  >> qspecl_then [‘c’, ‘w’, ‘nm’] mp_tac (Q.GENL [‘c’, ‘w’, ‘nm’] tick_inflight) >>
  simp[inflight_le_def] >> rw[] >> fs[] >>
  ‘c < LENGTH (l0_tick nm w).chans’ by simp[l0_tick_def, FOLDL_deliver_sent] >> fs[]
QED

Theorem ticks_pmono:
  ∀k w. pmono c w (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[pmono_trans, tick_pmono]
QED

(* A poll is a step of time, and (blocking) more steps of time *)
Theorem poll_ffi_pmono:
  l0_ffi_fn «sys_poll» conf bytes u = SOME (FFIreturn out u') ⇒ pmono c u u'
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> simp[] >>
  irule pmono_trans >> qexists_tac ‘l0_tick «sys_poll» u’ >> simp[tick_pmono] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[Once l0_call_def] >>
  rw[AllCaseEqs()] >> simp[ticks_pmono]
QED

Theorem polls_pmono:
  ∀ys u u'. faithful u ys ∧ EVERY is_poll ys ∧
            FOLDL l0_step (SOME u) (MAP ev_lcall ys) = SOME u' ⇒ pmono c u u'
Proof
  Induct >> rw[faithful_def] >> gvs[ev_lcall_def, l0_step_def, is_poll_def] >>
  irule pmono_trans >> qexists_tac ‘u''’ >> simp[] >>
  metis_tac[poll_ffi_pmono]
QED

(* The PF trace is faithful *)
Theorem pf_faithful:
  l0_rely w0 ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧ LPREFIX (fromList pp) io_p ⇒
  faithful (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp
Proof
  rw[ptrace_def, ppre_def] >> first_x_assum (qspec_then ‘pp’ mp_tac) >> simp[] >>
  strip_tac >> PairCases_on ‘ws’ >>
  drule fplays_prounds >> simp[fplays_def, l0_rely_reindex] >> strip_tac >>
  fs[IS_PREFIX_APPEND] >> metis_tac[faithful_prefix]
QED

(* Between two PF prefixes with the same non-poll events there are only
   polls *)
Theorem pf_poll_gap:
  l0_rely w0 ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  LPREFIX (fromList (pa ++ ys)) io_p ∧ nopoll ys = [] ∧
  world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pa = SOME a ∧
  world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) (pa ++ ys) = SOME b ⇒
  pmono c a b
Proof
  strip_tac >> drule_all pf_faithful >> strip_tac >>
  irule polls_pmono >> qexists_tac ‘ys’ >> rpt conj_tac >>
  TRY (irule faithful_drop >> qexistsl_tac [‘pa’, ‘reindex (btr lfd hw ifds bz m (w0, ps0)) w0’] >>
       fs[world_at_def, l0_replay_def] >> NO_TAC) >>
  TRY (fs[nopoll_def, FILTER_EQ_NIL, EVERY_MEM] >> NO_TAC) >>
  qpat_x_assum ‘world_at _ (pa ++ ys) = _’ mp_tac >>
  REWRITE_TAC[world_at_append] >> asm_rewrite_tac[optionTheory.OPTION_BIND_def] >>
  BETA_TAC >> REWRITE_TAC[]
QED

(* A PF prefix is anchored at a blocking prefix: the same non-poll events,
   and its world is the blocking world after some steps of time *)
Theorem p_anchor:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) pp ∧
  world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp = SOME w ⇒
  ∃bp wb x hp. bpre lfd hw ifds bz m (w0, ps0) bp ∧ world_at w0 bp = SOME wb ∧
               nopoll pp = nopoll bp ∧ w = lift (btr lfd hw ifds bz m (w0, ps0)) hp x ∧
               pmono c wb x ∧
               (¬(c < LENGTH wb.chans) ∧ c < LENGTH x.chans ⇒ (EL c x.chans).inflight = 0)
Proof
  strip_tac >> drule_all p2b >> strip_tac
  >- (qpat_x_assum ‘palign _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[palign_def]) >>
      qexistsl_tac [‘bp’, ‘wb’, ‘wb’, ‘hp’] >> simp[] >> fs[] >> rw[])
  >> qpat_x_assum ‘pmid _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[pmid_def]) >>
  ‘bpre lfd hw ifds bz m (w0, ps0) bp’ by (irule bpre_round >> metis_tac[IS_PREFIX_REFL]) >>
  qexistsl_tac [‘bp’, ‘wb’, ‘l0_ticks «sys_poll» i wb’, ‘hp’] >> simp[ticks_pmono] >> fs[] >>
  rw[] >> qspecl_then [‘i’, ‘wb’] mp_tac (Q.INST [‘nm’ |-> ‘«sys_poll»’] ticks_inflight) >>
  simp[inflight_le_def]
QED

(* The PF image of a blocking extension of bp either extends a PF prefix
   anchored at bp, or that prefix extends it by polls only *)
Theorem image_cmp:
  bquiet m ifds bz ∧ l0_rely w0 ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  LPREFIX (fromList pp) io_p ∧ nopoll pp = nopoll bp ∧
  bpre lfd hw ifds bz m (w0, ps0) (bp ++ bx) ∧ world_at w0 (bp ++ bx) = SOME wq ⇒
  ∃pq hq. LPREFIX (fromList pq) io_p ∧
          world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pq =
            SOME (lift (btr lfd hw ifds bz m (w0, ps0)) hq wq) ∧
          ((∃ys. pq = pp ++ ys) ∨ (∃ys. pp = pq ++ ys ∧ nopoll ys = []))
Proof
  strip_tac >> drule_all b2p >> strip_tac >> gvs[] >>
  rename1 ‘ppre _ _ _ _ _ pq’ >>
  ‘LPREFIX (fromList pq) io_p’ by metis_tac[ptrace_def] >>
  qexistsl_tac [‘pq’, ‘hp’] >> simp[] >>
  Cases_on ‘LENGTH pp ≤ LENGTH pq’
  >- (disj1_tac >> ‘pp ≼ pq’ by metis_tac[prefix_cmp] >> fs[IS_PREFIX_APPEND])
  >> disj2_tac >> ‘pq ≼ pp’ by (irule prefix_cmp >> metis_tac[NOT_LESS_EQUAL, LESS_IMP_LESS_OR_EQ]) >>
  fs[IS_PREFIX_APPEND] >>
  qpat_x_assum ‘pp = _’ SUBST_ALL_TAC >> fs[] >>
  ‘LENGTH (nopoll pq ++ nopoll l) = LENGTH (nopoll bp)’ by metis_tac[] >>
  ‘LENGTH (nopoll pq) = LENGTH (nopoll bp) + LENGTH (nopoll bx)’ by metis_tac[LENGTH_APPEND] >>
  Cases_on ‘nopoll l’ >> fs[]
QED

(* MAIN: D(c) (blocking ⇒ PF).  A PF prefix is anchored at a blocking
   prefix bp; the PF trace's "no more sends" gives the blocking trace's
   (PF images of extensions of bp extend the PF prefix, or stop short of
   it by polls only, which change no sends), and the blocking trace's
   empty channel shows on the PF image (or already on the PF prefix,
   when the image stops short: polls add nothing in flight) *)
Theorem drains_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  drains w0 io_b c ⇒ drains (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p c
Proof
  strip_tac >> REWRITE_TAC[drains_def] >> rpt strip_tac >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) evs’
    by metis_tac[ptrace_def] >>
  drule_all p_anchor >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
  qpat_x_assum ‘w = _’ SUBST_ALL_TAC >>
  qabbrev_tac ‘tr = btr lfd hw ifds bz m (w0, ps0)’ >>
  reverse (Cases_on ‘c < LENGTH wb.chans’)
  >- (qexistsl_tac [‘[]’, ‘lift tr hp x’] >> fs[]) >>
  ‘(EL c x.chans).sent = (EL c wb.chans).sent ∧
   (EL c x.chans).inflight ≤ (EL c wb.chans).inflight ∧ c < LENGTH x.chans’
    by fs[pmono_def] >>
  (* the blocking trace sends no more on c after bp *)
  ‘∀bx wq. LPREFIX (fromList (bp ++ bx)) io_b ∧ world_at w0 (bp ++ bx) = SOME wq ⇒
           (EL c wq.chans).sent = (EL c wb.chans).sent’
    by (rpt strip_tac >>
        ‘bpre lfd hw ifds bz m (w0, ps0) (bp ++ bx)’ by metis_tac[btrace_def] >>
        ‘dmono c wb wq’ by metis_tac[world_at_mono_dmono] >>
        ‘c < LENGTH wq.chans’ by fs[dmono_def] >>
        drule_all image_cmp >> strip_tac
        >- (gvs[] >>
            qpat_x_assum ‘∀evs' w'. LPREFIX _ _ ∧ _ ⇒ _’
              (qspecl_then [‘ys’, ‘lift tr hq wq’] mp_tac) >>
            simp[])
        >> gvs[] >>
        mp_tac (Q.INST [‘pa’ |-> ‘pq’, ‘a’ |-> ‘lift tr hq wq’, ‘b’ |-> ‘lift tr hp x’]
                  pf_poll_gap) >>
        simp[pmono_def]) >>
  qpat_x_assum ‘drains _ _ _’ (mp_tac o REWRITE_RULE[drains_def]) >>
  disch_then (qspecl_then [‘bp’, ‘wb’] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[btrace_def]) >> strip_tac >>
  ‘bpre lfd hw ifds bz m (w0, ps0) (bp ++ evs')’ by metis_tac[btrace_def] >>
  drule_all image_cmp >> strip_tac
  >- (qexistsl_tac [‘ys’, ‘lift tr hq w'’] >> gvs[])
  >> qexistsl_tac [‘[]’, ‘lift tr hp x’] >> gvs[] >>
  mp_tac (Q.INST [‘pa’ |-> ‘pq’, ‘a’ |-> ‘lift tr hq w'’, ‘b’ |-> ‘lift tr hp x’] pf_poll_gap) >>
  simp[pmono_def]
QED
