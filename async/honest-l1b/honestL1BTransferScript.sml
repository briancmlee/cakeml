(*
  L3-09 (S3): the guarantee transfers from the PF run's trace (in the
  reindexed world) to the blocking run's, predicate by predicate, through
  the prefix correspondence (honestL1BCorr: b2p, p2b).

  btrace / ptrace: io is the blocking run's / the PF run's trace (its
  finite prefixes are exactly bpre's / ppre's).

  MAIN: echo_safe_transfer, accepts_below_transfer, F2_transfer.
*)
Theory honestL1BTransfer
Ancestors
  honestL1BCorr honestL1BObs honestL1BStmts honestL1BSim honestL1BRefine honestL1BPoll
  honestL0Reindex honestEchoL0Spec honestL1BModel honestL1PFRound honestL1Steps
  honestL1Model honestL0WorldProps honestL0World honestL0 llist
Libs
  preamble

Definition btrace_def:
  btrace lfd hw ifds bz m w0 ps0 (io : io_event llist) ⇔
    ∀evs. LPREFIX (fromList evs) io ⇔ bpre lfd hw ifds bz m (w0, ps0) evs
End

Definition ptrace_def:
  ptrace lfd hw ifds bz m w0 ps0 (io : io_event llist) ⇔
    ∀evs. LPREFIX (fromList evs) io ⇔
          ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) evs
End

(* MAIN: safety (PF ⇒ blocking) *)
Theorem echo_safe_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  echo_safe_l0 io_p ⇒ echo_safe_l0 io_b
Proof
  rw[echo_safe_l0_def, btrace_def, ptrace_def] >>
  ‘bpre lfd hw ifds bz m (w0, ps0) evs’ by metis_tac[] >>
  drule_all b2p >> strip_tac >>
  first_x_assum (qspecl_then [‘pp’, ‘j’] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[nopoll_accepted]) >>
  metis_tac[nopoll_sent, nopoll_read]
QED

(* MAIN: fewer than 2^64 − 1 accepts (blocking ⇒ PF) *)
Theorem accepts_below_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  accepts_below io_b ⇒ accepts_below io_p
Proof
  rw[accepts_below_def, btrace_def, ptrace_def] >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) evs’ by metis_tac[] >>
  drule_all p2b >> rw[palign_def, pmid_def]
  >- (first_x_assum (qspec_then ‘bp’ mp_tac) >> simp[] >> metis_tac[nopoll_accepted])
  >> first_x_assum (qspec_then ‘bp’ mp_tac) >>
  ‘bpre lfd hw ifds bz m (w0, ps0) bp’ by (irule bpre_round >> metis_tac[IS_PREFIX_REFL]) >>
  simp[] >> metis_tac[nopoll_accepted]
QED

(* MAIN: F2 (blocking world ⇒ reindexed world) *)
Theorem F2_transfer:
  F2 w0 ⇒ F2 (reindex tr w0)
Proof
  simp[F2_def, reindex_def, reindex_ch_def]
QED

(* ------------------------------------------------------------------------
   Infinitely often, by counting along prefixes
   ------------------------------------------------------------------------ *)

Definition cnt_def:
  cnt Q (l : io_event list) = LENGTH (FILTER Q l)
End

Definition ioinf_def:
  ioinf Q (io : io_event llist) ⇔ ∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ Q ev
End

Theorem LPREFIX_fromList_LNTH:
  LPREFIX (fromList l) io ⇔ ∀i. i < LENGTH l ⇒ LNTH i io = SOME (EL i l)
Proof
  rw[LPREFIX_NTH, LNTH_fromList] >> eq_tac >> rw[] >> gvs[less_opt_def] >>
  TRY (first_x_assum (qspec_then ‘i’ mp_tac) >> simp[less_opt_def] >> NO_TAC) >>
  rw[] >> fs[less_opt_def]
QED

Theorem LNTH_prefix_exists:
  ∀n. LNTH n io = SOME ev ⇒
      ∃l. LPREFIX (fromList l) io ∧ LENGTH l = SUC n ∧ EL n l = ev
Proof
  rpt strip_tac >>
  ‘∀m. m ≤ n ⇒ ∃v. LNTH m io = SOME v’
    by (rpt strip_tac >> Cases_on ‘LNTH m io’ >> simp[] >>
        ‘LNTH n io = NONE’ by metis_tac[LNTH_NONE_MONO] >> fs[]) >>
  qexists_tac ‘GENLIST (λm. THE (LNTH m io)) (SUC n)’ >>
  simp[LPREFIX_fromList_LNTH] >> rw[]
  >- (first_x_assum (qspec_then ‘i’ mp_tac) >> simp[] >> strip_tac >> simp[])
  >> simp[EL_GENLIST]
QED

Theorem prefix_cmp:
  LPREFIX (fromList l1) io ∧ LPREFIX (fromList l2) io ∧ LENGTH l1 ≤ LENGTH l2 ⇒ l1 ≼ l2
Proof
  rw[LPREFIX_fromList_LNTH] >>
  ‘l1 = TAKE (LENGTH l1) l2’
    by (irule LIST_EQ >> rw[EL_TAKE] >> res_tac >> fs[]) >>
  pop_assum SUBST1_TAC >> simp[IS_PREFIX_APPEND] >>
  qexists_tac ‘DROP (LENGTH l1) l2’ >> simp[TAKE_DROP]
QED

Theorem cnt_append[simp]:
  cnt Q (a ++ b) = cnt Q a + cnt Q b
Proof
  simp[cnt_def, FILTER_APPEND]
QED

Theorem cnt_mem:
  MEM x r ∧ Q x ⇒ 0 < cnt Q r
Proof
  rw[cnt_def] >> Cases_on ‘FILTER Q r’ >> simp[] >> fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]
QED

Theorem cnt_le_LENGTH:
  cnt Q l ≤ LENGTH l
Proof
  simp[cnt_def, LENGTH_FILTER_LEQ]
QED

(* MAIN: infinitely often, as counts along prefixes *)
Theorem ioinf_cnt:
  ioinf Q io ⇔ ∀n. ∃l. LPREFIX (fromList l) io ∧ n ≤ cnt Q l
Proof
  eq_tac
  >- (strip_tac >> Induct
      >- (qexists_tac ‘[]’ >> simp[]) >>
      fs[] >> fs[ioinf_def] >>
      first_x_assum (qspec_then ‘LENGTH l’ strip_assume_tac) >>
      drule LNTH_prefix_exists >> strip_tac >>
      rename1 ‘LENGTH l' = SUC i'’ >>
      ‘l ≼ l'’ by (irule prefix_cmp >> simp[] >> qexists_tac ‘io’ >> simp[]) >>
      fs[IS_PREFIX_APPEND] >> gvs[] >>
      qexists_tac ‘l ++ l''’ >> simp[] >>
      ‘0 < cnt Q l''’
        by (irule cnt_mem >> qexists_tac ‘EL (i' − LENGTH l) l''’ >>
            ‘EL i' (l ++ l'') = EL (i' − LENGTH l) l''’ by (irule EL_APPEND2 >> simp[]) >>
            conj_tac >> TRY (irule EL_MEM >> decide_tac >> NO_TAC) >> fs[]) >>
      simp[])
  >> rw[ioinf_def] >>
  first_x_assum (qspec_then ‘SUC i’ strip_assume_tac) >>
  CCONTR_TAC >> fs[] >>
  ‘∀j. i ≤ j ∧ j < LENGTH l ⇒ ¬Q (EL j l)’
    by (rpt strip_tac >> fs[LPREFIX_fromList_LNTH] >> metis_tac[]) >>
  ‘cnt Q l = cnt Q (TAKE i l)’
    by (‘l = TAKE i l ++ DROP i l’ by simp[] >> pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
        simp[] >> simp[cnt_def, FILTER_EQ_NIL, EVERY_MEM, MEM_EL] >> rw[] >>
        fs[EL_DROP] >> first_x_assum irule >> simp[]) >>
  ‘cnt Q (TAKE i l) ≤ i’
    by (assume_tac (Q.INST [‘l’ |-> ‘TAKE i l’] cnt_le_LENGTH) >>
        fs[LENGTH_TAKE_EQ] >> rw[] >> fs[]) >>
  fs[]
QED

(* Counts along evrel *)
Theorem evrel_cnt:
  (∀fes bs. Q (IO_event (ExtCall «sys_poll») pollb_conf bs) ⇔
            Q (IO_event (ExtCall «sys_poll») [0w] bs)) ⇒
  ∀pp bp. evrel pp bp ⇒
          cnt Q bp ≤ cnt Q pp ∧
          ((∀fes e. epoll fes e ⇒ ¬Q e) ⇒ cnt Q pp = cnt Q bp)
Proof
  strip_tac >> Induct_on ‘evrel’ >> rw[cnt_def, FILTER_APPEND] >> fs[cnt_def] >>
  ‘(∀fes e. epoll fes e ⇒ ¬Q e) ⇒ FILTER Q es = []’
    by (strip_tac >> simp[FILTER_EQ_NIL] >> irule EVERY_MONOTONIC >>
        qexists_tac ‘epoll fes’ >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt strip_tac >> BETA_TAC >> res_tac) >>
  rw[] >> fs[] >> res_tac >> fs[]
QED

Theorem epoll_not_retried:
  epoll fes ev ⇒ ¬retried ev
Proof
  rw[epoll_def] >> drule poll_out_quiet >> strip_tac >>
  ‘MAP SND (ZIP (poll_buf fes, poll_out x (poll_buf fes))) = poll_out x (poll_buf fes)’
    by fs[MAP_ZIP] >>
  simp[retried_def] >>
  qpat_assum ‘MAP SND _ = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_assum ‘l0_res_of _ = _’ (fn th => REWRITE_TAC[th]) >> simp[]
QED

Theorem poll_swap_on:
  ev_on nm f (IO_event (ExtCall «sys_poll») pollb_conf bs) ⇔
  ev_on nm f (IO_event (ExtCall «sys_poll») [0w] bs)
Proof
  simp[ev_on_def] >> Cases_on ‘nm = «sys_poll»’ >>
  simp[call_fds_def, pollb_conf_def]
QED

Theorem poll_swap_retried:
  retried (IO_event (ExtCall «sys_poll») pollb_conf bs) ⇔
  retried (IO_event (ExtCall «sys_poll») [0w] bs)
Proof
  simp[retried_def]
QED

Theorem ioinf_split:
  ioinf P io ∧ ¬ioinf (λe. P e ∧ R e) io ⇒ ioinf (λe. P e ∧ ¬R e) io
Proof
  simp[ioinf_def] >> strip_tac >> qx_gen_tac ‘j’ >>
  qpat_x_assum ‘∀i. ∃i' ev. _’ (qspec_then ‘j + i’ strip_assume_tac) >>
  qexistsl_tac [‘i'’, ‘ev’] >> simp[] >>
  qpat_x_assum ‘∀i' e. _’ (qspecl_then [‘i'’, ‘ev’] mp_tac) >> simp[]
QED

Theorem ioinf_mono:
  ioinf P io ∧ (∀e. P e ⇒ P' e) ⇒ ioinf P' io
Proof
  rw[ioinf_def] >> metis_tac[]
QED

Theorem F1_ioinf:
  F1_io io ⇔ ∀nm f. ioinf (ev_on nm f) io ⇒ ioinf (λev. ev_on nm f ev ∧ ¬retried ev) io
Proof
  simp[F1_io_def, ioinf_def]
QED

(* MAIN: [F1] (blocking ⇒ PF).  If the PF trace has infinitely many calls
   nm on f, either infinitely many are not retried, or infinitely many are
   retried; retried ones are never empty polls, so the blocking trace has
   as many, its F1 gives infinitely many unretried ones there, and the PF
   trace has at least as many *)
Theorem F1_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  F1_io io_b ⇒ F1_io io_p
Proof
  rw[F1_ioinf] >>
  qabbrev_tac ‘Q1 = λev. ev_on nm f ev ∧ retried ev’ >>
  qabbrev_tac ‘Q2 = λev. ev_on nm f ev ∧ ¬retried ev’ >>
  ‘∀fes bs. Q1 (IO_event (ExtCall «sys_poll») pollb_conf bs) ⇔
            Q1 (IO_event (ExtCall «sys_poll») [0w] bs)’
    by simp[Abbr ‘Q1’, poll_swap_on, poll_swap_retried] >>
  ‘∀fes bs. Q2 (IO_event (ExtCall «sys_poll») pollb_conf bs) ⇔
            Q2 (IO_event (ExtCall «sys_poll») [0w] bs)’
    by simp[Abbr ‘Q2’, poll_swap_on, poll_swap_retried] >>
  ‘∀fes e. epoll fes e ⇒ ¬Q1 e’ by (simp[Abbr ‘Q1’] >> metis_tac[epoll_not_retried]) >>
  ‘∀pp bp. evrel pp bp ⇒ cnt Q1 pp = cnt Q1 bp’
    by (qpat_assum ‘∀fes bs. Q1 _ ⇔ _’ (assume_tac o MATCH_MP evrel_cnt) >> metis_tac[]) >>
  ‘∀pp bp. evrel pp bp ⇒ cnt Q2 bp ≤ cnt Q2 pp’
    by (qpat_assum ‘∀fes bs. Q2 _ ⇔ _’ (assume_tac o MATCH_MP evrel_cnt) >> metis_tac[]) >>
  ‘∀fes t. EVERY (epoll fes) t ⇒ cnt Q1 t = 0’
    by (rw[cnt_def, LENGTH_NIL, FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on ‘ioinf Q1 io_p’
  >- (‘ioinf Q1 io_b’
        by (fs[ioinf_cnt] >> gen_tac >>
            first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
            ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) l’
              by metis_tac[ptrace_def] >>
            drule_all p2b >> rw[palign_def, pmid_def] >> qexists_tac ‘bp’ >>
            TRY (‘bpre lfd hw ifds bz m (w0, ps0) bp’
                   by (irule bpre_round >> metis_tac[IS_PREFIX_REFL])) >>
            (conj_tac
             >- (qpat_assum ‘btrace _ _ _ _ _ _ _ _’
                   (fn th => REWRITE_TAC[REWRITE_RULE[btrace_def] th]) >> first_assum ACCEPT_TAC)) >>
            fs[] >> res_tac >> fs[]) >>
      ‘ioinf (ev_on nm f) io_b’ by (irule ioinf_mono >> qexists_tac ‘Q1’ >> simp[Abbr ‘Q1’]) >>
      first_x_assum drule >> REWRITE_TAC[] >> strip_tac >>
      ‘ioinf Q2 io_b’ by simp[Abbr ‘Q2’] >>
      fs[ioinf_cnt] >> gen_tac >>
      first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
      ‘bpre lfd hw ifds bz m (w0, ps0) l’ by metis_tac[btrace_def] >>
      drule_all b2p >> strip_tac >>
      qexists_tac ‘pp’ >> conj_tac >- metis_tac[ptrace_def] >>
      res_tac >> decide_tac)
  >> simp[Abbr ‘Q2’] >> irule ioinf_split >> fs[Abbr ‘Q1’]
QED
