(*
  L3-09 (S3), D23's observed excuse goes PF ⇒ blocking.  ep_timed_out is a
  stretch of a trace in which every poll lists the episode's fd for
  output.  The blocking trace differs from the PF trace only in idle
  stretches, where a blocking poll stands for empty polls and the poll
  that returned (evrel); an idle state polls nothing for output (no outbox
  holds bytes: pf_idle, idle_fes), so no such stretch meets an
  output-poll stretch, and the stretch is in the blocking trace too, poll
  for poll.

  MAIN: ep_timed_out_transfer.
*)
Theory honestL1BTimeout
Ancestors
  honestL1BGuar honestL1BNoFail honestL1BLive honestL1BTransfer honestL1BCorr honestL1BObs honestL1BSim honestL1BRefine honestL1BPoll
  honestL1BModel honestL1BStmts honestEchoL0Spec honestL1Inv honestL1Model
  honestL0World honestL0 llist
Libs
  preamble

(* The PF event and the blocking event of a stretch agree, up to a poll's
   blocking flag *)
Definition ev_eqp_def:
  ev_eqp e e' ⇔
    e = e' ∨ ∃bs. e = IO_event (ExtCall «sys_poll») [0w] bs ∧
                  e' = IO_event (ExtCall «sys_poll») pollb_conf bs
End

Theorem pe_fe_out[local]:
  e < 2 ⇒ SND (pe_fe (pfd_bytes (g, e))) < 2
Proof
  strip_tac >> ‘e = 0 ∨ e = 1’ by decide_tac >>
  rw[pe_fe_def, pfd_bytes_def, pe_events_def]
QED

(* An empty poll of an idle poll set lists nothing for output *)
Theorem epoll_not_out:
  epoll fes e ∧ EVERY (λ(f, e). e < 2) fes ⇒ poll_ev e ∧ ¬out_poll f e
Proof
  rw[epoll_def, poll_ev_def, out_poll_def] >>
  drule poll_out_quiet >> strip_tac >>
  simp[MAP_ZIP, poll_buf_ok] >> rpt strip_tac >>
  Cases_on ‘2 ≤ e' MOD 4’ >> simp[] >> rpt strip_tac >>
  gvs[pollfd_entries_buf, MEM_MAP] >> rename1 ‘MEM yy fes’ >> PairCases_on ‘yy’ >>
  fs[EVERY_MEM, FORALL_PROD] >> res_tac >>
  drule (Q.GEN ‘g’ pe_fe_out) >> disch_then (qspec_then ‘yy0’ mp_tac) >>
  qpat_x_assum ‘(f, e') = _’ (fn th => REWRITE_TAC[GSYM th]) >> simp[] >>
  strip_tac >> ‘e' MOD 4 = e'’ by simp[] >> fs[]
QED

(* Splitting the PF side of evrel where an output-poll stretch begins *)
Theorem evrel_split:
  ∀pp bp. evrel pp bp ⇒
    ∀xs ys. pp = xs ++ ys ∧ EVERY (λe. poll_ev e ⇒ out_poll f e) ys ⇒
            ∃bx by. bp = bx ++ by ∧ nopoll bx = nopoll xs ∧ LIST_REL ev_eqp ys by
Proof
  Induct_on ‘evrel’ >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on ‘ys’ using SNOC_CASES
      >- (gvs[] >> imp_res_tac evrel_nopoll >> simp[])
      >> fs[SNOC_APPEND] >>
      first_x_assum (qspecl_then [‘xs’, ‘l’] mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [‘bx’, ‘by ++ [x]’] >> simp[ev_eqp_def])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on ‘ys’ using SNOC_CASES
  >- (gvs[] >> imp_res_tac evrel_nopoll >> imp_res_tac nopoll_epolls >>
      simp[nopoll_def, is_poll_def])
  >> fs[SNOC_APPEND] >> qpat_x_assum ‘_ = x’ (SUBST_ALL_TAC o SYM) >>
  Cases_on ‘l = []’
  >- (gvs[] >> qexistsl_tac [‘bp’, ‘[IO_event (ExtCall «sys_poll») pollb_conf bs]’] >>
      simp[ev_eqp_def] >> imp_res_tac evrel_nopoll >>
      qpat_assum ‘EVERY (epoll _) es’ (assume_tac o MATCH_MP nopoll_epolls) >> simp[])
  >> Cases_on ‘es = []’
  >- (gvs[] >> first_x_assum (qspecl_then [‘xs’, ‘l’] mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [‘bx’, ‘by ++ [IO_event (ExtCall «sys_poll») pollb_conf bs]’] >>
      simp[ev_eqp_def])
  >> (* the stretch would begin inside an idle segment: its last empty poll is in it *)
  ‘LAST l = LAST es’
    by (‘LAST (xs ++ l) = LAST l ∧ LAST (pp ++ es) = LAST es’ by simp[LAST_APPEND_NOT_NIL] >>
        metis_tac[]) >>
  ‘MEM (LAST es) es ∧ MEM (LAST l) l’ by simp[MEM_LAST_NOT_NIL] >>
  ‘epoll fes (LAST es)’ by fs[EVERY_MEM] >>
  drule_all epoll_not_out >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  qpat_x_assum ‘EVERY (λe. poll_ev e ⇒ out_poll f e) l’
    (qspec_then ‘LAST l’ mp_tac o REWRITE_RULE[EVERY_MEM]) >> simp[]
QED

(* What ep_timed_out reads off a stretch is the same on both sides *)
Theorem ev_eqp_obs[local]:
  ev_eqp e e' ⇒
  (out_poll f e ⇔ out_poll f e') ∧ (poll_ev e ⇔ poll_ev e') ∧
  (send_took f e ⇔ send_took f e') ∧ (ep_ends f e ⇔ ep_ends f e')
Proof
  rw[ev_eqp_def] >> simp[out_poll_def, poll_ev_def, send_took_def, ep_ends_def,
                         l0_event_closed_def, l0_event_accepted_def]
QED

Theorem list_rel_obs[local]:
  ∀ys bs. LIST_REL ev_eqp ys bs ⇒
    n_out_polls f bs = n_out_polls f ys ∧
    (EVERY (λe. poll_ev e ⇒ out_poll f e) ys ⇒ EVERY (λe. poll_ev e ⇒ out_poll f e) bs) ∧
    (¬EXISTS (send_took f) ys ⇒ ¬EXISTS (send_took f) bs) ∧
    (¬EXISTS (ep_ends f) ys ⇒ ¬EXISTS (ep_ends f) bs)
Proof
  Induct >> simp[n_out_polls_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> fs[n_out_polls_def] >> strip_tac >>
  drule (Q.GEN ‘f’ ev_eqp_obs) >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  simp[] >> rw[] >> fs[]
QED

Theorem ppre_prefix[local]:
  ppre lfd hw ifds m ws0 (a ++ b) ⇒ ppre lfd hw ifds m ws0 a
Proof
  rw[ppre_def] >> goal_assum (drule_at Any) >> fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

(* MAIN: D23's observed excuse, PF ⇒ blocking *)
Theorem ep_timed_out_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  ep_timed_out KK j io_p ⇒ ep_timed_out KK j io_b
Proof
  rw[ep_timed_out_def] >>
  qabbrev_tac ‘f = EL j (l0_accepted evs)’ >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) (evs ++ span)’
    by metis_tac[ptrace_def] >>
  (* the stretch, carried by an evrel-related blocking prefix *)
  ‘∀pp bp. evrel pp bp ∧ pp = evs ++ span ∧ bpre lfd hw ifds bz m (w0, ps0) bp ⇒
           ∃evs' span'. LPREFIX (fromList (evs' ++ span')) io_b ∧ ep_open j evs' ∧
             KK ≤ n_out_polls (EL j (l0_accepted evs')) span' ∧
             EVERY (λe. poll_ev e ⇒ out_poll (EL j (l0_accepted evs')) e) span' ∧
             ¬EXISTS (send_took (EL j (l0_accepted evs'))) span' ∧
             ¬EXISTS (ep_ends (EL j (l0_accepted evs'))) span'’
    by (rpt strip_tac >>
        drule evrel_split >> disch_then (qspecl_then [‘f’, ‘evs’, ‘span’] mp_tac) >>
        simp[] >> strip_tac >>
        qexistsl_tac [‘bx’, ‘by’] >>
        ‘l0_accepted bx = l0_accepted evs’
          by (ONCE_REWRITE_TAC[GSYM nopoll_accepted] >> simp[]) >>
        ‘ep_open j bx’
          by (ONCE_REWRITE_TAC[GSYM ep_open_nopoll] >>
              qpat_assum ‘nopoll bx = _’ SUBST1_TAC >> REWRITE_TAC[ep_open_nopoll] >>
              first_assum ACCEPT_TAC) >>
        drule list_rel_obs >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
        qpat_x_assum ‘btrace _ _ _ _ _ _ _ _’ (assume_tac o REWRITE_RULE[btrace_def]) >>
        gvs[]) >>
  drule_all p2b >> strip_tac
  >- (fs[palign_def] >> first_x_assum irule >> qexists_tac ‘bp’ >> simp[])
  >> fs[pmid_def] >>
  (
  ‘EVERY (λ(f, e). e < 2) (pf_poll_set lfd hw ps (ifds h))’ by (irule idle_fes >> fs[bidle_def]) >>
  Cases_on ‘t = []’
  >- (gvs[] >> first_x_assum irule >> qexists_tac ‘bp’ >> simp[] >>
      irule bpre_round >> metis_tac[IS_PREFIX_REFL])
  >> Cases_on ‘span = []’
  >- (gvs[] >>
      drule_all p2b_nopoll >> strip_tac >>
      qexistsl_tac [‘bp'’, ‘[]’] >> fs[n_out_polls_def] >>
      qpat_x_assum ‘btrace _ _ _ _ _ _ _ _’ (assume_tac o REWRITE_RULE[btrace_def]) >>
      simp[] >> ONCE_REWRITE_TAC[GSYM ep_open_nopoll] >>
      ‘nopoll bp' = nopoll (pp0 ++ t)’ by (REWRITE_TAC[nopoll_append] >> first_assum ACCEPT_TAC) >>
      pop_assum SUBST1_TAC >> REWRITE_TAC[ep_open_nopoll] >> first_assum ACCEPT_TAC)
  >> ‘LAST span = LAST t’
       by (‘LAST (evs ++ span) = LAST span ∧ LAST (pp0 ++ t) = LAST t’
             by simp[LAST_APPEND_NOT_NIL] >> metis_tac[]) >>
  ‘MEM (LAST t) t ∧ MEM (LAST span) span’ by simp[MEM_LAST_NOT_NIL] >>
  ‘epoll (pf_poll_set lfd hw ps (ifds h)) (LAST t)’ by fs[EVERY_MEM] >>
  drule_all epoll_not_out >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  qpat_x_assum ‘EVERY (λe. poll_ev e ⇒ out_poll f e) span’
    (qspec_then ‘LAST span’ mp_tac o REWRITE_RULE[EVERY_MEM]) >> fs[])
QED

(* MAIN, (S3) without D23's premise: the echo's guarantee transfers from
   the PF trace (in the reindexed world) to the blocking trace *)
Theorem echo2_guar_transfer_full:
  bquiet m ifds bz ∧ l0_rely w0 ∧ l0wf w0 ∧ lone lfd w0 ∧
  btrace lfd hw ifds bz m w0 pinit io_b ∧ ptrace lfd hw ifds bz m w0 pinit io_p ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  linv lfd (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  flush_ok lfd hw ifds bz m w0 pinit ∧
  echo2_guar_l0 KK (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) io_p ⇒
  echo2_guar_l0 KK w0 io_b
Proof
  strip_tac >>
  ‘∀n. brounds lfd hw ifds bz m (w0, pinit) n ≠ NONE’ by (irule brounds_ok >> simp[]) >>
  irule echo2_guar_transfer_ok >> simp[] >>
  qexistsl_tac [‘bz’, ‘hw’, ‘ifds’, ‘io_p’, ‘lfd’, ‘m’] >> fs[] >> rpt strip_tac >>
  irule ep_timed_out_transfer >> simp[] >>
  qexistsl_tac [‘bz’, ‘hw’, ‘ifds’, ‘io_p’, ‘lfd’, ‘m’, ‘pinit’, ‘w0’] >> simp[]
QED
