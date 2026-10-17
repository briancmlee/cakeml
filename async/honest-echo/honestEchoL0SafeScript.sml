(*
  Route (d), S4 (design/46): echo_l0_safe.  Every finite prefix of the
  program's trace lies between the end of some round and the end of the
  next (the loop's rounds may be empty once it stops for lack of handle
  room); at a round boundary and inside a round, what each episode sent is
  a prefix of what it received (honestEchoL0Run's round_safe).
*)
Theory honestEchoL0Safe
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out honestEchoL0Run
  asyncCore asyncLevel1 asyncTranscript honestL1PFProg honestL1PFSpec
  asyncServer asyncServerSafety asyncM4GTrans
  honestEchoL0Prog honestEchoL0Main honestEchoL0Sem honestL1PFInv honestL1Inv
Libs
  preamble

Theorem FLAT_GENLIST_mono[local]:
  ∀d n. FLAT (GENLIST f n) ≼ FLAT (GENLIST f (n + d))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[GSYM ADD_SUC, GENLIST, SNOC_APPEND] >>
  rw[rich_listTheory.IS_PREFIX_APPEND] >> simp[]
QED

(* Every finite prefix of a trace made of rounds lies between the end of
   some round and the end of the next (rounds may be empty) *)
Theorem LPREFIX_rounds_any:
  LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇒
  ∃n. FLAT (GENLIST f n) ≼ evs ∧ evs ≼ FLAT (GENLIST f (SUC n))
Proof
  strip_tac >>
  Cases_on ‘∃m. ¬(FLAT (GENLIST f m) ≼ evs)’
  >- (qpat_x_assum ‘∃m. _’ (strip_assume_tac o HO_MATCH_MP arithmeticTheory.WOP) >>
      rename1 ‘¬(FLAT (GENLIST f m) ≼ evs)’ >>
      Cases_on ‘m’ >> gvs[] >> rename1 ‘GENLIST f (SUC n)’ >>
      qexists_tac ‘n’ >> simp[] >>
      Cases_on ‘LENGTH evs ≤ LENGTH (FLAT (GENLIST f (SUC n)))’
      >- (irule LPREFIX_comparable >> metis_tac[rounds_LPREFIX]) >>
      ‘FLAT (GENLIST f (SUC n)) ≼ evs’
        by (irule LPREFIX_comparable >> simp[] >> metis_tac[rounds_LPREFIX]) >>
      gvs[]) >>
  gvs[] >>
  (* every round boundary is inside evs: the rounds are eventually empty *)
  ‘∃N. ∀p. N ≤ p ⇒ f p = []’
    by (CCONTR_TAC >> gvs[] >>
        ‘∀m. ∃n. m ≤ LENGTH (FLAT (GENLIST f n))’
          by (Induct >> simp[] >> gvs[] >>
              first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
              qexists_tac ‘SUC p’ >> simp[GENLIST, SNOC_APPEND] >>
              ‘FLAT (GENLIST f n) ≼ FLAT (GENLIST f (n + (p − n)))’
                by simp[FLAT_GENLIST_mono] >>
              gvs[] >> imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >>
              Cases_on ‘f p’ >> gvs[]) >>
        first_x_assum (qspec_then ‘SUC (LENGTH evs)’ strip_assume_tac) >>
        qpat_x_assum ‘∀m. FLAT _ ≼ evs’ (qspec_then ‘n’ assume_tac) >>
        imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >> fs[]) >>
  qexists_tac ‘N’ >> simp[GENLIST, SNOC_APPEND] >>
  ‘LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) = fromList (FLAT (GENLIST f N))’
    by (ONCE_REWRITE_TAC [Q.SPEC ‘N’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
        ‘LFLATTEN (LGENLIST (λi. fromList (f (N + i))) NONE) = LNIL’
          by simp[LFLATTEN_EQ_NIL, every_LGENLIST] >>
        simp[LAPPEND_NIL_2ND]) >>
  gvs[LPREFIX_fromList, from_toList]
QED

(* S4 at a round boundary *)
Theorem boundary_safe:
  ri lfd (srelabel (server k)) (h, (w, ps), evs) ∧ hdln (w2n lfd) j < dimword (:64) ⇒
  ep_sn j (0, []) evs ≼ ep_rd j (0, []) evs
Proof
  strip_tac >> qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  ‘ep_sn j (0, []) evs ≼ hwritten (l1hdl lfd j) (texec (srelabel (server k)) h)’
    by (gvs[oi_def] >> imp_res_tac isPREFIX_APPEND_L) >>
  drule trans_texec >> strip_tac >>
  ‘ALL_DISTINCT (haccepted (trans (srelabel (server k)) h))’
    by (‘ALL_DISTINCT (GENLIST (λi. l1hdl lfd i) ps.b.nxt)’
          by (irule ALL_DISTINCT_hdl >> irule hdln_mono >>
              qexists_tac ‘ps.b.nxt + LENGTH ps.acq’ >> fs[]) >>
        qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_assum ‘haccepted (texec _ _) = _’
          (fn th => REWRITE_TAC [haccepted_APPEND, haccepted_NONE, th, APPEND_NIL]) >>
        first_assum ACCEPT_TAC) >>
  ‘hwritten (l1hdl lfd j) (trans (srelabel (server k)) h) =
   hread (l1hdl lfd j) (trans (srelabel (server k)) h)’
    by (irule server_handle_echo >> first_assum ACCEPT_TAC) >>
  ‘hwritten (l1hdl lfd j) (texec (srelabel (server k)) h) ≼
   hread (l1hdl lfd j) (texec (srelabel (server k)) h)’
    by (qpat_x_assum ‘hwritten _ (trans _ _) = _’ mp_tac >>
        qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
        simp[hwritten_APPEND, hread_APPEND] >> strip_tac >>
        pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  irule isPREFIX_TRANS >>
  qexists_tac ‘hwritten (l1hdl lfd j) (texec (srelabel (server k)) h)’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule isPREFIX_TRANS >>
  qexists_tac ‘hread (l1hdl lfd j) (texec (srelabel (server k)) h)’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[]
QED

(* An episode beyond the handle range is never opened *)
Theorem fresh_safe:
  ri lfd m (h, (w, ps), evs) ∧ pre ≼ evs ∧ ¬(hdln (w2n lfd) j < dimword (:64)) ⇒
  ep_sn j (0, []) pre = []
Proof
  strip_tac >> qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  ‘FST (l0_ep_st (0, []) evs) = ps.b.nxt + LENGTH ps.acq’
    by (Cases_on ‘l0_ep_st (0, []) evs’ >> gvs[own_ok_def]) >>
  ‘ps.b.nxt + LENGTH ps.acq < j’
    by (CCONTR_TAC >> ‘j ≤ ps.b.nxt + LENGTH ps.acq’ by simp[] >>
        ‘hdln (w2n lfd) j < dimword (:64)’
          by (irule hdln_mono >> qexists_tac ‘ps.b.nxt + LENGTH ps.acq’ >> fs[]) >>
        fs[]) >>
  irule ep_fold_fresh >> simp[ep_ok_def, FST_l0_ep_st] >>
  ‘LENGTH (l0_accepted pre) ≤ LENGTH (l0_accepted evs)’
    by (gvs[rich_listTheory.IS_PREFIX_APPEND, l0_accepted_def]) >>
  gvs[FST_l0_ep_st]
QED

Theorem prun_FLAT:
  (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ⇒
  ∀n. FLAT (GENLIST (pround_evs lfd hw ifds m ws0) n) = FST (SND (SND (prun lfd hw ifds m ws0 n)))
Proof
  strip_tac >> Induct >> simp[GENLIST, SNOC_APPEND] >>
  drule prun_SUC >> disch_then (qspec_then ‘n’ mp_tac) >> rw[] >> simp[]
QED

Theorem prun_ri:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  (∀n. prounds_t lfd hw ifds (srelabel (server k)) ws0 n ≠ NONE) ⇒
  ∀n. ri lfd (srelabel (server k))
         (FST (prun lfd hw ifds (srelabel (server k)) ws0 n),
          FST (SND (prun lfd hw ifds (srelabel (server k)) ws0 n)),
          FST (SND (SND (prun lfd hw ifds (srelabel (server k)) ws0 n))))
Proof
  rpt strip_tac >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘prounds_t lfd hw ifds (srelabel (server k)) ws0 n’ >> simp[prun_def] >>
  PairCases_on ‘x’ >> simp[] >> drule ri_echo >> disch_then drule >> simp[]
QED

(* MAIN, S4 for the loop: on every finite prefix of the loop's trace,
   what each episode sent is a prefix of what it received *)
Theorem echo_run_safe:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  (∀n. prounds_t lfd hw ifds (srelabel (server k)) ws0 n ≠ NONE) ∧
  LPREFIX (fromList evs)
    (LFLATTEN (LGENLIST (λi. fromList (pround_evs lfd hw ifds (srelabel (server k)) ws0 i)) NONE)) ⇒
  ∀j. ep_sn j (0, []) evs ≼ ep_rd j (0, []) evs
Proof
  strip_tac >> gen_tac >>
  drule LPREFIX_rounds_any >> strip_tac >>
  drule_all prun_FLAT >> strip_tac >> gvs[] >>
  drule_all prun_ri >> strip_tac >>
  qabbrev_tac ‘R = prun lfd hw ifds (srelabel (server k)) ws0’ >>
  ‘ri lfd (srelabel (server k)) (FST (R n), FST (SND (R n)), FST (SND (SND (R n)))) ∧
   ri lfd (srelabel (server k))
      (FST (R (SUC n)), FST (SND (R (SUC n))), FST (SND (SND (R (SUC n)))))’
    by simp[Abbr ‘R’] >>
  Cases_on ‘hdln (w2n lfd) j < dimword (:64)’
  >- (drule prun_SUC >> disch_then (qspec_then ‘n’ mp_tac) >> simp[] >>
      IF_CASES_TAC >> simp[] >> strip_tac
      >- (Cases_on ‘R n’ >> PairCases_on ‘r’ >> gvs[] >>
          PairCases_on ‘ws'’ >>
          qpat_x_assum ‘∀n. ri _ _ _’ (qspec_then ‘SUC n’ mp_tac) >> simp[] >> strip_tac >>
          irule round_safe >> simp[] >> metis_tac[]) >>
      ‘evs = FST (SND (SND (R n)))’ by (irule isPREFIX_ANTISYM >> gvs[]) >>
      Cases_on ‘R n’ >> PairCases_on ‘r’ >> gvs[] >>
      irule boundary_safe >> qexistsl [‘q’, ‘k’, ‘lfd’, ‘r1’, ‘r0’] >> fs[]) >>
  Cases_on ‘R (SUC n)’ >> PairCases_on ‘r’ >> gvs[] >>
  ‘ep_sn j (0, []) evs = []’ by (qpat_x_assum ‘ri _ _ (q, _, _)’
          (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] fresh_safe) th)) >>
        fs[]) >>
  simp[]
QED

(* The listener the program listens on is in use *)
Theorem listen_used:
  l0_rely w ∧ sys_listen_echo w = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  MEM (n2w k : word64) (l0_used w1)
Proof
  rw[sys_listen_echo_def, l0_do_def, l0_ffi_fn_def] >>
  gvs[AllCaseEqs(), l0_call_def, echo_port_conf_def]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[listen_fd_def, l0_res_of_def] >>
      gvs[l0_listen_def, AllCaseEqs(), l0_used_def]) >>
  PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  gvs[enc_listen_fail_def, listen_fd_def, l0_res_of_def, dec_res_def, AllCaseEqs()]
QED

(* The run invariant holds at the start of the loop *)
Theorem ri_echo_base:
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  ri (n2w k) (srelabel (server k)) ([], (w1, pinit), [])
Proof
  strip_tac >>
  ‘l0_rely w1 ∧ fds_lt w1’
    by (gvs[sys_listen_echo_def] >>
        metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_listen» = «sys_connect»”]) >>
  drule_all listen_used >> strip_tac >>
  simp[ri_def, wown_def, owned_def, own_ok_def, ep_ok_def, pinit_def, l1init_def,
       okb_def, outbox_of_def, texec_def, haccepted_def, ep_fold_def, oi_def, obp_def,
       epfd_def, live_def, inbp_def, hread_def, hwritten_def, inb_of_def, hdln_def] >>
  rw[]
QED

(* The listen event belongs to no episode *)
Theorem listen_event[local]:
  sys_listen_echo w = SOME (out, w1, ev) ⇒
  send_fd ev = NONE ∧ recv_fd ev = NONE ∧ l0_event_accepted ev = NONE ∧
  l0_event_closed ev = NONE
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >>
  simp[send_fd_def, recv_fd_def, l0_event_accepted_def, l0_event_closed_def]
QED

(* MAIN: the program's trace when the listen succeeds is safe *)
Theorem echo_l0_run_safe:
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  echo_safe_l0 (LCONS ev (echo_l0_run k w1))
Proof
  strip_tac >> drule_all ri_echo_base >> strip_tac >>
  ‘k < 2147483648’ by metis_tac[listen_fd_small] >>
  ‘∀n. prounds_t (n2w k) echo_hw (interest [n2w k]) (srelabel (server k)) (w1, pinit) n ≠ NONE’
    by (‘l0_rely w1’ by (gvs[sys_listen_echo_def] >> metis_tac[l0_do_rely]) >>
        ‘psmall (n2w k) pinit’
          by simp[psmall_def, pinit_def, l1init_def, small_fds_def, small_def] >>
        gen_tac >>
        qspecl_then [‘w1’, ‘pinit’, ‘n2w k’, ‘echo_hw’, ‘interest [n2w k]’, ‘srelabel (server k)’]
          mp_tac (Q.GENL [‘w0’, ‘ps0’, ‘lfd’, ‘hw’, ‘ifds’, ‘m’] prounds_t_total) >>
        simp[server_pt_ok] >> disch_then (qspec_then ‘n’ strip_assume_tac) >> simp[]) >>
  rw[echo_safe_l0_def, l0_sent_fold, l0_read_fold] >>
  gvs[LPREFIX_LCONS] >> TRY (simp[ep_fold_def] >> NO_TAC) >>
  Cases_on ‘evs’ >> gvs[] >>
  drule listen_event >> strip_tac >>
  ‘l0_ep_step (0, []) ev = (0, [])’ by simp[l0_ep_step_def] >>
  simp[ep_fold_def] >>
  irule echo_run_safe >> simp[] >> metis_tac[]
QED

(* MAIN: echo_l0_safe, the statement the user approved *)
Theorem echo_l0_safe:
  l0_server_world w0 ⇒
  ∃io. (semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog (Diverge io) ∧
        echo_safe_l0 io) ∨
       (∃out w1 ev. sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = NONE ∧
                    io = [|ev|] ∧
                    semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog
                      (Terminate Success [ev]))
Proof
  rw[l0_server_world_def] >>
  drule_all echo_l0_semantics_prog >> strip_tac
  >- (qexists_tac ‘[|ev|]’ >> disj2_tac >> simp[]) >>
  qexists_tac ‘LCONS ev (echo_l0_run k w1)’ >> disj1_tac >> simp[] >>
  irule echo_l0_run_safe >> simp[] >> metis_tac[]
QED

