(*
  Episode j's sent bytes in the kernel, whatever close calls happen
  (design/47, D after D32): a channel no fd and no listener queue holds
  ("unused") stays unused and its sent bytes never change; and a close
  call on f either keeps f on its channel (an interrupted close that keeps
  the fd: POSIX leaves its state unspecified) or leaves that channel
  unused.  So while episode j is open, the kernel's sent bytes on the
  channel its accept gave f are l0_sent j -- with no hypothesis on close
  calls (honestEchoL0KSent.episode_csent needs none on f).

  MAIN: faithful_unused, episode_csent2.
*)
Theory honestEchoL0CSentFree
Ancestors
  honestEchoL0KSent honestEchoL0ChanId honestEchoL0Sent honestEchoL0Excuse honestEchoL0LiveOwn honestEchoL0Trace
  honestEchoL0Spec honestL1BFaith
  honestL1BStmts honestL0Part honestL1PFOut honestL1PFRound honestL1Steps honestL1Inv
  honestL1Model honestL0WorldProps honestL0WorldInv honestL0Rely honestL0World honestL0
Libs
  preamble

(* Channel c exists and no fd or listener queue holds it *)
Definition unused_def:
  unused c w ⇔ c < LENGTH w.chans ∧ ¬MEM c (used_chans w)
End

Theorem unused_chan:
  unused c w ⇒ l0_chan_of w g ≠ SOME c
Proof
  rw[unused_def, l0_chan_of_def, AllCaseEqs(), used_chans_def] >>
  CCONTR_TAC >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem unused_upd[simp]:
  unused c (upd_lchan j g w) ⇔ unused c w
Proof
  simp[unused_def, upd_lchan_def, used_chans_def]
QED

Theorem csent_upd_other:
  j ≠ c ⇒ csent (upd_lchan j g w) c = csent w c
Proof
  rw[csent_def, upd_lchan_def, EL_LUPDATE]
QED

Theorem unused_deliver:
  unused c w ⇒ unused c (l0_deliver w a) ∧ csent (l0_deliver w a) c = csent w c
Proof
  strip_tac >> conj_tac
  >- (Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
      gvs[unused_def, used_chans_def] >>
      rename1 ‘FILTER _ w.listeners = (l, rr) :: rest’ >>
      ‘MEM l (MAP FST w.listeners)’
        by (qpat_x_assum ‘FILTER _ _ = _’ (mp_tac o Q.AP_TERM ‘MEM (l, rr)’) >>
            simp[MEM_FILTER, MEM_MAP] >> strip_tac >> qexists_tac ‘(l, rr)’ >> simp[]) >>
      drule AFUPDKEY_queue_PERM >> disch_then (qspec_then ‘LENGTH w.chans’ assume_tac) >>
      drule PERM_MEM_EQ >> simp[]) >>
  ‘c < LENGTH w.chans’ by fs[unused_def] >> metis_tac[csent_deliver]
QED

Theorem unused_tick:
  unused c w ⇒ unused c (l0_tick nm w) ∧ csent (l0_tick nm w) c = csent w c
Proof
  simp[l0_tick_def] >>
  ‘∀as w. unused c w ⇒
          unused c (FOLDL l0_deliver w as) ∧ csent (FOLDL l0_deliver w as) c = csent w c’
    by (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
        drule unused_deliver >> disch_then (qspec_then ‘h’ strip_assume_tac) >>
        first_x_assum drule >> simp[]) >>
  strip_tac >> first_x_assum (qspecl_then [‘w.env w.clock w.hist nm’,
                                            ‘w with clock := w.clock + 1’] mp_tac) >>
  impl_tac >- fs[unused_def, used_chans_def] >> simp[csent_def]
QED

Theorem unused_ticks:
  ∀k w. unused c w ⇒ unused c (l0_ticks nm k w) ∧ csent (l0_ticks nm k w) c = csent w c
Proof
  Induct >> simp[l0_ticks_def] >> rpt gen_tac >> strip_tac >>
  drule unused_tick >> disch_then (qspec_then ‘nm’ strip_assume_tac) >>
  first_x_assum drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The calls
   ------------------------------------------------------------------------ *)

Theorem unused_listen[local]:
  unused c w ∧ l0_listen p w = (x, w') ⇒ unused c w' ∧ csent w' c = csent w c
Proof
  strip_tac >> imp_res_tac csent_ops >> simp[] >>
  gvs[l0_listen_def, AllCaseEqs(), unused_def, used_chans_def]
QED

Theorem unused_simple_ops[local]:
  (unused c w ∧ l0_recv f n w = (r, d, w') ⇒ unused c w' ∧ csent w' c = csent w c) ∧
  (unused c w ∧ l0_shutdown f w = (r, w') ⇒ unused c w' ∧ csent w' c = csent w c) ∧
  (unused c w ∧ l0_connerr f w = (y, w') ⇒ unused c w' ∧ csent w' c = csent w c)
Proof
  rpt conj_tac >> strip_tac >> imp_res_tac csent_ops >> simp[] >>
  gvs[l0_recv_def, l0_shutdown_def, l0_connerr_def, AllCaseEqs()] >>
  rw[] >> gvs[unused_def, used_chans_def]
QED

Theorem unused_send[local]:
  unused c w ∧ l0_send f bs w = (r, w') ⇒ unused c w' ∧ csent w' c = csent w c
Proof
  strip_tac >> drule unused_chan >> disch_then (qspec_then ‘f’ assume_tac) >>
  gvs[l0_send_def, AllCaseEqs()] >> rw[] >> simp[csent_upd_other]
QED

Theorem unused_accept[local]:
  unused c w ∧ l0_accept l w = (r, w') ⇒ unused c w' ∧ csent w' c = csent w c
Proof
  simp[l0_accept_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule pop_used_PERM >> strip_tac >>
  ‘MEM j (used_chans w)’ by (imp_res_tac PERM_MEM_EQ >> fs[]) >>
  ‘j ≠ c’ by (strip_tac >> gvs[unused_def]) >>
  qpat_x_assum ‘PERM _ _’ (assume_tac o Q.SPEC ‘c’ o MATCH_MP PERM_MEM_EQ) >>
  simp[csent_upd_other] >> gvs[unused_def, used_chans_def, csent_def]
QED

Theorem unused_close[local]:
  unused c w ∧ l0_close f w = (r, w') ⇒ unused c w' ∧ csent w' c = csent w c
Proof
  strip_tac >> imp_res_tac csent_ops >> simp[] >>
  gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >> simp[] >>
  gvs[unused_def, used_chans_def, ADELKEY_def] >> rw[] >>
  metis_tac[MAP_SND_FILTER_sub, FLAT_FILTER_sub]
QED

Theorem unused_call:
  unused c w ∧ n ≠ «sys_connect» ∧
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  unused c w' ∧ csent w' c = csent w c
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[unused_listen, unused_simple_ops, unused_send, unused_accept, unused_close,
            unused_ticks]
QED

Theorem unused_hist[simp]:
  unused c (w with hist := h) ⇔ unused c w
Proof
  simp[unused_def, used_chans_def]
QED

Theorem unused_do_buf:
  unused c w ∧ n ≠ «sys_connect» ∧ l0_do_buf n conf bs w = SOME (out, w', ev) ⇒
  unused c w' ∧ csent w' c = csent w c
Proof
  strip_tac >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  drule unused_tick >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_all unused_call >> simp[csent_def]
QED

(* MAIN: along a faithful trace an unused channel stays unused, and its
   sent bytes stay put *)
Theorem faithful_unused:
  ∀evs w. faithful w evs ∧ winv w ∧ unused c w ⇒
          ∃u. FOLDL l0_step (SOME w) (MAP ev_lcall evs) = SOME u ∧ winv u ∧
              unused c u ∧ csent u c = csent w c
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  drule faithful_CONS_buf >> strip_tac >> gvs[] >>
  ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
  drule_all unused_do_buf >> strip_tac >>
  ‘winv u’ by metis_tac[winv_do_buf] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   While f holds c: a close call on f keeps it there or leaves c unused
   ------------------------------------------------------------------------ *)

Theorem distinct_snd2[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (a, j) l ∧ MEM (b, j) l ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP] >> metis_tac[SND]
QED

Theorem close_unused[local]:
  l0wf w ∧ l0_chan_of w f = SOME c ⇒
  unused c (close_fd f w) ∧ l0_chan_of (close_fd f w) f = NONE
Proof
  strip_tac >> simp[close_fd_def] >>
  ‘ALOOKUP w.open_fds f = SOME c ∧ c < LENGTH w.chans’
    by gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘MEM (f, c) w.open_fds’ by metis_tac[ALOOKUP_MEM] >>
  gvs[l0wf_def, used_chans_def, ALL_DISTINCT_APPEND] >>
  simp[unused_def, used_chans_def, l0_chan_of_def, ALOOKUP_ADELKEY] >>
  conj_tac
  >- (simp[MEM_MAP, ADELKEY_def, MEM_FILTER, EXISTS_PROD] >> rpt strip_tac >>
      metis_tac[distinct_snd2]) >>
  strip_tac >>
  ‘MEM c (MAP SND w.open_fds)’ by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem close_step[local]:
  l0wf w ∧ l0_chan_of w f = SOME c ∧ l0_close f w = (r, w') ⇒
  l0_chan_of w' f = SOME c ∨ (unused c w' ∧ l0_chan_of w' f = NONE)
Proof
  rw[l0_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[close_unused]
QED

(* One faithful event while f holds c: f keeps c and c's sent bytes grow
   by what the event sent on f, or (a close call on f) c is left unused
   and f has no channel *)
Theorem faithful_step_mapped:
  winv w ∧ l0_chan_of w f = SOME c ∧ faithful w (ev :: evs) ⇒
  ∃u. l0_step (SOME w) (ev_lcall ev) = SOME u ∧ faithful u evs ∧ winv u ∧
      ((l0_chan_of u f = SOME c ∧ csent u c = csent w c ++ l0_event_sent f ev) ∨
       (unused c u ∧ l0_chan_of u f = NONE ∧ csent u c = csent w c ∧
        l0_event_sent f ev = []))
Proof
  strip_tac >>
  Cases_on ‘closes_fd f ev’
  >- (drule faithful_CONS_buf >> strip_tac >> gvs[] >>
      ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
      ‘winv u’ by metis_tac[winv_do_buf] >> simp[] >>
      gvs[closes_fd_def] >>
      simp[l0_event_sent_def] >>
      drule l0_do_buf_cases >> strip_tac >> gvs[] >>
      qabbrev_tac ‘wt = l0_tick «sys_close» w’ >>
      ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
      ‘l0_chan_of wt (bytes_fd conf) = SOME c ∧ csent wt c = csent w c ∧ l0wf wt’
        by (qspecl_then [‘w’, ‘«sys_close»’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
            simp[Abbr ‘wt’] >> gvs[l0_chan_of_def, AllCaseEqs(), winv_def, l0wf_tick]) >>
      qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, AllCaseEqs()] >>
      strip_tac >> pairarg_tac >> gvs[] >>
      drule (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 csent_ops)))) >> strip_tac >>
      drule_all close_step >> strip_tac
      >- (disj1_tac >> gvs[l0_chan_of_def, csent_def]) >>
      disj2_tac >> gvs[l0_chan_of_def, csent_def]) >>
  drule_all faithful_step_csent >> strip_tac >> simp[ev_sent_l0]
QED

(* ------------------------------------------------------------------------
   The end of the episode while f holds c: a successful close leaves c
   unused; an accept cannot return f (it is in use)
   ------------------------------------------------------------------------ *)

Theorem close_ok_unused[local]:
  l0wf w ∧ l0_chan_of w f = SOME c ∧ l0_close f w = (Ok k, w') ⇒ unused c w'
Proof
  rw[l0_close_def, AllCaseEqs()] >> gvs[fail_def] >> metis_tac[close_unused]
QED

Theorem accept_fresh[local]:
  fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧ l0_accept l w = (Ok k, w') ⇒ ¬MEM (n2w k) (l0_used w)
Proof
  rw[l0_accept_def, AllCaseEqs(), fail_def, l0_alloc_def] >> gvs[] >>
  irule lowest_fd_free_lim >> fs[fds_lt_def]
QED

Theorem chan_used[local]:
  l0_chan_of w f = SOME c ⇒ MEM f (l0_used w)
Proof
  rw[l0_chan_of_def, AllCaseEqs(), l0_used_def] >> imp_res_tac ALOOKUP_MEM >>
  simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem faithful_step_end:
  winv w ∧ l0_chan_of w f = SOME c ∧ faithful w (e :: evs) ∧ ep_ends f e ⇒
  ∃u. l0_step (SOME w) (ev_lcall e) = SOME u ∧ faithful u evs ∧ winv u ∧
      unused c u ∧ csent u c = csent w c
Proof
  strip_tac >> drule faithful_CONS_buf >> strip_tac >> gvs[] >>
  ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
  ‘winv u’ by metis_tac[winv_do_buf] >> simp[] >>
  drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick n w’ >>
  ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘l0_chan_of wt f = SOME c ∧ csent wt c = csent w c’
    by (qspecl_then [‘w’, ‘n’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
        simp[Abbr ‘wt’] >> gvs[l0_chan_of_def, AllCaseEqs()]) >>
  ‘l0wf wt ∧ fds_lt wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, l0wf_tick] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  simp[csent_def] >>
  qpat_x_assum ‘ep_ends _ _’ mp_tac >>
  simp[ep_ends_def, l0_event_closed_def, l0_event_accepted_def, l0_ev_res_def, MAP_ZIP] >>
  strip_tac >> gvs[AllCaseEqs()]
  >- ((* a successful close of f *)
      qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, AllCaseEqs()] >>
      strip_tac >> pairarg_tac >> gvs[] >>
      ‘l0_res_ok r’
        by (qpat_x_assum ‘l0_close _ _ = _’ mp_tac >> simp[l0_close_def] >>
            rw[AllCaseEqs()] >> TRY (irule fail_ok >> simp[] >> NO_TAC) >>
            simp[l0_res_ok_def]) >>
      rename1 ‘dec_res _ = SOME (Ok kk)’ >>
      ‘r = Ok kk’
        by (qpat_x_assum ‘enc_res _ = _’ (SUBST_ALL_TAC o SYM) >>
            drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >> gvs[]) >>
      gvs[] >> drule_all close_ok_unused >> strip_tac >>
      drule (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 csent_ops)))) >> strip_tac >>
      fs[unused_def, used_chans_def, csent_def]) >>
  (* an accept returning f: impossible, f is in use *)
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, AllCaseEqs()] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  drule_all l0_accept_res >> strip_tac >>
  rename1 ‘dec_res _ = SOME (Ok kk)’ >>
  ‘r = Ok kk’
    by (qpat_x_assum ‘enc_res _ = _’ (SUBST_ALL_TAC o SYM) >>
        drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >> gvs[]) >>
  gvs[] >>
  ‘wt.fd_limit ≤ 2 ** 31’ by fs[l0_rely_def] >>
  drule_all accept_fresh >> strip_tac >>
  drule chan_used >> simp[]
QED

(* ------------------------------------------------------------------------
   Along the episode, and after it
   ------------------------------------------------------------------------ *)

(* Through events with no end of f's episode: c's sent bytes are at most
   what those events sent on f, with f on c or c unused *)
Theorem post_csent:
  ∀post u X. faithful u post ∧ winv u ∧
    ((l0_chan_of u f = SOME c ∧ csent u c = X) ∨
     (unused c u ∧ l0_chan_of u f = NONE ∧ csent u c ≼ X)) ∧
    EVERY (λe. ¬ep_ends f e) post ⇒
    ∃v. FOLDL l0_step (SOME u) (MAP ev_lcall post) = SOME v ∧ winv v ∧
        csent v c ≼ X ++ FLAT (MAP (l0_event_sent f) post) ∧
        (l0_chan_of v f = SOME c ∨ (unused c v ∧ l0_chan_of v f = NONE))
Proof
  Induct >- (rpt strip_tac >> fs[]) >> rpt gen_tac >> strip_tac
  >- (drule_all faithful_step_mapped >> rpt strip_tac >> simp[] >>
      first_x_assum (qspecl_then [‘u'’, ‘X ++ l0_event_sent f h’] mp_tac) >>
      impl_tac >> TRY (gvs[] >> NO_TAC) >> fs[])
  >- (drule faithful_step_chan_back >> simp[] >> strip_tac >>
      drule faithful_CONS_buf >> strip_tac >> gvs[] >>
      ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
      drule_all unused_do_buf >> strip_tac >> gvs[] >>
      first_x_assum irule >> simp[] >>
      conj_tac >- metis_tac[] >> disj2_tac >>
      conj_tac
      >- (Cases_on ‘l0_chan_of u' f’ >> simp[] >>
          qpat_x_assum ‘∀f'. ¬ep_ends f' _ ⇒ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
      fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC])
QED

Theorem ep_sn_gone:
  ∀rest s. j < FST s ∧ (∀g. ALOOKUP (SND s) g ≠ SOME j) ⇒ ep_fold pf fdf j s rest = []
Proof
  Induct >> simp[ep_fold_def] >> rpt gen_tac >> PairCases_on ‘s’ >> strip_tac >>
  conj_tac >- (every_case_tac >> fs[]) >>
  first_x_assum irule >> simp[l0_ep_step_def] >> every_case_tac >> simp[] >>
  rw[ALOOKUP_ADELKEY] >> fs[]
QED

Theorem first_occ:
  ∀l. EXISTS P l ⇒ ∃p1 e p2. l = p1 ++ [e] ++ p2 ∧ P e ∧ ¬EXISTS P p1
Proof
  Induct >> simp[] >> rpt strip_tac
  >- (qexistsl_tac [‘[]’, ‘h’, ‘l’] >> simp[]) >>
  Cases_on ‘P h’
  >- (qexistsl_tac [‘[]’, ‘h’, ‘l’] >> simp[]) >>
  fs[] >> qexistsl_tac [‘h :: p1’, ‘e’, ‘p2’] >> simp[]
QED

Theorem alookup_snd_inj2[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l a = SOME v ∧ ALOOKUP l b = SOME v ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[AllCaseEqs()] >>
  imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem ep_ok_inj[local]:
  ep_ok (k, opn) ∧ ALOOKUP opn a = SOME v ∧ ALOOKUP opn b = SOME v ⇒ a = b
Proof
  rw[ep_ok_def] >> metis_tac[alookup_snd_inj2]
QED

(* After the episode's end, l0_sent j stays as it was before the end *)
Theorem l0_sent_after_end:
  LENGTH (l0_accepted pre) = j ∧ l0_event_accepted ev = SOME f ∧
  EVERY (λe. ¬ep_ends f e) p1 ∧ ep_ends f e ⇒
  l0_sent j (pre ++ [ev] ++ p1 ++ [e] ++ p2) = FLAT (MAP (l0_event_sent f) p1)
Proof
  strip_tac >>
  ‘l0_sent j (pre ++ [ev] ++ p1) = FLAT (MAP (l0_event_sent f) p1)’
    by (irule l0_sent_open >> simp[] >> metis_tac[]) >>
  fs[l0_sent_fold, ep_fold_APPEND] >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (pre ++ [ev] ++ p1))) f = SOME j’
    by (irule ep_open_state >> rpt conj_tac >>
        FIRST [qspecl_then [‘pre’, ‘j’, ‘ev’, ‘f’, ‘p1’] mp_tac
                 (Q.GENL [‘pre’, ‘j’, ‘ev’, ‘g’, ‘post’] ep_open_EL) >> fs[] >> NO_TAC,
               simp[ep_open_def] >> metis_tac[] >> NO_TAC]) >>
  ‘ep_ok (l0_ep_st (0, []) (pre ++ [ev] ++ p1))’
    by (irule ep_ok_st >> simp[ep_ok_def]) >>
  ‘send_fd e = NONE’
    by (Cases_on ‘e’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
        fs[ep_ends_def, l0_event_closed_def, l0_event_accepted_def, send_fd_def] >>
        rw[] >> fs[]) >>
  Cases_on ‘l0_ep_st (0, []) (pre ++ [ev] ++ p1)’ >> rename1 ‘_ = (k, opn)’ >>
  ‘j < k’ by (fs[ep_ok_def, EVERY_MEM, MEM_MAP] >> imp_res_tac ALOOKUP_MEM >>
              first_x_assum irule >> qexists_tac ‘(f, j)’ >> simp[]) >>
  fs[ep_fold_def] >>
  irule ep_sn_gone >>
  fs[ep_ends_def, l0_ep_step_def] >> every_case_tac >> gvs[] >>
  rw[ALOOKUP_ADELKEY] >>
  TRY (metis_tac[ep_ok_inj] >> NO_TAC) >>
  imp_res_tac accepted_not_closed >> fs[]
QED

(* MAIN: at any point after episode j's accept (open or ended, whatever
   close calls happened), the kernel's sent bytes on the channel the
   accept gave f are a prefix of l0_sent j *)
Theorem episode_csent_le:
  faithful w0 (pre ++ [ev] ++ post) ∧ winv w0 ∧ qfresh w0 ∧
  LENGTH (l0_accepted pre) = j ∧ l0_event_accepted ev = SOME f ⇒
  ∃w1 c w. world_at w0 (pre ++ [ev]) = SOME w1 ∧ l0_chan_of w1 f = SOME c ∧
           world_at w0 (pre ++ [ev] ++ post) = SOME w ∧
           csent w c ≼ l0_sent j (pre ++ [ev] ++ post)
Proof
  strip_tac >>
  ‘faithful w0 (pre ++ (ev :: post))’ by full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND] >>
  drule_all faithful_APPEND_inv >> strip_tac >>
  drule_all faithful_accept_csent >> strip_tac >>
  rename1 ‘l0_chan_of u1 f = SOME c’ >>
  qexistsl_tac [‘u1’, ‘c’] >>
  simp[world_at_def, l0_replay_def, FOLDL_APPEND] >>
  Cases_on ‘EXISTS (ep_ends f) post’
  >- (drule first_occ >> strip_tac >>
      qpat_x_assum ‘post = _’ SUBST_ALL_TAC >>
      rename1 ‘ep_ends f e’ >>
      ‘faithful u1 (p1 ++ (e :: p2))’ by full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND] >>
      drule_all faithful_APPEND_inv >> strip_tac >>
      rename1 ‘FOLDL _ (SOME u1) (MAP ev_lcall p1) = SOME v’ >>
      ‘EVERY (λe. ¬ep_ends f e) p1’ by fs[EVERY_MEM, EXISTS_MEM] >>
      ‘faithful u1 p1’
        by (irule faithful_prefix >> qexists_tac ‘e :: p2’ >> first_assum ACCEPT_TAC) >>
      qspecl_then [‘p1’, ‘u1’, ‘[]’] mp_tac post_csent >>
      impl_tac >- simp[] >>
      strip_tac >>
      ‘v' = v’ by fs[] >> pop_assum SUBST_ALL_TAC >>
      ‘∃v2. l0_step (SOME v) (ev_lcall e) = SOME v2 ∧ faithful v2 p2 ∧ winv v2 ∧
            unused c v2 ∧ csent v2 c = csent v c’
        by (TRY (qpat_assum ‘winv v’ (fn h1 =>
                   qpat_assum ‘l0_chan_of v f = SOME c’ (fn h2 =>
                   qpat_assum ‘faithful v (e :: p2)’ (fn h3 =>
                   qpat_assum ‘ep_ends f e’ (fn h4 =>
                   mp_tac (MATCH_MP faithful_step_end (LIST_CONJ [h1, h2, h3, h4])))))) >>
                 strip_tac >> rename1 ‘l0_step (SOME v) (ev_lcall e) = SOME vv’ >>
                 qexists_tac ‘vv’ >> simp[] >> NO_TAC) >>
            qpat_x_assum ‘faithful v (e :: p2)’
              (strip_assume_tac o MATCH_MP faithful_CONS_buf) >>
            rename1 ‘l0_do_buf _ _ _ v = SOME (_, v2, _)’ >>
            ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
            ‘unused c v2 ∧ csent v2 c = csent v c’
              by (drule_at (Pos last) unused_do_buf >> simp[]) >>
            ‘winv v2’ by (drule_at (Pos last) winv_do_buf >> simp[]) >>
            qexists_tac ‘v2’ >> simp[]) >>
      qspecl_then [‘p2’, ‘v2’] mp_tac faithful_unused >> simp[] >> strip_tac >>
      ‘l0_sent j (pre ++ [ev] ++ p1 ++ [e] ++ p2) = FLAT (MAP (l0_event_sent f) p1)’
        by (irule l0_sent_after_end >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[FOLDL_APPEND] >> fs[]) >>
  ‘EVERY (λe. ¬ep_ends f e) post’ by fs[EVERY_MEM, EXISTS_MEM] >>
  qspecl_then [‘post’, ‘u1’, ‘[]’] mp_tac post_csent >>
  impl_tac >- simp[] >>
  strip_tac >> simp[] >>
  ‘l0_sent j (pre ++ [ev] ++ post) = FLAT (MAP (l0_event_sent f) post)’
    by (qspecl_then [‘pre ++ [ev] ++ post’, ‘pre’, ‘ev’, ‘post’, ‘j’, ‘f’] mp_tac
          (Q.GENL [‘evs’, ‘pre’, ‘ev’, ‘post’, ‘j’, ‘f’] l0_sent_open) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
        simp[]) >>
  fs[]
QED
