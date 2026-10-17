(*
  The echo reads an fd at end-of-file (design/47 D, close step; L3-09 SQ
  part 1): on the PF echo run, if L1 holds f under handle h with f's EOF
  seen, the server reads h within three rounds (cf-actions' M4
  read_soon_eof_s, lifted through echo_sim).

  Its extra hypothesis -- the server has not yet read h's end-of-file --
  holds because a handle whose end-of-file was read is out of the handle
  table for good (eof_gone, an invariant of the version-2 simulation's
  handle layer; the converse of close-v2-sim's closed_eof).

  MAIN: echo_read_soon_eof.
*)
Theory honestEchoL0EofRead
Ancestors
  honestEchoL0SrvOut honestEchoL0Stop asyncM4ReadSoonEof asyncM4ReadSoon asyncM4LiveWorld
  asyncHLEchoSpec2 asyncHLSimTrace asyncHLSimEvents asyncHLSimOps asyncHLSimRun
  asyncHLSimTick asyncHLSimWorld asyncHLEof asyncHLModel
  asyncM4Account asyncM4SockInv asyncM4GTrans asyncM4GRounds asyncM4EchoRunOk asyncM3World
  honestEchoL0Obl honestL1PFRefine
Libs
  preamble


(* Round n's actions, performed by the handle layer from round n's state,
   give round n's responses and round n + 1's handle state *)
Theorem round_hacts:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. (∃evs2 s2'.
         hacts (n2w lfdn) (hst (n2w lfdn) EI ES s2 n) (gacts EI ES (v1of (n2w lfdn) s2) n) =
         SOME (gres EI ES (v1of (n2w lfdn) s2) n, evs2,
               (s2', SND (hst (n2w lfdn) EI ES s2 (SUC n))))) ∧
      EVERY (action_ok (n2w lfdn) (wacc (gperf EI ES (v1of (n2w lfdn) s2) n)))
            (gacts EI ES (v1of (n2w lfdn) s2) n)
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘grun_ok EI ES s1’ by (irule echo_grun_ok >> simp[]) >>
  ‘sched_wf s1’ by (simp[Abbr ‘s1’] >> irule v1of_sched_wf >> simp[]) >>
  drule_all hrun_sim >> strip_tac >>
  drule_all hrun_events >> strip_tac >>
  gen_tac >>
  qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. ep_st _ _ _ = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘Abbrev (s1 = _)’
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [FST, SND]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto EI ES s1 n’ by simp[grun_ok_gok_upto] >>
  drule echo_round_actions_ok >> strip_tac >>
  ‘no_after_eof (gperf EI ES s1 n) (ZIP (gacts EI ES s1 n, gres EI ES s1 n))’
    by (irule round_no_after_eof >> fs[]) >>
  qspecl_then [‘gacts EI ES s1 n’, ‘gstate EI ES s1 n’, ‘s2k’, ‘hsk’,
               ‘gres EI ES s1 n’, ‘evs’, ‘s'’, ‘gperf EI ES s1 n’] mp_tac
    (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf EI ES s1 n)’] hacts_written) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  ‘hacts_of (n2w lfdn) EI ES s2 n = gacts EI ES s1 n’
    by simp[hacts_of_def, gacts_def] >>
  ‘hacts_tot (n2w lfdn) (hst (n2w lfdn) EI ES s2 n) (hacts_of (n2w lfdn) EI ES s2 n) =
   (gres EI ES s1 n, evs2, (s2', hs'))’
    by simp[hacts_tot_def] >>
  drule hround_step >> strip_tac >>
  simp[] >> qexistsl_tac [‘evs2’, ‘s2'’] >> simp[]
QED

(* ------------------------------------------------------------------------
   eof_gone: a handle whose end-of-file was read is issued and out of the
   table
   ------------------------------------------------------------------------ *)

Definition eof_gone_def:
  eof_gone lfd P (hs : hstate) ⇔
    ∀h k. MEM (Read h k, Got (SOME [])) P ⇒
          ∃j. h = hdl lfd j ∧ j < hs.nxt ∧ ALOOKUP hs.tbl h = NONE
End

Theorem hdo_nxt_mono[local]:
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ⇒ hs.nxt ≤ hs'.nxt
Proof
  Cases_on ‘a’ >> rw[hdo_def, AllCaseEqs()] >> simp[]
QED

Theorem hdo_eof_none[local]:
  hdo lfd (s, hs) (Read h k) = SOME (Got (SOME []), (s', hs'), evs) ⇒
  ALOOKUP hs'.tbl h = NONE
Proof
  rw[hdo_def, AllCaseEqs()] >> simp[ALOOKUP_ADELKEY]
QED

Theorem hdo_out_keep[local]:
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ∧ j < hs.nxt ∧
  ALOOKUP hs.tbl (hdl lfd j) = NONE ⇒
  ALOOKUP hs'.tbl (hdl lfd j) = NONE
Proof
  strip_tac >>
  ‘∀i. hdln (w2n lfd) i < dimword (:64) ∧ j < i ⇒ hdl lfd i ≠ hdl lfd j’
    by (rpt strip_tac >>
        ‘hdln (w2n lfd) j < dimword (:64)’
          by (qpat_x_assum ‘hdln _ i < _’ mp_tac >> rw[hdln_def]) >>
        ‘i = j’ by (irule hdl_inj_lt >> qexists_tac ‘lfd’ >> simp[]) >>
        fs[]) >>
  Cases_on ‘a’ >> gvs[hdo_def, AllCaseEqs(), ALOOKUP_ADELKEY] >> rw[] >>
  metis_tac[]
QED

Theorem hacts_eof_gone:
  ∀acts s hs rs evs s' hs' P.
    hacts lfd (s, hs) acts = SOME (rs, evs, (s', hs')) ∧ eof_gone lfd P hs ∧
    (∀h k. MEM (Read h k) acts ⇒ ∃j. h = hdl lfd j ∧ j < hs.nxt) ⇒
    eof_gone lfd (P ++ ZIP (acts, rs)) hs'
Proof
  Induct >- simp[hacts_def] >>
  rpt gen_tac >> simp[Once hacts_def, AllCaseEqs()] >> strip_tac >>
  PairCases_on ‘st1’ >> gvs[] >>
  rename1 ‘hdo lfd (s, hs) a = SOME (r, (s1, hs1), evs1)’ >>
  ‘hs.nxt ≤ hs1.nxt’ by metis_tac[hdo_nxt_mono] >>
  ‘eof_gone lfd (P ++ [(a, r)]) hs1’
    by (fs[eof_gone_def] >> rpt gen_tac >> strip_tac
        >- (first_x_assum drule >> strip_tac >> qexists_tac ‘j’ >> simp[] >>
            irule hdo_out_keep >> metis_tac[]) >>
        rveq >> first_x_assum (qspecl_then [‘h’, ‘k’] mp_tac) >> simp[] >>
        strip_tac >> qexists_tac ‘j’ >> simp[] >> metis_tac[hdo_eof_none]) >>
  first_x_assum (qspecl_then [‘s1’, ‘hs1’, ‘rs'’, ‘evs'’, ‘s'’, ‘hs'’, ‘P ++ [(a, r)]’]
                   mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> first_x_assum (qspecl_then [‘h’, ‘k’] mp_tac) >>
      impl_tac >- fs[] >> strip_tac >> qexists_tac ‘j’ >> fs[]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
QED

(* The invariant along the simulation's run *)
Theorem run_eof_gone:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. eof_gone (n2w lfdn) (gperf EI ES (v1of (n2w lfdn) s2) n)
               (SND (hst (n2w lfdn) EI ES s2 n))
Proof
  strip_tac >> drule_all round_hacts >> strip_tac >>
  ‘sched_wf (v1of (n2w lfdn) s2)’ by (irule v1of_sched_wf >> simp[]) >>
  drule_all hrun_sim >> strip_tac >>
  Induct
  >- simp[eof_gone_def, gperf_def] >>
  qpat_assum ‘∀n. (∃evs2 s2'. hacts _ _ _ = _) ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >> fs[] >>
  simp[gperf_SUC] >>
  qpat_x_assum ‘hacts _ _ _ = SOME _’ assume_tac >> drule hacts_eof_gone >>
  disch_then (qspec_then ‘gperf EI ES (v1of (n2w lfdn) s2) n’ mp_tac) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  ‘action_ok (n2w lfdn) (wacc (gperf EI ES (v1of (n2w lfdn) s2) n)) (Read h k)’
    by fs[EVERY_MEM] >>
  pop_assum mp_tac >> simp[action_ok_def] >>
  qpat_x_assum ‘GENLIST _ _ = wacc _’ (SUBST1_TAC o SYM) >>
  simp[MEM_GENLIST] >> metis_tac[]
QED

(* On the PF echo run: a handle whose end-of-file the server has read is
   not in L1's table *)
Theorem eof_read_gone:
  echo_run lfdn pol w0 ∧ MEM (Read h k, Got (SOME [])) (SP lfdn EI V1 m) ⇒
  ALOOKUP (rstate (n2w lfdn) pol EI ES w0 m).b.tbl h = NONE
Proof
  strip_tac >> drule echo_psk_facts >> strip_tac >>
  drule_all run_eof_gone >> disch_then (qspec_then ‘m’ mp_tac) >>
  drule_then (qspec_then ‘m’ strip_assume_tac) echo_sim >>
  simp[eof_gone_def, hs_of_def] >> disch_then drule >> strip_tac >> fs[hs_of_def]
QED

(* MAIN: an fd L1 holds at end-of-file is read within three rounds *)
Theorem echo_read_soon_eof:
  echo_run lfdn pol w0 ∧
  ALOOKUP (rstate (n2w lfdn) pol EI ES w0 m).b.tbl h = SOME f ∧
  MEM f (rstate (n2w lfdn) pol EI ES w0 m).eof ⇒
  ∃i kk. i ≤ 3 ∧
         MEM (Read h kk) (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 (m + i)))
Proof
  strip_tac >>
  ‘∀k. ¬MEM (Read h k, Got (SOME [])) (SP lfdn EI V1 m)’
    by (rpt strip_tac >> drule_all eof_read_gone >> simp[]) >>
  drule_then (qspec_then ‘m’ strip_assume_tac) echo_sim >>
  ‘lfdn < dimword (:64)’ by fs[echo_run_def] >>
  qabbrev_tac ‘ps = rstate (n2w lfdn) pol EI ES w0 m’ >>
  qabbrev_tac ‘cm = FST (pcm (n2w lfdn) pol EI ES w0 m)’ >>
  Cases_on ‘hst (n2w lfdn) EI ES PSK m’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hs = hs_of ps’ by fs[] >>
  ‘pv_rel (n2w lfdn) cm ps s2’ by fs[] >>
  ‘hsim0 (n2w lfdn) (gstate EI ES V1 m) (s2, hs)’ by fs[hsim_def] >>
  ‘∃j. j < ps.b.nxt ∧ h = hdl (n2w lfdn) j ∧ ALOOKUP s2.open_fds f = SOME j’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, hs_of_def] >> metis_tac[]) >>
  ‘(EL j s2.clients).peer_closed’
    by (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> simp[pv_rel_def] >> strip_tac >>
        first_x_assum drule >> strip_tac >> gvs[]) >>
  ‘j < LENGTH s2.clients’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, hs_of_def]) >>
  ‘MEM (hdl (n2w lfdn) j) (MAP FST (gstate EI ES V1 m).conns)’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def, MEM_GENLIST] >>
        metis_tac[]) >>
  ‘∃cn. ALOOKUP (gstate EI ES V1 m).conns (hdl (n2w lfdn) j) = SOME cn’
    by (Cases_on ‘ALOOKUP (gstate EI ES V1 m).conns (hdl (n2w lfdn) j)’ >>
        fs[ALOOKUP_NONE]) >>
  ‘cn.peer_closed’
    by (qpat_x_assum ‘hsim0 _ _ _’ mp_tac >> simp[hsim0_def] >> strip_tac >>
        TRY (fs[] >> NO_TAC) >>
        qpat_x_assum ‘∀j cn. _ ∧ ALOOKUP _ _ = SOME cn ⇒ _’
          (qspecl_then [‘j’, ‘cn’] mp_tac) >> simp[]) >>
  ‘MEM (hdl (n2w lfdn) j) (wacc (gperf EI ES V1 m))’
    by (qpat_x_assum ‘GENLIST _ _ = wacc _’ (SUBST1_TAC o SYM) >> simp[MEM_GENLIST] >>
        metis_tac[]) >>
  qspecl_then [‘V1’, ‘lfdn’, ‘hdl (n2w lfdn) j’, ‘m’, ‘cn’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’, ‘cn’] read_soon_eof_s) >>
  impl_tac >- (fs[v1of_def] >> rveq >> fs[]) >>
  strip_tac >> fs[reads_c_def] >>
  drule_then (qspec_then ‘m + i’ strip_assume_tac) echo_sim >>
  qexistsl_tac [‘i’, ‘k’] >> gvs[gacts_def]
QED
