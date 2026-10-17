(*
  Moonshot step 12, C1 (close-v2): the client's E1 run, read on its raw L0
  events at a round boundary.  One episode map lc, fixed for the whole
  run, such that at every round:
   - no listen, every connect is to a, no accept (e1TraceEvents);
   - episode j sent a prefix of rqs (lc j)'s requests, lc j < N, and at
     most one episode per logical connection sent anything;
   - no close of fds 0-2 (moonshotStdioClose).

  The chain for the sends: episode j's bytes are what E1 credits channel
  j (moonshotSentGlue), a prefix of channel j's bytes in the world built
  from the run (l1ep_refines_ehl_upto_sent's sent_inv), which are what the
  history wrote on channel j's handle (e1TraceChan); the client's
  guarantee on its handles (client_l1_guar) bounds those.  lc j is the
  guarantee's logical connection of channel j's handle (blc).
*)
Theory moonshotClientL0Rounds
Ancestors
  e1TraceChan e1TraceEvents moonshotClientTotal moonshotClientSpec moonshotClient
  moonshotStdioClose moonshotSentGlue honestL1EPRefine honestL1EPModel l0sysEpisodes
  honestL0Outcome
Libs
  preamble

(* ------------------------------------------------------------------------
   The client's actions
   ------------------------------------------------------------------------ *)

Theorem client_connects_a:
  MEM (EConnect p) (new_actions (log_of (cprog a N rqs)) h) ⇒ p = a
Proof
  strip_tac >>
  strip_assume_tac moonshotClientTheory.cstate_last >>
  gvs[cprog_new_actions, MEM_cacts, cact1_def] >> every_case_tac >> gvs[]
QED

Theorem client_evs_ok:
  erounds lfd pol ifds (cprog a N rqs) ws0 n = SOME (h, ws, evs, logs) ⇒
  EVERY (e1ev_ok (λp. p = a)) evs
Proof
  strip_tac >>
  drule_at (Pos last) (Q.SPEC ‘λp. p = a’ (Q.GEN ‘P’ erounds_evs_ok) |> BETA_RULE) >>
  disch_then (qspec_then ‘a’ mp_tac) >> impl_tac >- (rpt strip_tac >> drule client_connects_a >> simp[]) >> simp[]
QED

(* The listener is never in the interest, nor in L1's table after a
   round's actions: the client accepts nothing *)
Theorem client_noaccept:
  a < 65536 ∧ N < cbound ∧ l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀n h ws evs logs.
    erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») evs
Proof
  strip_tac >>
  ‘(∀n. erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) n ≠ NONE) ∧
   ∀n. SND (ecm lfd pol (cifds a N rqs) (cprog a N rqs) w0 n) + 1 < dimword (:64)’
    by (irule client_l1_total >> simp[]) >>
  match_mp_tac erounds_noaccept >> rpt gen_tac >> strip_tac >> conj_tac
  >- (‘∃h' ws' evs' logs'.
         erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) n = SOME (h', ws', evs', logs') ∧
         cinv lfd N (cstate a N rqs h') (SND ws') (cready h') ∧ (SND ws').p.b.nxt < cbound + N’
        by metis_tac[client_rounds] >>
      gvs[] >> simp[cifds_def] >> irule cinv_not_lfd >>
      qexistsl_tac [‘N’, ‘cready h’, ‘SND ws’] >> simp[] >>
      pop_assum mp_tac >> qpat_x_assum ‘N < cbound’ mp_tac >> simp[cbound_def]) >>
  ‘erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) (SUC n) ≠ NONE’ by simp[] >>
  Cases_on ‘erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) (SUC n)’ >> gvs[] >>
  rename1 ‘SOME r’ >> PairCases_on ‘r’ >>
  qspecl_then [‘SUC n’, ‘cifds a N rqs’, ‘cprog a N rqs’] mp_tac
    (Q.GENL [‘N’, ‘ifds’, ‘m’] l1ep_refines_ehl_upto_sent) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [‘SUC n’, ‘r0’, ‘(r1, r2)’, ‘r3’, ‘r4’] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum ‘∀n'. n' < SUC n ⇒ eround_own _ _ _ _ _ _’ (qspec_then ‘n’ mp_tac) >>
  simp[eround_own_def] >> PairCases_on ‘ws1’ >>
  disch_then (qspecl_then [‘LENGTH (new_actions (log_of (cprog a N rqs)) h)’,
                           ‘rs’, ‘evs1’, ‘ws10’, ‘ws11’] mp_tac) >>
  simp[TAKE_LENGTH_ID, eown_def, ALL_DISTINCT_APPEND]
QED

(* ------------------------------------------------------------------------
   The episode map: a channel's handle's logical connection
   ------------------------------------------------------------------------ *)

Definition blc_def:
  blc (lcg : word64 -> num) (B : num -> (num # word64) list) j =
    if ∃n hd. ALOOKUP (B n) j = SOME hd then lcg (@hd. ∃n. ALOOKUP (B n) j = SOME hd) else 0
End

Theorem blc_eq:
  (∀n n' j hd. ALOOKUP (B n) j = SOME hd ∧ n ≤ n' ⇒ ALOOKUP (B n') j = SOME hd) ∧
  ALOOKUP (B n) j = SOME hd ⇒
  blc lcg B j = lcg hd
Proof
  strip_tac >> simp[blc_def] >> IF_CASES_TAC >- (SELECT_ELIM_TAC >> conj_tac
  >- metis_tac[] >>
  rpt strip_tac >> rename1 ‘ALOOKUP (B m) j = SOME hd'’ >>
  ‘ALOOKUP (B (MAX n m)) j = SOME hd ∧ ALOOKUP (B (MAX n m)) j = SOME hd'’
    by (conj_tac >> qpat_assum ‘∀n n' j hd. _ ⇒ _’ irule >> simp[] >>
        first_assum (irule_at Any) >> simp[]) >>
  gvs[]) >> metis_tac[]
QED

Theorem blc_eq_all:
  (∀n n' j hd. ALOOKUP (B n) j = SOME hd ∧ n ≤ n' ⇒ ALOOKUP (B n') j = SOME hd) ⇒
  ∀j hd. ALOOKUP (B n) j = SOME hd ⇒ blc lcg B j = lcg hd
Proof
  rpt strip_tac >> irule blc_eq >> metis_tac[]
QED

Theorem blc_lt:
  (∀n j hd. ALOOKUP (B n) j = SOME hd ⇒ lcg hd < N) ∧ 0 < N ⇒ blc lcg B j < N
Proof
  rw[blc_def] >> SELECT_ELIM_TAC >> metis_tac[]
QED

Theorem made_conn:
  hl_made hd ps ∧ (∀x r. MEM (x, r) ps ⇒ ∀l. x ≠ EAccept l) ⇒ MEM hd (hl_conn_handles ps)
Proof
  rw[hl_made_def] >- (simp[hl_conn_handles_def, hl_connects_def, MEM_FLAT, MEM_MAP,
                            PULL_EXISTS, EXISTS_PROD] >>
                       qexistsl_tac [‘p’, ‘EConnected (SOME hd)’, ‘EConnect p’] >> simp[]) >>
  metis_tac[]
QED

Theorem alookup_inj:
  ALL_DISTINCT (MAP SND B) ∧ ALOOKUP B j = SOME hd ∧ ALOOKUP B j' = SOME hd ⇒ j = j'
Proof
  strip_tac >> imp_res_tac ALOOKUP_MEM >> metis_tac[bind_inj]
QED

Theorem prefix_nonnil:
  x ≼ y ∧ x ≠ [] ⇒ y ≠ []
Proof
  Cases_on ‘x’ >> Cases_on ‘y’ >> simp[]
QED

Theorem gchinv_distinct:
  gchinv lfd B ps St ⇒ ALL_DISTINCT (MAP SND B)
Proof
  PairCases_on ‘St’ >> simp[gchinv_def]
QED

Theorem sent_in_binds:
  sent_inv cm (FST St) es R ∧ gchinv lfd B ps St ⇒
  ∀j. R j = [] ∨ ∃hd. ALOOKUP B j = SOME hd ∧ R j ≼ hl_sent hd ps
Proof
  PairCases_on ‘St’ >> rw[sent_inv_def, gchinv_def] >>
  Cases_on ‘j < LENGTH St0.chans’ >> simp[] >>
  qpat_x_assum ‘∀j. j < LENGTH St0.chans ⇒ R j ≼ _ ∧ _’ drule >> strip_tac >>
  qpat_x_assum ‘∀j. j < LENGTH St0.chans ⇒ (EL j St0.chans).sent = _’ drule >>
  strip_tac >> Cases_on ‘ALOOKUP B j’ >> gvs[] >> Cases_on ‘R j’ >> gvs[]
QED

(* A round's sends, given each sending episode's handle (small contexts) *)
Theorem round_sent_bound:
  (∀j. l0_ep_sent j evs = [] ∨
       ∃hd. ALOOKUP B j = SOME hd ∧ l0_ep_sent j evs ≼ hl_sent hd ps) ∧
  (∀j hd. ALOOKUP B j = SOME hd ⇒ blc lc BB j = lc hd) ∧
  (∀hd. hl_sent hd ps ≼ brequests (rqs (lc hd))) ⇒
  ∀j. l0_ep_sent j evs ≼ brequests (rqs (blc lc BB j))
Proof
  rpt strip_tac >> qpat_x_assum ‘∀j. _ ∨ _’ (qspec_then ‘j’ strip_assume_tac) >- simp[] >>
  qpat_x_assum ‘∀j hd. ALOOKUP B j = SOME hd ⇒ _’ drule >> disch_then SUBST1_TAC >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘hl_sent hd ps’ >> conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         qpat_x_assum ‘∀hd. hl_sent hd ps ≼ _’ (qspec_then ‘hd’ ACCEPT_TAC)]
QED

Theorem round_sent_inj:
  (∀j. l0_ep_sent j evs = [] ∨
       ∃hd. ALOOKUP B j = SOME hd ∧ l0_ep_sent j evs ≼ hl_sent hd ps) ∧
  (∀j hd. ALOOKUP B j = SOME hd ⇒ blc lc BB j = lc hd) ∧
  (∀hd hd'. hl_sent hd ps ≠ [] ∧ hl_sent hd' ps ≠ [] ∧ lc hd' = lc hd ⇒ hd' = hd) ∧
  ALL_DISTINCT (MAP SND B) ⇒
  ∀j j'. l0_ep_sent j evs ≠ [] ∧ l0_ep_sent j' evs ≠ [] ∧ blc lc BB j = blc lc BB j' ⇒
         j = j'
Proof
  rpt strip_tac >>
  ‘∃hd. ALOOKUP B j = SOME hd ∧ l0_ep_sent j evs ≼ hl_sent hd ps’ by metis_tac[] >>
  ‘∃hd'. ALOOKUP B j' = SOME hd' ∧ l0_ep_sent j' evs ≼ hl_sent hd' ps’ by metis_tac[] >>
  ‘hl_sent hd ps ≠ [] ∧ hl_sent hd' ps ≠ []’ by metis_tac[prefix_nonnil] >>
  ‘lc hd' = lc hd’ by metis_tac[] >>
  ‘hd' = hd’ by metis_tac[] >>
  metis_tac[alookup_inj]
QED

(* ------------------------------------------------------------------------
   The rounds
   ------------------------------------------------------------------------ *)

Definition client_round_safe_def:
  client_round_safe a N rqs (lc : num -> num) evs ⇔
    EVERY (e1ev_ok (λp. p = a)) evs ∧
    EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») evs ∧
    (∀j. l0_ep_sent j evs ≼ brequests (rqs (lc j))) ∧
    (∀j j'. l0_ep_sent j evs ≠ [] ∧ l0_ep_sent j' evs ≠ [] ∧ lc j = lc j' ⇒ j = j') ∧
    no_close_stdio evs
End

(* client_rounds_safe's per-round premises, in its goal's names *)
val blc_tac =
  match_mp_tac blc_eq_all >> first_assum ACCEPT_TAC
val sent_tac =
  gen_tac >> qpat_assum ‘ehhist _ lv _ _ PW n = h’ (SUBST1_TAC o SYM) >>
  qpat_assum ‘∀n hd. hl_sent hd _ ≼ _’ (qspecl_then [‘n’, ‘hd’] ACCEPT_TAC)
val inj_tac =
  qpat_assum ‘ehhist _ lv _ _ PW n = h’ (SUBST1_TAC o SYM) >>
  qpat_assum ‘∀n hd hd'. hl_sent hd _ ≠ [] ∧ _ ⇒ hd' = hd’ (qspec_then ‘n’ ACCEPT_TAC)
val distinct_tac =
  qpat_assum ‘∀n. gchinv _ _ _ _’ (qspec_then ‘n’ mp_tac) >>
  disch_then (ACCEPT_TAC o MATCH_MP gchinv_distinct)

Theorem client_rounds_safe:
  2 ≤ N ∧ N < cbound ∧ (∀i. EVERY valid_brequest (rqs i)) ∧ a < 65536 ∧
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  MEM 0w (l0_used w0) ∧ MEM 1w (l0_used w0) ∧ MEM 2w (l0_used w0) ⇒
  ∃lc. (∀j. lc j < N) ∧
       ∀n h ws evs logs.
         erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) n = SOME (h, ws, evs, logs) ⇒
         client_round_safe a N rqs lc evs
Proof
  strip_tac >>
  ‘(∀n. erounds lfd pol (cifds a N rqs) (cprog a N rqs) (w0, einit) n ≠ NONE) ∧
   ∀n. SND (ecm lfd pol (cifds a N rqs) (cprog a N rqs) w0 n) + 1 < dimword (:64)’
    by (irule client_l1_total >> simp[]) >>
  qabbrev_tac ‘lv = elv lfd pol (cifds a N rqs) (cprog a N rqs) w0’ >>
  qabbrev_tac ‘PW = pew lfd 0 pol (cifds a N rqs) (cprog a N rqs) w0 []’ >>
  qabbrev_tac ‘B = ehbinds lfd lv (cifds a N rqs) (cprog a N rqs) PW’ >>
  ‘client_guar' a N rqs lfd lv (cifds a N rqs) (cprog a N rqs) PW’
    by (unabbrev_all_tac >> irule client_l1_guar >> simp[]) >>
  qpat_x_assum ‘client_guar' _ _ _ _ _ _ _ _’
    (strip_assume_tac o SIMP_RULE std_ss [client_guar'_def, LET_THM]) >>
  ‘∀n. gchinv lfd (B n)
         (hl_pairs (cprog a N rqs) (ehhist lfd lv (cifds a N rqs) (cprog a N rqs) PW n))
         (ehst lfd lv (cifds a N rqs) (cprog a N rqs) PW n)’
    by (qunabbrev_tac ‘B’ >> irule ehrounds_gchinv >>
        simp[Abbr ‘PW’, pew_def, erun_alloc_ok]) >>
  ‘∀n j hd. MEM (j, hd) (B n) ⇒
            hl_made hd (hl_pairs (cprog a N rqs) (ehhist lfd lv (cifds a N rqs) (cprog a N rqs) PW n))’
    by (qunabbrev_tac ‘B’ >> match_mp_tac ehbinds_made >> simp[]) >>
  ‘∀n j hd. ALOOKUP (B n) j = SOME hd ⇒ lc hd < N’
    by (rpt strip_tac >> drule ALOOKUP_MEM >> strip_tac >>
        qpat_x_assum ‘∀n j hd. MEM (j, hd) (B n) ⇒ _’ drule >> strip_tac >>
        qpat_x_assum ‘∀n hd. MEM hd (hl_conn_handles _) ⇒ lc hd < N’ irule >>
        qexists_tac ‘n’ >> irule made_conn >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC,
               rpt gen_tac >> strip_tac >>
               qpat_x_assum ‘∀n x r. MEM (x, r) _ ⇒ _’ drule >> simp[]]) >>
  ‘∀n n' j hd. ALOOKUP (B n) j = SOME hd ∧ n ≤ n' ⇒ ALOOKUP (B n') j = SOME hd’
    by (rpt strip_tac >> qunabbrev_tac ‘B’ >> irule ehbinds_lookup_mono >>
        qexists_tac ‘n’ >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac ‘blc lc B’ >> conj_tac
  >- (gen_tac >> irule blc_lt >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, qpat_x_assum ‘2 ≤ N’ mp_tac >> simp[]]) >>
  rpt gen_tac >> strip_tac >>
  (* the round's sends, through E1's credit and the built world *)
  ‘MEM 0w (l0_used w0)’ by simp[] >>
  qspecl_then [‘w0’, ‘lfd’, ‘pol’, ‘cifds a N rqs’, ‘cprog a N rqs’] mp_tac
    (Q.GENL [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’] l0_ep_sent_run) >>
  impl_tac >- simp[] >> disch_then drule >> strip_tac >>
  qspecl_then [‘n’, ‘cifds a N rqs’, ‘cprog a N rqs’, ‘0’, ‘[]’] mp_tac
    (Q.GENL [‘N’, ‘ifds’, ‘m’, ‘a’, ‘calls’] l1ep_refines_ehl_upto_sent) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >> simp[] >> strip_tac >>
  ‘ehhist lfd lv (cifds a N rqs) (cprog a N rqs) PW n = h’
    by (qunabbrev_tac ‘lv’ >> qunabbrev_tac ‘PW’ >> first_assum ACCEPT_TAC) >>
  ‘∀j. l0_ep_sent j evs = [] ∨
       ∃hd. ALOOKUP (B n) j = SOME hd ∧
            l0_ep_sent j evs ≼ hl_sent hd (hl_pairs (cprog a N rqs) h)’
    by (qpat_x_assum ‘∀n. gchinv _ _ _ _’ (qspec_then ‘n’ assume_tac) >>
        qunabbrev_tac ‘lv’ >> qunabbrev_tac ‘PW’ >>
        qpat_x_assum ‘sent_inv _ _ _ _’ assume_tac >>
        drule_all sent_in_binds >>
        qpat_x_assum ‘ehhist _ _ _ _ _ n = h’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘∀j. l0_ep_sent j evs = _’ (fn th => REWRITE_TAC [th]) >>
        simp[]) >>
  ‘EVERY (e1ev_ok (λp. p = a)) evs’
    by (drule client_evs_ok >> simp[]) >>
  ‘EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») evs’
    by (drule_at (Pos last) client_noaccept >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  REWRITE_TAC[client_round_safe_def] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qspecl_then [‘B n’, ‘hl_pairs (cprog a N rqs) h’, ‘B’, ‘lc’, ‘rqs’, ‘evs’] mp_tac
        (Q.GENL [‘B’, ‘ps’, ‘BB’, ‘lc’, ‘rqs’, ‘evs’] round_sent_bound) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, blc_tac, sent_tac]) >>
      disch_then ACCEPT_TAC)
  >- (qspecl_then [‘B n’, ‘hl_pairs (cprog a N rqs) h’, ‘B’, ‘lc’, ‘evs’] mp_tac
        (Q.GENL [‘B’, ‘ps’, ‘BB’, ‘lc’, ‘evs’] round_sent_inj) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, blc_tac, inj_tac, distinct_tac]) >>
      disch_then ACCEPT_TAC) >>
  drule_at (Pos last) erounds_no_close_stdio >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED
