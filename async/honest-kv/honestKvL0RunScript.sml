(*
  P4 (design/46), step D: the raw L0 episodes of any server run on L1.

  The j-th raw accept is L1's j-th handle: L1's queue of accepted fds
  (acq) grows only at its tail (pf_fetch) and only the server's Accept
  pops its head (pdo), so the episodes pair up in order and the key bridge
  is the identity.  honestEchoL0Run's run invariant ri relates raw episode
  j to handle l1hdl lfd j; its step (ri_step) holds for any server.  Only
  ri_echo used echo's own fact that the server writes only through handles
  it was handed.

  ri_gen: ri along the guarded run of any server that writes only through
  handles it was handed.
  round_pair: per round, raw episode j against handle j.
  prounds_t_pcm_bound: while the guard holds, R1's client-count bound
  (for psk_upto).
*)
Theory honestKvL0Run
Ancestors
  asyncTranscript asyncServer asyncServerSafety asyncM4ServerUses asyncM4Relabel asyncM4RelabelDist
  asyncM4SockModel asyncRunOkGen honestL1PFModel honestL1PFProg
  honestL1PFSpec honestEchoL0Spec honestEchoL0Trace honestEchoL0Model honestEchoL0Inv
  honestEchoL0Out honestEchoL0Run honestKvL0Count honestL1PFRefine
Libs
  preamble

(* The server writes only through handles it was handed *)
Definition writes_accepted_def:
  writes_accepted m ⇔
    ∀h hd bs r.
      ALL_DISTINCT (haccepted (trans m h)) ∧ MEM (Write hd bs, r) (trans m h) ⇒
      MEM hd (haccepted (trans m h))
End

(* A read or write of fd in a trace where fd is accepted first comes after
   its accept *)
Theorem acc_first_accepted:
  ∀tr. acc_first fd tr ∧ MEM p tr ∧ on_fd fd p ⇒ MEM fd (accepted tr)
Proof
  Induct >> rw[acc_first_def] >> PairCases_on ‘h’ >>
  gvs[accepts_def, accepted_def, on_fd_def] >>
  every_case_tac >> gvs[]
QED

(* A server that uses only connections it was handed (asyncRunOkGen's
   uses_ok) writes only through handles it was handed, after relabelling *)
Theorem uses_ok_writes_accepted:
  uses_ok lfd m ⇒ writes_accepted (srelabel m)
Proof
  rw[writes_accepted_def, uses_ok_def] >>
  ‘rl (trans m (MAP sfs h)) (trans (srelabel m) h)’
    by (irule trans_relabel >> simp[snap_map_def]) >>
  drule rl_accepted >> strip_tac >>
  ‘MEM (Write hd bs, OPTION_MAP sfr r)
       (MAP (λ(a, r). (a, OPTION_MAP sfr r)) (trans (srelabel m) h))’
    by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘∃a r'. MEM (a, r') (trans m (MAP sfs h)) ∧ sfa a = Write hd bs’
    by (qpat_x_assum ‘MAP _ _ = MAP _ _’ (fn th => fs[GSYM th]) >>
        gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  Cases_on ‘a’ >> gvs[sfa_def] >>
  rename1 ‘MEM (Write fd d, r') _’ >>
  ‘MEM fd (accepted (trans m (MAP sfs h)))’
    by (irule acc_first_accepted >> simp[] >>
        qexists_tac ‘(Write fd d, r')’ >> simp[on_fd_def]) >>
  gvs[MEM_MAP]
QED

(* MAIN: the run invariant along the guarded run of any such server *)
Theorem ri_gen:
  writes_accepted m ∧ ri lfd m ([], ws0, []) ⇒
  ∀n h w ps evs logs.
    prounds_t lfd hw ifds m ws0 n = SOME (h, (w, ps), evs, logs) ⇒
    ri lfd m (h, (w, ps), evs)
Proof
  strip_tac >> Induct >- (simp[prounds_t_def] >> rw[] >> gvs[]) >>
  rpt gen_tac >> simp[prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds m ws0 n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’, ‘x3’, ‘x4’] mp_tac) >> simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      irule ri_step >> simp[] >> rpt (first_assum (irule_at Any) >> simp[]) >>
      rpt strip_tac >>
      ‘(∀i. i < LENGTH x0 ⇒
            LENGTH (EL i x0).results = LENGTH (new_actions (log_of m) (TAKE i x0))) ∧
       haccepted (texec m x0) = GENLIST (λi. l1hdl lfd i) x2.b.nxt’
        by gvs[ri_def] >>
      drule trans_texec >> strip_tac >>
      ‘x2.b.nxt < dimword (:64)’ by gvs[ri_def] >>
      ‘MEM hd (haccepted (trans m x0))’
        by (qpat_x_assum ‘writes_accepted m’ (irule o REWRITE_RULE [writes_accepted_def]) >>
            qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
            qpat_assum ‘haccepted (texec _ _) = _’
              (fn th => REWRITE_TAC [haccepted_APPEND, haccepted_NONE, th, APPEND_NIL]) >>
            conj_tac >- (irule ALL_DISTINCT_hdl >> simp[]) >>
            qexistsl [‘bs’, ‘NONE’] >> simp[MEM_MAP]) >>
      qpat_x_assum ‘MEM hd (haccepted (trans _ _))’ mp_tac >>
      qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >> simp[haccepted_APPEND]) >>
  rw[] >> gvs[]
QED

(* Writes do not look at answers *)
Theorem hwritten_answers:
  ∀as rs. LENGTH rs = LENGTH as ⇒
          hwritten hd (ZIP (as, MAP SOME rs)) = hwritten hd (MAP (λa. (a, NONE)) as)
Proof
  Induct >> Cases_on ‘rs’ >> fs[hwritten_def]
QED

(* MAIN, per round: at any raw prefix pre inside a round, what raw episode
   j read extends what handle j read in the rounds executed so far, and
   what it sent is a prefix of what handle j has been asked to write
   (answered or not) *)
Theorem round_pair:
  ri lfd m (h, (w, ps), evs) ∧
  ri lfd m (h ++ [sn], (w', ps'), evs ++ tevs) ∧
  hdl_room lfd ps (naccepts (new_actions (log_of m) h)) ∧
  pround lfd hw hs (w, ps) (new_actions (log_of m) h) = SOME (sn, (w', ps'), log, tevs) ∧
  evs ≼ pre ∧ pre ≼ evs ++ tevs ∧ hdln (w2n lfd) j < dimword (:64) ⇒
  hread (l1hdl lfd j) (texec m (h ++ [sn])) ≼ l0_read j pre ∧
  l0_sent j pre ≼ hwritten (l1hdl lfd j) (trans m h)
Proof
  strip_tac >>
  qabbrev_tac ‘acts = new_actions (log_of m) h’ >>
  REWRITE_TAC[l0_read_fold, l0_sent_fold] >>
  ‘ep_sn j (0, []) pre ≼ ep_sn j (0, []) (evs ++ tevs) ∧
   ep_rd j (0, []) evs ≼ ep_rd j (0, []) pre’ by simp[ep_fold_prefix] >>
  (* the end of the round *)
  qpat_assum ‘ri _ _ (h ++ [sn], _, _)’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  ‘LENGTH sn.results = LENGTH acts’
    by (qpat_x_assum ‘∀i. i < LENGTH (h ++ [sn]) ⇒ _’ (qspec_then ‘LENGTH h’ mp_tac) >>
        simp[EL_APPEND2, TAKE_APPEND1, Abbr ‘acts’]) >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  ‘ep_sn j (0, []) (evs ++ tevs) ≼ hwritten (l1hdl lfd j) (texec m (h ++ [sn]))’
    by (gvs[oi_def] >> imp_res_tac isPREFIX_APPEND_L) >>
  (* the start of the round *)
  qpat_x_assum ‘ri _ _ (h, _, _)’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  ‘hwritten (l1hdl lfd j) (texec m (h ++ [sn])) = hwritten (l1hdl lfd j) (trans m h)’
    by (drule trans_texec >> disch_then (fn th => REWRITE_TAC [th]) >>
        REWRITE_TAC[texec_SNOC, hwritten_APPEND] >> AP_TERM_TAC >>
        irule hwritten_answers >> fs[Abbr ‘acts’]) >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  ‘hread (l1hdl lfd j) (ZIP (acts, MAP SOME sn.results)) ≼ inbp lfd ps j’
    by (irule pround_hread >> gvs[hdl_room_def] >>
        conj_tac >- (Cases_on ‘l0_ep_st (0,[]) evs’ >> gvs[] >> metis_tac[]) >>
        qexistsl [‘tevs’, ‘hs’, ‘hw’, ‘log’, ‘ps'’, ‘w’, ‘w'’] >> simp[]) >>
  conj_tac
  >- (irule isPREFIX_TRANS >> qexists_tac ‘ep_rd j (0, []) evs’ >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      simp[texec_SNOC, hread_APPEND] >>
      qpat_x_assum ‘ep_rd j (0,[]) evs = _’ (fn th => REWRITE_TAC [th]) >>
      fs[Abbr ‘acts’]) >>
  irule isPREFIX_TRANS >> qexists_tac ‘ep_sn j (0, []) (evs ++ tevs)’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘ep_sn j _ (evs ++ tevs) ≼ hwritten (l1hdl _ _) _’ mp_tac >>
  qpat_x_assum ‘hwritten _ (texec _ _) = _’ mp_tac >>
  simp[]
QED

Theorem prounds_t_some_le:
  ∀k i. prounds_t lfd hw ifds m ws0 k ≠ NONE ∧ i ≤ k ⇒ prounds_t lfd hw ifds m ws0 i ≠ NONE
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on ‘i = SUC k’ >- gvs[] >>
  ‘prounds_t lfd hw ifds m ws0 k ≠ NONE’
    by (strip_tac >> qpat_x_assum ‘prounds_t _ _ _ _ _ (SUC k) ≠ NONE’ mp_tac >>
        simp[prounds_t_def]) >>
  first_x_assum (qspec_then ‘i’ mp_tac) >> simp[]
QED

(* MAIN: while the loop's guard (D40) holds, the client count stays below
   2^64 − 1, as R1 and psk_upto need *)
Theorem prounds_t_pcm_bound:
  writes_accepted m ∧ ri lfd m ([], (w0, pinit), []) ∧
  prounds_t lfd hw ifds m (w0, pinit) (SUC n) ≠ NONE ∧
  (∀i h ws evs logs. i ≤ n ∧ prounds_t lfd hw ifds m (w0, pinit) i = SOME (h, ws, evs, logs) ⇒
     hdl_room lfd (SND ws) (naccepts (new_actions (log_of m) h))) ⇒
  ∀n'. n' ≤ SUC n ⇒ SND (pcm lfd (pol_self hw) ifds m w0 n') + 1 < dimword (:64)
Proof
  strip_tac >> Cases >- simp[pcm_def] >> rename1 ‘SUC i ≤ SUC n’ >> strip_tac >>
  ‘prounds_t lfd hw ifds m (w0, pinit) i ≠ NONE’
    by (irule prounds_t_some_le >> qexists_tac ‘SUC n’ >> simp[]) >>
  Cases_on ‘prounds_t lfd hw ifds m (w0, pinit) i’ >- gvs[] >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >>
  rename1 ‘prounds_t _ _ _ _ _ i = SOME (h, (w, ps), evs, logs)’ >>
  ‘hdl_room lfd ps (naccepts (new_actions (log_of m) h))’
    by (qpat_x_assum ‘∀i h ws evs logs. _’ (qspecl_then [‘i’, ‘h’, ‘(w, ps)’, ‘evs’, ‘logs’] mp_tac) >>
        simp[]) >>
  ‘prounds_t lfd hw ifds m (w0, pinit) (SUC i) ≠ NONE’
    by (irule prounds_t_some_le >> qexists_tac ‘SUC n’ >> simp[]) >>
  qpat_x_assum ‘prounds_t _ _ _ _ _ (SUC i) ≠ NONE’ mp_tac >>
  simp[prounds_t_def] >>
  Cases_on ‘pround lfd (pol_self hw) (ifds h) (w, ps) (new_actions (log_of m) h)’ >> simp[] >>
  rename1 ‘SOME y’ >> PairCases_on ‘y’ >>
  rename1 ‘pround _ _ _ _ _ = SOME (sn, (w', ps'), log, tevs)’ >> strip_tac >>
  ‘prounds_t lfd hw ifds m (w0, pinit) (SUC i) = SOME (h ++ [sn], (w', ps'), evs ++ tevs, logs ++ [log])’
    by simp[prounds_t_def] >>
  ‘ri lfd m (h, (w, ps), evs)’
    by (drule ri_gen >> disch_then drule >> disch_then (qspecl_then [‘ifds’, ‘hw’, ‘i’] mp_tac) >> simp[]) >>
  ‘ri lfd m (h ++ [sn], (w', ps'), evs ++ tevs)’
    by (drule ri_gen >> disch_then drule >> disch_then (qspecl_then [‘ifds’, ‘hw’, ‘SUC i’] mp_tac) >> simp[]) >>
  ‘prounds_t lfd hw ifds m (w0, pinit) (SUC i) = prounds lfd (pol_self hw) ifds m (w0, pinit) (SUC i)’
    by (irule prounds_t_prounds >> rpt strip_tac >>
        qpat_x_assum ‘∀i h ws evs logs. _’ irule >> simp[] >>
        qexistsl [‘evs'’, ‘i'’, ‘logs'’] >> simp[]) >>
  ‘SND (pcm lfd (pol_self hw) ifds m w0 (SUC i)) = ps'.b.nxt + LENGTH ps'.acq’
    by (‘prounds lfd (pol_self hw) ifds m (w0, pinit) (SUC i) =
         SOME (h ++ [sn], (w', ps'), evs ++ tevs, logs ++ [log])’
          by (qpat_x_assum ‘prounds_t _ _ _ _ _ (SUC i) = prounds _ _ _ _ _ _’
                (fn th => REWRITE_TAC [GSYM th]) >>
              qpat_x_assum ‘prounds_t _ _ _ _ _ (SUC i) = SOME _’ ACCEPT_TAC) >>
        drule prounds_pcm >> simp[]) >>
  ‘LENGTH ps'.acq ≤ 1’ by gvs[ri_def] >>
  ‘ps.b.nxt + naccepts (new_actions (log_of m) h) + 2 < dimword (:64)’ by gvs[hdl_room_def] >>
  qpat_x_assum ‘ri lfd m (h, _, _)’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  Cases_on ‘l0_ep_st (0, []) evs’ >>
  ‘ps'.b.nxt ≤ ps.b.nxt + naccepts (new_actions (log_of m) h)’
    by (‘ps.b.nxt + naccepts (new_actions (log_of m) h) < dimword (:64)’
          by (qpat_x_assum ‘_ + _ + 2 < dimword (:64)’ mp_tac >> simp[]) >>
        drule_all pround_acc >> simp[]) >>
  qpat_x_assum ‘SND (pcm _ _ _ _ _ _) = _’ SUBST1_TAC >>
  qpat_x_assum ‘LENGTH ps'.acq ≤ 1’ mp_tac >>
  qpat_x_assum ‘ps'.b.nxt ≤ _’ mp_tac >>
  qpat_x_assum ‘_ + _ + 2 < dimword (:64)’ mp_tac >>
  rpt (pop_assum kall_tac) >> simp[]
QED
