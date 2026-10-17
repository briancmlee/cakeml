(*
  B2, isolated: a proof of moonshotStep12Stmts' b2_iso_stmt.

  The pairing cn is sys_causal's: two episodes are paired when, at the end
  of the run, their channels are peers.  What isolation adds is
  b2_quiet_ab: an episode on a or b that cn leaves unpaired has read
  nothing.  At any instant t such an episode's channel either
   - has no peer: a connect to a or b gets data from outside only by an
     EArrive, which isolation forbids (I3); an accept on a or b always has
     a peer, since outside processes do not connect to a or b (I1, I2); or
   - has a peer that is not an episode of its process at t (else the two
     would be paired at the end): such a channel has sent nothing (oinv),
     because no process ever has a socket on fd 0 (zinv, from fd0_safe).
*)
Theory moonshotB2Iso
Ancestors
  moonshotB2IsoWorld moonshotStep12Stmts moonshotSysGlue moonshotW2
  l0sysRun l0sysStep l0sysCausal l0sysMono l0sysInv l0sysInvCall l0sysEpisodes
  l0sys honestL0World honestL0Rely
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The invariants *)

(* I3: an unpaired end on a or b has heard nothing *)
Definition i3_def:
  i3 a b (s : sysstate) ⇔
    ∀e. is_end s e ∧ s.peer e = NONE ∧ on_ab a b s e ⇒ (sys_chan s e).peer_sent = []
End

(* I1: a connection queued on a listener of a or b is paired *)
Definition i1_def:
  i1 a b (s : sysstate) ⇔
    ∀k l p q c. k < LENGTH s.procs ∧ MEM (l, p, q) (EL k s.procs).listeners ∧ MEM c q ∧
                (p = a ∨ p = b) ⇒ s.peer (k, c) ≠ NONE
End

(* I2: an episode accepted on a or b is paired *)
Definition i2_def:
  i2 a b rs (s : sysstate) css ⇔
    ∀k j p. k < LENGTH s.procs ∧ j < LENGTH (css k) ∧
            EL j (ep_roles [] (proc_events k rs)) = Accepted p ∧ (p = a ∨ p = b) ⇒
            s.peer (k, EL j (css k)) ≠ NONE
End

(* Each process: no socket on fd 0, and its non-episode channels sent nothing *)
Definition zo_def:
  zo RS rs (s : sysstate) css ⇔
    ∀k. k < LENGTH s.procs ⇒
        zinv (proc_events k RS) (proc_events k rs) (EL k s.procs) ∧ oinv (EL k s.procs) (css k)
End

(*---------------------------------------------------------------------------*)
(* I3 *)

Theorem i3_fields[simp]:
  (i3 a b (s with moved := X1) ⇔ i3 a b s) ∧ (i3 a b (s with acked := X2) ⇔ i3 a b s) ∧
  (i3 a b (s with finned := X3) ⇔ i3 a b s) ∧ (i3 a b (s with alive := X4) ⇔ i3 a b s)
Proof
  simp[i3_def, on_ab_def]
QED

Theorem i3_local:
  i3 a b s ∧ k < LENGTH s.procs ∧ wmono (EL k s.procs) w' ⇒
  i3 a b (s with procs := LUPDATE w' k s.procs)
Proof
  strip_tac >> drule_all local_chans >> strip_tac >>
  rewrite_tac[i3_def] >> rpt strip_tac >>
  ‘on_ab a b s e’ by fs[on_ab_def] >>
  Cases_on ‘is_end s e’
  >- (‘cmono (sys_chan s e) (sys_chan (s with procs := LUPDATE w' k s.procs) e)’
        by metis_tac[] >>
      fs[cmono_def] >> qpat_x_assum ‘i3 _ _ _’ mp_tac >> rewrite_tac[i3_def] >>
      disch_then irule >> fs[]) >>
  metis_tac[]
QED

Theorem i3_target:
  i3 a b s ∧ (is_end s e ⇒ (sys_chan s e).peer_sent = []) ⇒
  i3 a b (s with target := (e =+ x) s.target)
Proof
  rw[i3_def, on_ab_def, APPLY_UPDATE_THM] >> Cases_on ‘e = e'’ >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem i3_peer:
  i3 a b s ⇒ i3 a b (s with peer := (e =+ SOME x) ((e' =+ SOME y) s.peer))
Proof
  rw[i3_def, on_ab_def, APPLY_UPDATE_THM] >> first_x_assum irule >>
  gvs[on_ab_def, AllCaseEqs()]
QED

Theorem i3_deliver:
  i3 a b s ∧ k < LENGTH s.procs ∧
  (∀j bs. a' = LData j bs ⇒ s.peer (k, j) = NONE ⇒ ¬on_ab a b s (k, j)) ⇒
  i3 a b (sys_deliver k a' s)
Proof
  strip_tac >> Cases_on ‘∃j bs. a' = LData j bs’
  >- (fs[] >> rveq >> fs[] >>
      rewrite_tac[i3_def] >> rpt strip_tac >> rename1 ‘is_end _ e’ >> PairCases_on ‘e’ >>
      ‘s.peer (e0, e1) = NONE ∧ on_ab a b s (e0, e1)’ by fs[sys_deliver_def, on_ab_def] >>
      ‘is_end s (e0, e1)’
        by (qpat_x_assum ‘is_end (sys_deliver _ _ _) _’ mp_tac >>
            simp[is_end_def, sys_deliver_def, EL_LUPDATE] >> rw[deliver_data]) >>
      ‘(sys_chan s (e0, e1)).peer_sent = []’
        by (qpat_x_assum ‘i3 _ _ _’ mp_tac >> rewrite_tac[i3_def] >> disch_then irule >> simp[]) >>
      Cases_on ‘e0 = k’ >> fs[sys_deliver_def, sys_chan_def, EL_LUPDATE, is_end_def] >>
      simp[deliver_data] >> rw[] >> fs[]) >>
  fs[sys_deliver_def] >> irule i3_local >> simp[] >> irule wmono_deliver >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* I1 *)

Theorem i1_fields[simp]:
  (i1 a b (s with moved := X1) ⇔ i1 a b s) ∧ (i1 a b (s with acked := X2) ⇔ i1 a b s) ∧
  (i1 a b (s with finned := X3) ⇔ i1 a b s) ∧ (i1 a b (s with alive := X4) ⇔ i1 a b s) ∧
  (i1 a b (s with target := X5) ⇔ i1 a b s)
Proof
  simp[i1_def]
QED

Theorem i1_local:
  i1 a b s ∧ k < LENGTH s.procs ∧ lsub (EL k s.procs) w' ⇒
  i1 a b (s with procs := LUPDATE w' k s.procs)
Proof
  strip_tac >> rewrite_tac[i1_def] >> qx_genl_tac [‘k1’, ‘l’, ‘p’, ‘q’, ‘c’] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum ‘i1 _ _ _’ mp_tac >> rewrite_tac[i1_def] >> strip_tac >>
  ‘k1 < LENGTH s.procs’ by fs[LENGTH_LUPDATE] >>
  Cases_on ‘k1 = k’
  >- (qpat_x_assum ‘k1 = k’ SUBST_ALL_TAC >>
      ‘MEM (l, p, q) w'.listeners’ by fs[EL_LUPDATE] >>
      ‘∃q0. MEM (l, p, q0) (EL k s.procs).listeners ∧ MEM c q0’
        by (qpat_x_assum ‘lsub _ _’ mp_tac >> rewrite_tac[lsub_def] >>
            disch_then drule_all >> rewrite_tac[]) >>
      simp_tac (srw_ss()) [] >> first_x_assum irule >> metis_tac[]) >>
  ‘MEM (l, p, q) (EL k1 s.procs).listeners’ by fs[EL_LUPDATE] >>
  simp_tac (srw_ss()) [] >> first_x_assum irule >> metis_tac[]
QED

Theorem i1_peer:
  i1 a b s ∧ (∀e. s.peer e ≠ NONE ⇒ P e ≠ NONE) ⇒ i1 a b (s with peer := P)
Proof
  rw[i1_def] >> first_x_assum irule >> first_x_assum irule >> metis_tac[]
QED

Theorem deliver_listeners:
  (∀p. a ≠ LIncoming p) ⇒ (l0_deliver w a).listeners = w.listeners
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> simp[]
QED

Theorem i1_deliver:
  i1 a b s ∧ k < LENGTH s.procs ∧ (∀p. a' ≠ LIncoming p) ⇒ i1 a b (sys_deliver k a' s)
Proof
  rw[sys_deliver_def] >>
  ‘(l0_deliver (EL k s.procs) a').listeners = (EL k s.procs).listeners’
    by (irule deliver_listeners >> simp[]) >>
  irule i1_local >> simp[lsub_def] >> metis_tac[]
QED

(* A new queued connection: on a port other than a and b, or paired *)
Theorem i1_incoming_gen:
  i1 a b s ∧ sys_room s k p ∧ ALL_DISTINCT (MAP FST (EL k s.procs).listeners) ∧
  ((p = a ∨ p = b) ⇒ P (k, LENGTH (EL k s.procs).chans) ≠ NONE) ∧
  (∀e. s.peer e ≠ NONE ⇒ P e ≠ NONE) ⇒
  i1 a b ((sys_deliver k (LIncoming p) s) with peer := P)
Proof
  strip_tac >> ‘k < LENGTH s.procs’ by fs[sys_room_def] >>
  ‘FILTER (λ(l, p', q). p' = p) (EL k s.procs).listeners ≠ []’
    by (fs[sys_room_def] >> every_case_tac >> fs[]) >>
  rewrite_tac[i1_def] >> qx_genl_tac [‘k1’, ‘l’, ‘p1’, ‘q’, ‘c’] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >> simp_tac (srw_ss()) [] >>
  ‘k1 < LENGTH s.procs’ by fs[sys_deliver_def] >>
  Cases_on ‘k1 = k’
  >- (qpat_x_assum ‘k1 = k’ SUBST_ALL_TAC >>
      ‘MEM (l, p1, q) (l0_deliver (EL k s.procs) (LIncoming p)).listeners’
        by (qpat_x_assum ‘MEM (l, p1, q) _’ mp_tac >> simp[sys_deliver_def, EL_LUPDATE]) >>
      drule_all incoming_listeners >> strip_tac
      >- (qpat_x_assum ‘∀e. s.peer e ≠ NONE ⇒ _’ irule >>
          qpat_x_assum ‘i1 _ _ _’ mp_tac >> rewrite_tac[i1_def] >>
          disch_then irule >> metis_tac[]) >>
      qpat_x_assum ‘c = _’ SUBST_ALL_TAC >> qpat_x_assum ‘p1 = p’ SUBST_ALL_TAC >>
      qpat_x_assum ‘p = a ∨ p = b ⇒ _’ irule >> rewrite_tac[] >>
      qpat_x_assum ‘p = a ∨ p = b’ ACCEPT_TAC) >>
  ‘MEM (l, p1, q) (EL k1 s.procs).listeners’
    by (qpat_x_assum ‘MEM (l, p1, q) _’ mp_tac >> simp[sys_deliver_def, EL_LUPDATE]) >>
  qpat_x_assum ‘∀e. s.peer e ≠ NONE ⇒ _’ irule >>
  qpat_x_assum ‘i1 _ _ _’ mp_tac >> rewrite_tac[i1_def] >>
  disch_then irule >> metis_tac[]
QED

Theorem i1_incoming:
  i1 a b s ∧ sys_room s k p ∧ ALL_DISTINCT (MAP FST (EL k s.procs).listeners) ∧ p ≠ a ∧ p ≠ b ⇒
  i1 a b (sys_deliver k (LIncoming p) s)
Proof
  strip_tac >>
  ‘sys_deliver k (LIncoming p) s = (sys_deliver k (LIncoming p) s) with peer := s.peer’
    by simp[sys_deliver_def, l0sysTheory.sysstate_component_equality] >>
  pop_assum SUBST1_TAC >> irule i1_incoming_gen >> simp[]
QED

Theorem i1_pair:
  i1 a b s ∧ sys_room s k' p ∧ ALL_DISTINCT (MAP FST (EL k' s.procs).listeners) ⇒
  i1 a b (sys_pair e k' p s)
Proof
  strip_tac >> simp[sys_pair_def] >>
  ‘(sys_deliver k' (LIncoming p) s).peer = s.peer’ by simp[sys_deliver_def] >>
  ‘LENGTH (EL k' (sys_deliver k' (LIncoming p) s).procs).chans ≥ 0’ by simp[] >>
  ‘(EL k' (sys_deliver k' (LIncoming p) s).procs) = l0_deliver (EL k' s.procs) (LIncoming p)’
    by (fs[sys_room_def, sys_deliver_def, EL_LUPDATE]) >>
  irule i1_incoming_gen >> simp[] >> rw[APPLY_UPDATE_THM]
QED

(*---------------------------------------------------------------------------*)
(* I2 *)

Theorem i2_mono:
  i2 a b rs s css ∧ LENGTH s'.procs = LENGTH s.procs ∧
  (∀e e'. s.peer e = SOME e' ⇒ s'.peer e = SOME e') ⇒
  i2 a b rs s' css
Proof
  rewrite_tac[i2_def] >> rpt strip_tac >>
  ‘s.peer (k, EL j (css k)) ≠ NONE’
    by (qpat_x_assum ‘∀k j p. _’ irule >> simp[] >> metis_tac[]) >>
  Cases_on ‘s.peer (k, EL j (css k))’ >> fs[] >> res_tac >> fs[]
QED

Theorem i2_other:
  (∀k nm conf bys out. r ≠ Call k nm conf bys out) ⇒
  (i2 a b (rs ++ [r]) s css ⇔ i2 a b rs s css)
Proof
  simp[i2_def, proc_events_other]
QED

Theorem i2_call:
  sinv rs s css ∧ i1 a b s ∧ i2 a b rs s css ∧ k < LENGTH s.procs ∧
  l0_call nm (unblock nm conf) bys (EL k s.procs) = SOME (FFIreturn out w1) ⇒
  i2 a b (rs ++ [Call k nm conf bys out]) (call_state s k nm conf bys w1)
     (call_css s k nm conf bys out css)
Proof
  strip_tac >>
  qabbrev_tac ‘w = EL k s.procs’ >>
  qabbrev_tac ‘ev = IO_event (ExtCall nm) conf (ZIP (bys, out))’ >>
  qabbrev_tac ‘evs = proc_events k rs’ >>
  ‘pk rs s css k’ by fs[sinv_def] >>
  ‘l0_rely w ∧ pinv evs w (css k)’
    by (qpat_x_assum ‘pk rs s css k’ mp_tac >> simp[pk_def, Abbr ‘w’, Abbr ‘evs’]) >>
  ‘LENGTH (ep_roles [] evs) = LENGTH (css k)’ by gvs[LENGTH_ep_roles, pinv_def] >>
  ‘(call_state s k nm conf bys w1).peer = s.peer ∧
   LENGTH (call_state s k nm conf bys w1).procs = LENGTH s.procs’ by simp[call_state_def] >>
  rewrite_tac[i2_def] >> qx_genl_tac [‘k0’, ‘j’, ‘p’] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum ‘(call_state _ _ _ _ _ _).peer = _’ (fn th => rewrite_tac[th]) >>
  Cases_on ‘k0 = k’
  >- (qpat_x_assum ‘k0 = k’ SUBST_ALL_TAC >>
      ‘proc_events k (rs ++ [Call k nm conf bys out]) = evs ++ [ev]’
        by simp[proc_events_SNOC, Abbr ‘evs’, Abbr ‘ev’] >>
      ‘call_css s k nm conf bys out css k = css k ++ new_chans w ev’
        by simp[call_css_def, APPLY_UPDATE_THM, Abbr ‘w’, Abbr ‘ev’] >>
      ‘ep_roles [] (evs ++ [ev]) = ep_roles [] evs ++ ev_role (lsn evs) ev’
        by simp[ep_roles_SNOC] >>
      qpat_x_assum ‘p = a ∨ p = b’ mp_tac >> fs[] >> DISCH_TAC >>
      Cases_on ‘j < LENGTH (css k)’
      >- (‘EL j (ep_roles [] evs ++ ev_role (lsn evs) ev) = EL j (ep_roles [] evs) ∧
           EL j (css k ++ new_chans w ev) = EL j (css k)’
            by (conj_tac >> irule EL_APPEND1 >> fs[]) >>
          fs[] >> qpat_x_assum ‘i2 _ _ _ _ _’ mp_tac >> rewrite_tac[i2_def] >>
          disch_then irule >> simp[] >> metis_tac[]) >>
      Cases_on ‘ev_new ev’ >- fs[new_chans_def] >>
      rename1 ‘ev_new ev = SOME x’ >> PairCases_on ‘x’ >>
      ‘j = LENGTH (css k)’ by (Cases_on ‘x1’ >> fs[new_chans_def]) >>
      qpat_x_assum ‘j = _’ SUBST_ALL_TAC >>
      ‘∀r. EL (LENGTH (css k)) (ep_roles [] evs ++ [r]) = r’
        by (gen_tac >> qpat_x_assum ‘LENGTH (ep_roles [] evs) = _’ (SUBST1_TAC o GSYM) >>
            simp[EL_LENGTH_APPEND]) >>
      Cases_on ‘x1’ >> fs[new_chans_def, ev_role_def, EL_LENGTH_APPEND] >>
      qpat_x_assum ‘ev_new _ = SOME _’ mp_tac >> simp[Abbr ‘ev’] >> strip_tac >>
      drule ev_new_INR >> strip_tac >> qpat_x_assum ‘nm = _’ SUBST_ALL_TAC >>
      fs[unblock_other] >>
      drule_all accept_new_chan >> strip_tac >>
      rename1 ‘FILTER _ _ = (l1, p1, pop_chan _ y :: q1) :: _’ >>
      ‘MEM (l1, p1, pop_chan w y :: q1) (FILTER (λ(l', p, q). l' = y) w.listeners)’ by simp[] >>
      ‘l1 = y ∧ MEM (y, p1, pop_chan w y :: q1) w.listeners’
        by (qpat_x_assum ‘MEM _ (FILTER _ _)’ mp_tac >> rewrite_tac[MEM_FILTER] >>
            simp_tac (srw_ss()) [] >> strip_tac >> qpat_x_assum ‘l1 = y’ SUBST_ALL_TAC >>
            asm_rewrite_tac[]) >>
      qpat_x_assum ‘MEM _ (FILTER _ _)’ kall_tac >>
      ‘ALOOKUP (lsn evs) y = SOME p1’
        by (qpat_x_assum ‘pinv evs _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
            first_x_assum drule >> simp[]) >>
      ‘p = p1’
        by (qpat_x_assum ‘(case ALOOKUP _ _ of NONE => _ | SOME _ => _) = _’ mp_tac >>
            qpat_x_assum ‘ALOOKUP _ _ = SOME p1’ (fn th => rewrite_tac[th]) >>
            simp_tac (srw_ss()) [] >> DISCH_THEN SUBST_ALL_TAC >>
            qpat_x_assum ‘p = _’ ACCEPT_TAC) >>
      qpat_x_assum ‘p = p1’ SUBST_ALL_TAC >>
      qpat_x_assum ‘i1 _ _ _’ mp_tac >> rewrite_tac[i1_def] >>
      disch_then (qspecl_then [‘k’, ‘y’, ‘p1’, ‘pop_chan w y :: q1’, ‘pop_chan w y’] mp_tac) >>
      simp[Abbr ‘w’]) >>
  ‘proc_events k0 (rs ++ [Call k nm conf bys out]) = proc_events k0 rs’
    by simp[proc_events_SNOC] >>
  ‘call_css s k nm conf bys out css k0 = css k0’ by simp[call_css_def, APPLY_UPDATE_THM] >>
  fs[] >> qpat_x_assum ‘i2 _ _ _ _ _’ mp_tac >> rewrite_tac[i2_def] >>
  disch_then irule >> simp[] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* zinv and oinv *)

Definition fd0_ok_def:
  fd0_ok G ⇔ fdok_first G ∧ no_close0 G ∨ no_conn G
End

Theorem fd0_safe_ok:
  fd0_safe G ⇔ fd0_ok G
Proof
  simp[fd0_safe_def, fd0_ok_def, fdok_first_def, no_close0_def, no_conn_def]
QED

Theorem zo_fields[simp]:
  (zo RS rs (s with moved := X1) css ⇔ zo RS rs s css) ∧
  (zo RS rs (s with acked := X2) css ⇔ zo RS rs s css) ∧
  (zo RS rs (s with finned := X3) css ⇔ zo RS rs s css) ∧
  (zo RS rs (s with alive := X4) css ⇔ zo RS rs s css) ∧
  (zo RS rs (s with target := X5) css ⇔ zo RS rs s css) ∧
  (zo RS rs (s with peer := X6) css ⇔ zo RS rs s css)
Proof
  simp[zo_def]
QED

Theorem zo_other:
  (∀k nm conf bys out. r ≠ Call k nm conf bys out) ⇒
  (zo RS (rs ++ [r]) s css ⇔ zo RS rs s css)
Proof
  simp[zo_def, proc_events_other]
QED

Theorem zo_deliver:
  zo RS rs s css ∧ k < LENGTH s.procs ⇒ zo RS rs (sys_deliver k a s) css
Proof
  rw[zo_def, sys_deliver_def, EL_LUPDATE] >> rw[zinv_deliver, oinv_deliver]
QED

Theorem zo_exit:
  zo RS rs s css ∧ k < LENGTH s.procs ⇒
  zo RS rs (s with procs := LUPDATE (close_all (EL k s.procs)) k s.procs) css
Proof
  rw[zo_def, EL_LUPDATE] >> rw[zinv_close_all, oinv_close_all]
QED

Theorem proc_events_SNOC_prefix:
  rs ++ [r] ≼ RS ⇒ proc_events k (rs ++ [r]) ≼ proc_events k RS
Proof
  rw[IS_PREFIX_APPEND] >> simp[proc_events_APPEND]
QED

Theorem zo_call:
  zo RS rs s css ∧ sinv rs s css ∧ k < LENGTH s.procs ∧ fd0_ok (proc_events k RS) ∧
  rs ++ [Call k nm conf bys out] ≼ RS ∧
  l0_call nm (unblock nm conf) bys (EL k s.procs) = SOME (FFIreturn out w1) ⇒
  zo RS (rs ++ [Call k nm conf bys out]) (call_state s k nm conf bys w1)
     (call_css s k nm conf bys out css)
Proof
  strip_tac >> rewrite_tac[zo_def] >> gen_tac >> strip_tac >>
  rename1 ‘k0 < _’ >>
  ‘k0 < LENGTH s.procs’ by fs[call_state_def] >>
  Cases_on ‘k0 = k’
  >- (qpat_x_assum ‘k0 = k’ SUBST_ALL_TAC >>
      qabbrev_tac ‘w = EL k s.procs’ >>
      qabbrev_tac ‘ev = IO_event (ExtCall nm) conf (ZIP (bys, out))’ >>
      ‘pk rs s css k’ by fs[sinv_def] >>
      ‘l0_rely w ∧ pinv (proc_events k rs) w (css k)’
        by (qpat_x_assum ‘pk rs s css k’ mp_tac >> simp[pk_def, Abbr ‘w’]) >>
      ‘fds_lt w’ by fs[pinv_def] >>
      ‘zinv (proc_events k RS) (proc_events k rs) w ∧ oinv w (css k)’
        by (qpat_x_assum ‘zo _ _ _ _’ mp_tac >> rewrite_tac[zo_def] >>
            disch_then drule >> simp[Abbr ‘w’]) >>
      ‘proc_events k (rs ++ [Call k nm conf bys out]) = proc_events k rs ++ [ev]’
        by simp[proc_events_SNOC, Abbr ‘ev’] >>
      ‘proc_events k rs ++ [ev] ≼ proc_events k RS’
        by metis_tac[proc_events_SNOC_prefix] >>
      ‘EL k (call_state s k nm conf bys w1).procs =
       w1 with <| clock := w.clock + 1; hist := w.hist ++ [(nm, conf, bys)] |>’
        by simp[call_state_def, EL_LUPDATE, Abbr ‘w’] >>
      ‘call_css s k nm conf bys out css k = css k ++ new_chans w ev’
        by simp[call_css_def, APPLY_UPDATE_THM, Abbr ‘w’, Abbr ‘ev’] >>
      asm_rewrite_tac[zinv_clock_hist, oinv_clock_hist] >> conj_tac
      >- (qunabbrev_tac ‘ev’ >> irule zinv_call >> rpt conj_tac
          >- (qpat_x_assum ‘fd0_ok _’ mp_tac >> rewrite_tac[fd0_ok_def])
          >- (qpat_x_assum ‘_ ≼ proc_events k RS’ ACCEPT_TAC) >>
          qexists_tac ‘w’ >> asm_rewrite_tac[]) >>
      irule oinv_call >> fs[zinv_def] >> metis_tac[]) >>
  ‘proc_events k0 (rs ++ [Call k nm conf bys out]) = proc_events k0 rs’
    by simp[proc_events_SNOC] >>
  ‘call_css s k nm conf bys out css k0 = css k0’ by simp[call_css_def, APPLY_UPDATE_THM] >>
  ‘EL k0 (call_state s k nm conf bys w1).procs = EL k0 s.procs’
    by simp[call_state_def, EL_LUPDATE] >>
  asm_rewrite_tac[] >> qpat_x_assum ‘zo _ _ _ _’ mp_tac >> rewrite_tac[zo_def] >>
  disch_then drule >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* One step: what isolation says of it, and a call's two outcomes *)

Definition iso_step_def:
  iso_step a b r (s : sysstate) ⇔
    (∀k p. r = Env (EIncoming k p) ⇒ p ≠ a ∧ p ≠ b) ∧
    (∀k x j. r = Env (EArrive k x) ∧ env_arrival_chan x = SOME j ⇒ ¬on_ab a b s (k, j))
End

Theorem isolated_iso_step:
  isolated a b rs ss ∧ i < LENGTH rs ⇒ iso_step a b (EL i rs) (EL i ss)
Proof
  rewrite_tac[isolated_def, iso_step_def] >> strip_tac >>
  qpat_x_assum ‘∀i. _’ (qspec_then ‘i’ mp_tac) >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem call_step_cases:
  sys_step s (Call k nm conf bys out) s' ⇒
  k < LENGTH s.procs ∧
  ∃w1. l0_call nm (unblock nm conf) bys (EL k s.procs) = SOME (FFIreturn out w1) ∧
       (s' = call_state s k nm conf bys w1 ∨
        nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH (EL k s.procs).chans + 1 ∧
        ∃k'. sys_room (call_state s k nm conf bys w1) k' (w22n conf) ∧
             s' = sys_pair (k, LENGTH (EL k s.procs).chans) k' (w22n conf)
                    (call_state s k nm conf bys w1))
Proof
  rw[sys_step_def] >> qexists_tac ‘w1’ >> simp[] >>
  qpat_x_assum ‘if _ then _ else _’ mp_tac >>
  simp[call_state_def, call_target_def] >>
  rw[] >> fs[l0sysTheory.sysstate_component_equality] >> metis_tac[]
QED

Theorem sinv_lsn_distinct:
  sinv rs s css ∧ k < LENGTH s.procs ⇒ ALL_DISTINCT (MAP FST (EL k s.procs).listeners)
Proof
  rw[sinv_def] >> first_x_assum drule >> simp[pk_def, pinv_def]
QED

Theorem exit_state:
  s with <| alive := A; procs := P |> = (s with procs := P) with alive := A
Proof
  simp[l0sysTheory.sysstate_component_equality]
QED

(*---------------------------------------------------------------------------*)
(* I3 over a step *)

Theorem i3_call_state:
  i3 a b s ∧ sinv rs s css ∧ k < LENGTH s.procs ∧
  l0_call nm (unblock nm conf) bys (EL k s.procs) = SOME (FFIreturn out w1) ⇒
  i3 a b (call_state s k nm conf bys w1)
Proof
  strip_tac >>
  qabbrev_tac ‘w = EL k s.procs’ >>
  qabbrev_tac ‘w2 = w1 with <| clock := w.clock + 1; hist := w.hist ++ [(nm, conf, bys)] |>’ >>
  ‘l0_rely w’ by fs[sinv_def, pk_def, Abbr ‘w’] >>
  ‘wmono w w2’ by metis_tac[wmono_fields, wmono_call] >>
  ‘i3 a b (s with procs := LUPDATE w2 k s.procs)’ by (irule i3_local >> simp[Abbr ‘w’]) >>
  simp[call_state_def, call_target_def] >> IF_CASES_TAC
  >- (‘s with <| procs := LUPDATE w2 k s.procs;
                 target := ((k, LENGTH w.chans) =+ SOME (w22n conf)) s.target |> =
       (s with procs := LUPDATE w2 k s.procs) with
         target := ((k, LENGTH w.chans) =+ SOME (w22n conf))
                     (s with procs := LUPDATE w2 k s.procs).target’ by simp[] >>
      pop_assum SUBST1_TAC >> irule i3_target >> simp[] >>
      simp[sys_chan_def, EL_LUPDATE, Abbr ‘w2’] >> strip_tac >>
      irule connect_peer_sent >> fs[unblock_other] >> metis_tac[]) >>
  ‘s with <| procs := LUPDATE w2 k s.procs; target := s.target |> =
   s with procs := LUPDATE w2 k s.procs’ by simp[l0sysTheory.sysstate_component_equality] >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem i3_pair:
  i3 a b s ∧ k' < LENGTH s.procs ⇒ i3 a b (sys_pair e k' p s)
Proof
  strip_tac >> simp[sys_pair_def] >>
  qmatch_goalsub_abbrev_tac ‘s1 with peer := _’ >>
  ‘s1.peer = s.peer’ by simp[Abbr ‘s1’, sys_deliver_def] >>
  ‘i3 a b s1’ by (simp[Abbr ‘s1’] >> irule i3_deliver >> simp[]) >>
  qpat_x_assum ‘s1.peer = s.peer’ (fn th => rewrite_tac[GSYM th]) >>
  irule i3_peer >> first_assum ACCEPT_TAC
QED

Theorem i3_step:
  i3 a b s ∧ sinv rs s css ∧ iso_step a b r s ∧ sys_step s r s' ⇒ i3 a b s'
Proof
  strip_tac >> ‘kinv s’ by fs[sinv_def] >>
  Cases_on ‘r’
  >- (rename1 ‘Call k nm conf bys out’ >> drule call_step_cases >> rpt strip_tac >>
      ‘i3 a b (call_state s k nm conf bys w1)’ by (irule i3_call_state >> metis_tac[]) >>
      rveq >> TRY (first_assum ACCEPT_TAC) >> irule i3_pair >> fs[sys_room_def])
  >- (rename1 ‘Kern ks’ >> Cases_on ‘ks’ >> fs[sys_step_def] >> rveq
      >- (irule i3_pair >> fs[sys_room_def] >> irule i3_deliver >> fs[is_end_def])
      >- (rename1 ‘s.peer (k, j) = SOME (k', j')’ >>
          ‘s.peer (k', j') = SOME (k, j) ∧ is_end s (k', j')’
            by (qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> metis_tac[]) >>
          simp[] >> irule i3_deliver >> fs[is_end_def])
      >- (simp[] >> irule i3_deliver >> fs[is_end_def])
      >- (rename1 ‘s.peer (k, j) = SOME (k', j')’ >>
          ‘is_end s (k', j')’
            by (qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> metis_tac[]) >>
          simp[] >> irule i3_deliver >> fs[is_end_def])
      >> irule i3_deliver >> fs[is_end_def])
  >- (rename1 ‘Env es’ >> Cases_on ‘es’ >> fs[sys_step_def] >> rveq >>
      irule i3_deliver >> fs[is_end_def, sys_room_def] >>
      qx_genl_tac [‘j1’, ‘bs’] >> rpt strip_tac >>
      qpat_x_assum ‘iso_step _ _ _ _’ mp_tac >> rewrite_tac[iso_step_def] >>
      disch_then (qspecl_then [‘n’, ‘l’, ‘j1’] mp_tac o CONJUNCT2) >>
      fs[env_arrival_chan_def]) >>
  fs[sys_step_def] >> rveq >>
  ‘i3 a b (s with procs := LUPDATE (close_all (EL n s.procs)) n s.procs)’
    by (irule i3_local >> simp[wmono_close_all]) >>
  pop_assum mp_tac >> rewrite_tac[i3_def, on_ab_def] >> strip_tac >> gen_tac >>
  PairCases_on ‘e’ >> pop_assum (qspec_then ‘(e0, e1)’ mp_tac) >>
  simp[is_end_def, sys_chan_def]
QED

(*---------------------------------------------------------------------------*)
(* I1 over a step *)

Theorem i1_call_state:
  i1 a b s ∧ k < LENGTH s.procs ∧
  l0_call nm (unblock nm conf) bys (EL k s.procs) = SOME (FFIreturn out w1) ⇒
  i1 a b (call_state s k nm conf bys w1)
Proof
  strip_tac >>
  ‘i1 a b (s with procs := LUPDATE (w1 with <| clock := (EL k s.procs).clock + 1;
                                               hist := (EL k s.procs).hist ++ [(nm, conf, bys)] |>)
                                   k s.procs)’
    by (irule i1_local >> simp[] >> irule (cj 4 lsub_fields) >> metis_tac[lsub_call]) >>
  pop_assum mp_tac >> simp[call_state_def, i1_def]
QED

Theorem i1_step:
  i1 a b s ∧ sinv rs s css ∧ iso_step a b r s ∧ sys_step s r s' ⇒ i1 a b s'
Proof
  strip_tac >> ‘kinv s’ by fs[sinv_def] >>
  Cases_on ‘r’
  >- (rename1 ‘Call k nm conf bys out’ >> drule call_step_cases >> rpt strip_tac >>
      ‘i1 a b (call_state s k nm conf bys w1)’ by (irule i1_call_state >> metis_tac[]) >>
      rveq >> TRY (first_assum ACCEPT_TAC) >> irule i1_pair >> simp[] >>
      ‘sinv (rs ++ [Call k «sys_connect» conf bys out])
            (call_state s k «sys_connect» conf bys w1)
            (call_css s k «sys_connect» conf bys out css)’ by (irule sinv_call >> simp[]) >>
      drule sinv_lsn_distinct >> disch_then irule >> fs[sys_room_def])
  >- (rename1 ‘Kern ks’ >> Cases_on ‘ks’ >> fs[sys_step_def] >> rveq
      >- (rename1 ‘Handshake k j k'’ >>
          ‘k < LENGTH s.procs ∧ k' < LENGTH s.procs’ by fs[is_end_def, sys_room_def] >>
          ‘i1 a b (sys_deliver k (LConnUp j) s)’ by (irule i1_deliver >> simp[]) >>
          ‘ALL_DISTINCT (MAP FST (EL k' (sys_deliver k (LConnUp j) s).procs).listeners)’
            by (simp[sys_deliver_def, EL_LUPDATE] >> rw[conn_up_fields] >>
                irule sinv_lsn_distinct >> metis_tac[]) >>
          ‘sys_room (sys_deliver k (LConnUp j) s) k' p’
            by (qpat_x_assum ‘sys_room _ _ _’ mp_tac >>
                simp[sys_room_def, sys_deliver_def, EL_LUPDATE] >>
                Cases_on ‘k' = k’ >> simp[conn_up_fields]) >>
          irule i1_pair >> simp[])
      >- (rename1 ‘s.peer (k, j) = SOME (k', j')’ >>
          ‘is_end s (k', j')’
            by (qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> metis_tac[]) >>
          simp[] >> irule i1_deliver >> fs[is_end_def])
      >- (simp[] >> irule i1_deliver >> fs[is_end_def])
      >- (rename1 ‘s.peer (k, j) = SOME (k', j')’ >>
          ‘is_end s (k', j')’
            by (qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> metis_tac[]) >>
          simp[] >> irule i1_deliver >> fs[is_end_def])
      >> irule i1_deliver >> fs[is_end_def])
  >- (rename1 ‘Env es’ >> Cases_on ‘es’ >> fs[sys_step_def] >> rveq
      >- (irule i1_incoming >> fs[iso_step_def] >> irule sinv_lsn_distinct >>
          fs[sys_room_def] >> metis_tac[])
      >- (irule i1_deliver >> fs[is_end_def]) >>
      irule i1_deliver >> fs[is_end_def] >> rpt strip_tac >> fs[env_arrival_chan_def]) >>
  fs[sys_step_def] >> rveq >>
  ‘i1 a b (s with procs := LUPDATE (close_all (EL n s.procs)) n s.procs)’
    by (irule i1_local >> simp[lsub_close_all]) >>
  pop_assum mp_tac >> simp[i1_def]
QED

(*---------------------------------------------------------------------------*)
(* I2 over a step: from a call's own state, pairs persist *)

Theorem i2_step:
  i2 a b rs s css ∧ i1 a b s ∧ sinv rs s css ∧ sys_step s r s' ⇒
  i2 a b (rs ++ [r]) s' (step_css s r css)
Proof
  strip_tac >> drule_all sys_ext_step >> strip_tac >>
  ‘LENGTH s'.procs = LENGTH s.procs ∧ ∀e e'. s.peer e = SOME e' ⇒ s'.peer e = SOME e'’
    by fs[sys_ext_def] >>
  Cases_on ‘r’
  >- (rename1 ‘Call k nm conf bys out’ >> drule call_step_cases >>
      disch_then (CONJUNCTS_THEN2 assume_tac
                   (qx_choose_then ‘w1’ (CONJUNCTS_THEN2 assume_tac kall_tac))) >>
      ‘i2 a b (rs ++ [Call k nm conf bys out]) (call_state s k nm conf bys w1)
          (call_css s k nm conf bys out css)’ by (irule i2_call >> simp[]) >>
      simp[step_css_def] >> irule i2_mono >>
      qexists_tac ‘call_state s k nm conf bys w1’ >> simp[] >> simp[call_state_def]) >>
  simp[step_css_def, i2_other] >> irule i2_mono >> qexists_tac ‘s’ >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* zo over a step *)

Theorem zo_pair:
  zo RS rs s css ∧ k' < LENGTH s.procs ⇒ zo RS rs (sys_pair e k' p s) css
Proof
  strip_tac >> simp[sys_pair_def] >> irule zo_deliver >> simp[]
QED

Theorem zo_step:
  zo RS rs s css ∧ sinv rs s css ∧ sys_step s r s' ∧ rs ++ [r] ≼ RS ∧
  (∀k nm conf bys out. r = Call k nm conf bys out ⇒ fd0_ok (proc_events k RS)) ⇒
  zo RS (rs ++ [r]) s' (step_css s r css)
Proof
  strip_tac >> ‘kinv s’ by fs[sinv_def] >>
  Cases_on ‘r’
  >- (rename1 ‘Call k nm conf bys out’ >> drule call_step_cases >> rpt strip_tac >>
      ‘zo RS (rs ++ [Call k nm conf bys out]) (call_state s k nm conf bys w1)
          (call_css s k nm conf bys out css)’ by (irule zo_call >> fs[]) >>
      rveq >> simp[step_css_def] >> TRY (first_assum ACCEPT_TAC) >>
      irule zo_pair >> fs[sys_room_def])
  >- (rename1 ‘Kern ks’ >> simp[step_css_def, zo_other] >>
      Cases_on ‘ks’ >> fs[sys_step_def] >> rveq
      >- (irule zo_pair >> fs[sys_room_def] >> irule zo_deliver >> fs[is_end_def])
      >- (rename1 ‘s.peer (k, j) = SOME (k', j')’ >>
          ‘is_end s (k', j')’
            by (qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> metis_tac[]) >>
          simp[] >> irule zo_deliver >> fs[is_end_def])
      >- (simp[] >> irule zo_deliver >> fs[is_end_def])
      >- (rename1 ‘s.peer (k, j) = SOME (k', j')’ >>
          ‘is_end s (k', j')’
            by (qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> metis_tac[]) >>
          simp[] >> irule zo_deliver >> fs[is_end_def])
      >> irule zo_deliver >> fs[is_end_def])
  >- (rename1 ‘Env es’ >> simp[step_css_def, zo_other] >>
      Cases_on ‘es’ >> fs[sys_step_def] >> rveq >>
      irule zo_deliver >> fs[is_end_def, sys_room_def]) >>
  simp[step_css_def, zo_other] >> fs[sys_step_def] >> rveq >>
  ‘zo RS rs (s with procs := LUPDATE (close_all (EL n s.procs)) n s.procs) css’
    by (irule zo_exit >> simp[]) >>
  pop_assum mp_tac >> simp[zo_def]
QED

(*---------------------------------------------------------------------------*)
(* All four, along a run *)

Definition binv_def:
  binv a b RS rs s css ⇔ i3 a b s ∧ i1 a b s ∧ i2 a b rs s css ∧ zo RS rs s css
End

Theorem binv_step:
  binv a b RS rs s css ∧ sinv rs s css ∧ iso_step a b r s ∧ sys_step s r s' ∧ rs ++ [r] ≼ RS ∧
  (∀k nm conf bys out. r = Call k nm conf bys out ⇒ fd0_ok (proc_events k RS)) ⇒
  binv a b RS (rs ++ [r]) s' (step_css s r css)
Proof
  rewrite_tac[binv_def] >> strip_tac >> rpt conj_tac
  >- (irule i3_step >> metis_tac[])
  >- (irule i1_step >> metis_tac[])
  >- (irule i2_step >> simp[]) >>
  irule zo_step >> simp[]
QED

Theorem binv_init:
  sys_init ps s0 ⇒ binv a b RS [] s0 (K [])
Proof
  strip_tac >> rewrite_tac[binv_def] >> rpt conj_tac
  >- (‘s0.target = K NONE’ by fs[sys_init_def] >> simp[i3_def, on_ab_def])
  >- (rw[i1_def] >> ‘k < LENGTH ps’ by fs[sys_init_def] >>
      qpat_x_assum ‘sys_init _ _’ mp_tac >> rewrite_tac[sys_init_def] >>
      strip_tac >> qpat_x_assum ‘∀k. k < LENGTH ps ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[LET_THM] >>
      strip_tac >> fs[])
  >- simp[i2_def] >>
  rw[zo_def, zinv_def, oinv_def, proc_events_def] >>
  ‘k < LENGTH ps’ by fs[sys_init_def] >>
  qpat_x_assum ‘sys_init _ _’ mp_tac >> rewrite_tac[sys_init_def] >>
  strip_tac >> qpat_x_assum ‘∀k. k < LENGTH ps ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[LET_THM] >>
  strip_tac >> fs[]
QED

Theorem binv_run:
  sys_init ps s0 ∧ sys_steps s0 RS ss ∧ isolated a b RS ss ∧
  (∀k. k < LENGTH ps ⇒ fd0_ok (proc_events k RS)) ⇒
  ∀t. t ≤ LENGTH RS ⇒
      LENGTH (EL t ss).procs = LENGTH ps ∧
      binv a b RS (TAKE t RS) (EL t ss) (ghost ss RS (K []) t)
Proof
  strip_tac >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  ‘∀t. t ≤ LENGTH RS ⇒ sinv (TAKE t RS) (EL t ss) (ghost ss RS (K []) t)’
    by (match_mp_tac sinv_run >> simp[]) >>
  drule sys_steps_EL >> strip_tac >>
  Induct
  >- (strip_tac >> ‘EL 0 ss = s0’ by (Cases_on ‘ss’ >> fs[]) >>
      simp[ghost_def] >> conj_tac >- fs[sys_init_def] >>
      irule binv_init >> metis_tac[]) >>
  strip_tac >> ‘t < LENGTH RS’ by simp[] >>
  ‘LENGTH (EL t ss).procs = LENGTH ps ∧ binv a b RS (TAKE t RS) (EL t ss) (ghost ss RS (K []) t)’
    by (qpat_x_assum ‘t ≤ LENGTH RS ⇒ _’ irule >> simp[]) >>
  ‘sinv (TAKE t RS) (EL t ss) (ghost ss RS (K []) t)’
    by (qpat_x_assum ‘∀t. t ≤ LENGTH RS ⇒ sinv _ _ _’ irule >> simp[]) >>
  ‘sys_step (EL t ss) (EL t RS) (EL (t + 1) ss)’
    by (qpat_x_assum ‘∀t. t < LENGTH RS ⇒ sys_step _ _ _’ irule >> simp[]) >>
  ‘iso_step a b (EL t RS) (EL t ss)’ by (irule isolated_iso_step >> simp[]) >>
  simp[ghost_def, ADD1, TAKE_SUC_SNOC] >> conj_tac
  >- (drule_all sys_ext_step >> simp[sys_ext_def]) >>
  ‘TAKE t RS ++ [EL t RS] ≼ RS’ by metis_tac[TAKE_SUC_SNOC, TAKE_prefix_self] >>
  irule binv_step >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum ‘∀k. k < LENGTH ps ⇒ fd0_ok _’ irule >>
  qpat_x_assum ‘sys_step _ _ _’ mp_tac >> asm_rewrite_tac[sys_step_def] >>
  qpat_x_assum ‘LENGTH _ = LENGTH ps’ (fn th => rewrite_tac[th]) >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Quiet: at any instant, an episode on a or b that is unpaired at the end
   has heard nothing *)

Theorem kinv_peer_end:
  kinv s ∧ s.peer e = SOME e' ⇒ s.peer e' = SOME e ∧ is_end s e ∧ is_end s e'
Proof
  strip_tac >> qpat_x_assum ‘kinv s’ (strip_assume_tac o REWRITE_RULE [kinv_def]) >>
  qpat_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’ (qspecl_then [‘e’, ‘e'’] assume_tac) >>
  qpat_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’ (qspecl_then [‘e'’, ‘e’] assume_tac) >>
  metis_tac[]
QED

Theorem ep_fds_nz:
  ∀evs. EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs ⇒ EVERY (λf. f ≠ 0w) (ep_fds evs)
Proof
  Induct >> rw[ep_fds_def] >> fs[ep_fds_def] >>
  Cases_on ‘ev_new h’ >> simp[] >> rename1 ‘ev_new h = SOME x’ >> PairCases_on ‘x’ >>
  simp[] >> strip_tac >> fs[]
QED

Theorem run_no_fd0:
  sys_init ps s0 ∧ sys_steps s0 RS ss ∧ (∀k. k < LENGTH ps ⇒ fd0_ok (proc_events k RS)) ∧
  k < LENGTH ps ∧ j < LENGTH (ep_fds (proc_events k (TAKE t RS))) ⇒
  EL j (ep_fds (proc_events k (TAKE t RS))) ≠ 0w ∧ EL j (ep_fds (proc_events k RS)) ≠ 0w
Proof
  strip_tac >>
  ‘EVERY (λf. f ≠ 0w) (ep_fds (proc_events k RS))’
    by (irule ep_fds_nz >> irule fd0_safe_no_ev0 >> rewrite_tac[GSYM fd0_ok_def] >>
        metis_tac[]) >>
  ‘EL j (ep_fds (proc_events k (TAKE t RS))) = EL j (ep_fds (proc_events k RS))’
    by (irule prefix_EL >> simp[ep_fds_TAKE]) >>
  ‘j < LENGTH (ep_fds (proc_events k RS))’
    by metis_tac[ep_fds_TAKE, IS_PREFIX_LENGTH, LESS_LESS_EQ_TRANS] >>
  fs[EVERY_EL]
QED

Theorem recvd_peer_sent:
  sinv rs st cst ∧ k < LENGTH st.procs ∧ j < LENGTH (cst k) ∧
  EL j (ep_fds (proc_events k rs)) ≠ 0w ⇒
  l0_ep_recvd j (proc_events k rs) ≼ (sys_chan st (k, EL j (cst k))).peer_sent
Proof
  strip_tac >>
  ‘pinv (proc_events k rs) (EL k st.procs) (cst k)’ by fs[sinv_def, pk_def] >>
  simp[l0_ep_recvd_def, sys_chan_def] >> irule in_ok_prefix >>
  qpat_x_assum ‘pinv _ _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]
QED

(* The peer is no episode: it has sent nothing *)
Theorem quiet_peer:
  ∀rs RS st cst e k' c'.
  sinv rs st cst ∧ zo RS rs st cst ∧ st.peer e = SOME (k', c') ∧ ¬MEM c' (cst k') ⇒
  (sys_chan st e).peer_sent = []
Proof
  rpt gen_tac >> strip_tac >> ‘kinv st’ by fs[sinv_def] >>
  drule_all kinv_peer_end >> strip_tac >>
  ‘(sys_chan st e).peer_sent ≼ TAKE (st.moved (k', c')) (sys_chan st (k', c')).sent’
    by (qpat_x_assum ‘kinv st’ (strip_assume_tac o REWRITE_RULE [kinv_def]) >>
        qpat_x_assum ‘∀e e'. st.peer e = SOME e' ⇒ _’ (qspecl_then [‘(k', c')’, ‘e’] mp_tac) >>
        asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]) >>
  ‘k' < LENGTH st.procs ∧ c' < LENGTH (EL k' st.procs).chans’ by fs[is_end_def] >>
  ‘oinv (EL k' st.procs) (cst k')’
    by (qpat_x_assum ‘zo _ _ _ _’ mp_tac >> rewrite_tac[zo_def] >>
        disch_then (qspec_then ‘k'’ mp_tac) >> asm_rewrite_tac[] >> strip_tac) >>
  ‘(sys_chan st (k', c')).sent = []’
    by (qpat_x_assum ‘oinv _ _’ mp_tac >> rewrite_tac[oinv_def, sys_chan_def] >>
        disch_then irule >> asm_rewrite_tac[]) >>
  fs[IS_PREFIX_NIL]
QED

(* No peer: an episode on a or b *)
Theorem quiet_none:
  ∀rs st cst a b k j.
  sinv rs st cst ∧ i3 a b st ∧ i2 a b rs st cst ∧ k < LENGTH st.procs ∧ j < LENGTH (cst k) ∧
  st.peer (k, EL j (cst k)) = NONE ∧
  MEM (EL j (ep_roles [] (proc_events k rs))) [Connected a; Connected b; Accepted a; Accepted b] ⇒
  (sys_chan st (k, EL j (cst k))).peer_sent = []
Proof
  rpt gen_tac >> strip_tac >>
  ‘pk rs st cst k’ by fs[sinv_def] >>
  ‘pinv (proc_events k rs) (EL k st.procs) (cst k)’ by fs[pk_def] >>
  ‘is_end st (k, EL j (cst k))’ by fs[pinv_def, EVERY_EL, is_end_def] >>
  Cases_on ‘EL j (ep_roles [] (proc_events k rs))’
  >- (rename1 ‘_ = Connected p’ >>
      ‘p = a ∨ p = b’ by (qpat_x_assum ‘MEM _ _’ mp_tac >> asm_rewrite_tac[] >> simp[]) >>
      ‘st.target (k, EL j (cst k)) = SOME p’
        by (qpat_x_assum ‘pk _ _ _ _’ mp_tac >> rewrite_tac[pk_def] >>
            simp_tac std_ss [LET_THM] >> strip_tac >>
            qpat_x_assum ‘∀j p. j < LENGTH (cst k) ∧ _ = Connected p ⇒ _’
              (qspecl_then [‘j’, ‘p’] mp_tac) >> asm_rewrite_tac[]) >>
      ‘on_ab a b st (k, EL j (cst k))’ by (rewrite_tac[on_ab_def] >> metis_tac[]) >>
      qpat_x_assum ‘i3 _ _ _’ mp_tac >> rewrite_tac[i3_def] >> disch_then irule >>
      asm_rewrite_tac[]) >>
  rename1 ‘_ = Accepted p’ >>
  ‘p = a ∨ p = b’ by (qpat_x_assum ‘MEM _ _’ mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum ‘i2 _ _ _ _ _’ mp_tac >> rewrite_tac[i2_def] >>
  disch_then (qspecl_then [‘k’, ‘j’, ‘p’] mp_tac) >> asm_rewrite_tac[]
QED

(* A peer that is an episode: the two are paired at the end *)
Theorem quiet_fin_pair:
  ∀st cst sf csf RS k k' j j'.
  hist_inv st cst sf csf ∧ k < LENGTH st.procs ∧ k' < LENGTH st.procs ∧
  j < LENGTH (cst k) ∧ j' < LENGTH (cst k') ∧
  st.peer (k, EL j (cst k)) = SOME (k', EL j' (cst k')) ∧
  EL j (ep_fds (proc_events k RS)) ≠ 0w ∧ EL j' (ep_fds (proc_events k' RS)) ≠ 0w ⇒
  fin_pair RS sf csf (k, j) (k', j')
Proof
  rpt gen_tac >> strip_tac >> ‘cst k ≼ csf k ∧ cst k' ≼ csf k'’ by fs[hist_inv_def] >>
  ‘EL j (cst k) = EL j (csf k) ∧ EL j' (cst k') = EL j' (csf k')’ by metis_tac[prefix_EL] >>
  ‘LENGTH (cst k) ≤ LENGTH (csf k) ∧ LENGTH (cst k') ≤ LENGTH (csf k')’
    by metis_tac[IS_PREFIX_LENGTH] >>
  ‘LENGTH sf.procs = LENGTH st.procs’ by fs[hist_inv_def] >>
  ‘sf.peer (k, EL j (cst k)) = SOME (k', EL j' (cst k'))’
    by (qpat_x_assum ‘hist_inv _ _ _ _’ mp_tac >> rewrite_tac[hist_inv_def] >> strip_tac >>
        qpat_x_assum ‘∀e e'. st.peer e = SOME e' ⇒ sf.peer e = SOME e'’ irule >>
        first_assum ACCEPT_TAC) >>
  rewrite_tac[fin_pair_def] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, decide_tac, metis_tac[]]
QED

(* A process outside the system makes no call *)
Theorem proc_events_out:
  sys_steps s0 RS ss ∧ (∀t. t ≤ LENGTH RS ⇒ LENGTH (EL t ss).procs = n) ∧ n ≤ k ⇒
  ∀t. proc_events k (TAKE t RS) = []
Proof
  strip_tac >> drule sys_steps_EL >> strip_tac >> Induct >- simp[proc_events_def] >>
  Cases_on ‘t < LENGTH RS’
  >- (simp[ADD1, TAKE_SUC_SNOC, proc_events_APPEND] >>
      ‘LENGTH (EL t ss).procs = n’
        by (qpat_x_assum ‘∀t. t ≤ LENGTH RS ⇒ LENGTH _ = n’ (qspec_then ‘t’ mp_tac) >> simp[]) >>
      qpat_x_assum ‘∀t. t < LENGTH RS ⇒ sys_step _ _ _’ (qspec_then ‘t’ mp_tac) >>
      asm_rewrite_tac[] >>
      Cases_on ‘EL t RS’ >> simp[proc_events_def, sys_step_def] >> rw[] >> fs[]) >>
  ‘LENGTH RS ≤ t ∧ LENGTH RS ≤ SUC t’ by simp[] >> fs[TAKE_LENGTH_TOO_LONG]
QED

Theorem quiet_at:
  ∀ps s0 ss RS a b t k j r.
  sys_init ps s0 ∧ sys_steps s0 RS ss ∧ isolated a b RS ss ∧
  (∀k. k < LENGTH ps ⇒ fd0_ok (proc_events k RS)) ∧ t ≤ LENGTH RS ∧ k < LENGTH ps ∧
  (∀e'. ¬fin_pair RS (EL (LENGTH RS) ss) (ghost ss RS (K []) (LENGTH RS)) (k, j) e') ∧
  l0_ep_role j (proc_events k RS) = SOME r ∧
  MEM r [Connected a; Connected b; Accepted a; Accepted b] ⇒
  l0_ep_recvd j (proc_events k (TAKE t RS)) = []
Proof
  rpt gen_tac >> strip_tac >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  ‘sinv (TAKE t RS) (EL t ss) (ghost ss RS (K []) t)’
    by (‘∀t. t ≤ LENGTH RS ⇒ sinv (TAKE t RS) (EL t ss) (ghost ss RS (K []) t)’
          by (match_mp_tac sinv_run >> simp[]) >>
        pop_assum (qspec_then ‘t’ mp_tac) >> asm_rewrite_tac[]) >>
  ‘LENGTH (EL t ss).procs = LENGTH ps ∧
   binv a b RS (TAKE t RS) (EL t ss) (ghost ss RS (K []) t)’
    by (qspecl_then [‘ps’, ‘s0’, ‘RS’, ‘ss’, ‘a’, ‘b’] mp_tac (Q.GENL [‘ps’, ‘s0’, ‘RS’, ‘ss’, ‘a’, ‘b’] binv_run) >>
        impl_tac >- asm_rewrite_tac[] >>
        disch_then (qspec_then ‘t’ mp_tac) >> asm_rewrite_tac[]) >>
  ‘hist_inv (EL t ss) (ghost ss RS (K []) t) (EL (LENGTH RS) ss) (ghost ss RS (K []) (LENGTH RS))’
    by (qspecl_then [‘s0’, ‘RS’, ‘ss’, ‘K []’, ‘t’] mp_tac (Q.GENL [‘s0’, ‘rs’, ‘ss’, ‘css0’, ‘t’] hist_run) >>
        impl_tac >- asm_rewrite_tac[] >>
        disch_then (qspec_then ‘LENGTH RS - t’ mp_tac) >>
        ‘t + (LENGTH RS - t) = LENGTH RS’ by simp[] >> pop_assum SUBST1_TAC >>
        rewrite_tac[LESS_EQ_REFL]) >>
  qabbrev_tac ‘st = EL t ss’ >> qabbrev_tac ‘cst = ghost ss RS (K []) t’ >>
  qabbrev_tac ‘sf = EL (LENGTH RS) ss’ >> qabbrev_tac ‘csf = ghost ss RS (K []) (LENGTH RS)’ >>
  qpat_x_assum ‘binv _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [binv_def]) >>
  ‘kinv st’ by fs[sinv_def] >>
  ‘k < LENGTH st.procs’ by decide_tac >>
  ‘pinv (proc_events k (TAKE t RS)) (EL k st.procs) (cst k)’
    by (qpat_x_assum ‘sinv _ _ _’ mp_tac >> rewrite_tac[sinv_def] >> strip_tac >>
        qpat_x_assum ‘∀k. k < LENGTH st.procs ⇒ _’ drule >> simp[pk_def]) >>
  ‘LENGTH (cst k) = LENGTH (ep_fds (proc_events k (TAKE t RS)))’ by fs[pinv_def] >>
  reverse (Cases_on ‘j < LENGTH (cst k)’)
  >- (rewrite_tac[l0_ep_recvd_def] >> irule ep_io_unborn >> decide_tac) >>
  ‘j < LENGTH (ep_fds (proc_events k (TAKE t RS)))’ by decide_tac >>
  drule_all run_no_fd0 >> strip_tac >>
  ‘l0_ep_recvd j (proc_events k (TAKE t RS)) ≼ (sys_chan st (k, EL j (cst k))).peer_sent’
    by (irule recvd_peer_sent >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘(sys_chan st (k, EL j (cst k))).peer_sent = []’
    suffices_by (disch_then (fn th => qpat_x_assum ‘_ ≼ _’ (mp_tac o REWRITE_RULE [th])) >>
                 rewrite_tac[IS_PREFIX_NIL]) >>
  (* the role at t is the final one *)
  ‘EL j (ep_roles [] (proc_events k (TAKE t RS))) = r’
    by (‘proc_events k RS = proc_events k (TAKE t RS) ++ proc_events k (DROP t RS)’
          by metis_tac[proc_events_APPEND, TAKE_DROP] >>
        ‘j < LENGTH (ep_roles [] (proc_events k (TAKE t RS)))’
          by metis_tac[LENGTH_ep_roles] >>
        qpat_x_assum ‘l0_ep_role j _ = SOME r’ mp_tac >>
        qpat_x_assum ‘proc_events k RS = _’ (fn th => rewrite_tac[th, l0_ep_role_def, ep_roles_APPEND]) >>
        IF_CASES_TAC >> simp[] >> disch_then (SUBST1_TAC o SYM) >> metis_tac[EL_APPEND1]) >>
  Cases_on ‘st.peer (k, EL j (cst k))’
  >- (qspecl_then [‘TAKE t RS’, ‘st’, ‘cst’, ‘a’, ‘b’, ‘k’, ‘j’] mp_tac quiet_none >>
      impl_tac >- asm_rewrite_tac[] >> rewrite_tac[]) >>
  rename1 ‘SOME e'’ >> PairCases_on ‘e'’ >>
  reverse (Cases_on ‘MEM e'1 (cst e'0)’)
  >- (qspecl_then [‘TAKE t RS’, ‘RS’, ‘st’, ‘cst’, ‘(k, EL j (cst k))’, ‘e'0’, ‘e'1’] mp_tac
        quiet_peer >>
      impl_tac >- asm_rewrite_tac[] >> rewrite_tac[]) >>
  (* the peer is an episode: then the two are paired at the end *)
  ‘∃j'. j' < LENGTH (cst e'0) ∧ e'1 = EL j' (cst e'0)’ by metis_tac[MEM_EL] >>
  qpat_x_assum ‘e'1 = _’ SUBST_ALL_TAC >>
  ‘is_end st (e'0, EL j' (cst e'0))’ by (drule_all kinv_peer_end >> simp[]) >>
  ‘e'0 < LENGTH st.procs’ by fs[is_end_def] >>
  ‘e'0 < LENGTH ps’ by decide_tac >>
  ‘pinv (proc_events e'0 (TAKE t RS)) (EL e'0 st.procs) (cst e'0)’
    by (qpat_x_assum ‘sinv _ _ _’ mp_tac >> rewrite_tac[sinv_def] >> strip_tac >>
        qpat_x_assum ‘∀k. k < LENGTH st.procs ⇒ _’ drule >> simp[pk_def]) >>
  ‘j' < LENGTH (ep_fds (proc_events e'0 (TAKE t RS)))’ by fs[pinv_def] >>
  ‘EL j' (ep_fds (proc_events e'0 RS)) ≠ 0w’ by (drule_all run_no_fd0 >> simp[]) >>
  qspecl_then [‘st’, ‘cst’, ‘sf’, ‘csf’, ‘RS’, ‘k’, ‘e'0’, ‘j’, ‘j'’] mp_tac quiet_fin_pair >>
  impl_tac >- asm_rewrite_tac[] >>
  qpat_x_assum ‘∀e'. ¬fin_pair _ _ _ _ _’ (qspec_then ‘(e'0, j')’ mp_tac) >> disch_then (fn th => disch_then (CONTR_TAC o MP (NOT_ELIM th)))
QED

Theorem b2_iso_stmt_holds:
  b2_iso_stmt
Proof
  rewrite_tac[b2_iso_stmt_def, l0sys_iso_run_def] >> rpt gen_tac >> strip_tac >>
  rename1 ‘sys_init ps s0’ >>
  ‘∀k. k < LENGTH ps ⇒ fd0_ok (proc_events k rs)’
    by (rpt strip_tac >> rewrite_tac[GSYM fd0_safe_ok] >>
        qpat_x_assum ‘∀k. k < LENGTH ps ⇒ fd0_safe _’ drule >> rewrite_tac[]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ LENGTH (EL t ss).procs = LENGTH ps’
    by (qspecl_then [‘ps’, ‘s0’, ‘rs’, ‘ss’, ‘a’, ‘b’] mp_tac
          (Q.GENL [‘ps’, ‘s0’, ‘RS’, ‘ss’, ‘a’, ‘b’] binv_run) >>
        impl_tac >- asm_rewrite_tac[] >>
        rpt strip_tac >> first_x_assum drule >> strip_tac) >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  qabbrev_tac ‘sf = EL (LENGTH rs) ss’ >> qabbrev_tac ‘csf = ghost ss rs (K []) (LENGTH rs)’ >>
  ‘∀t. t ≤ LENGTH rs ⇒ sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t)’
    by (match_mp_tac sinv_run >> simp[]) >>
  ‘sinv rs sf csf’
    by (map_every qunabbrev_tac [‘sf’, ‘csf’] >> first_assum (qspec_then ‘LENGTH rs’ mp_tac) >>
        rewrite_tac[TAKE_LENGTH_ID, LESS_EQ_REFL]) >>
  ‘kinv sf’ by fs[sinv_def] >>
  ‘LENGTH sf.procs = LENGTH ps’
    by (qunabbrev_tac ‘sf’ >> first_assum irule >> rewrite_tac[LESS_EQ_REFL]) >>
  qexists_tac ‘λe. if ∃e'. fin_pair rs sf csf e e' then SOME (@e'. fin_pair rs sf csf e e')
                   else NONE’ >>
  ‘∀e e'. (if ∃e'. fin_pair rs sf csf e e' then SOME (@e'. fin_pair rs sf csf e e')
           else NONE) = SOME e' ⇔ fin_pair rs sf csf e e'’
    by (rpt gen_tac >> IF_CASES_TAC >> simp[]
        >- (SELECT_ELIM_TAC >> metis_tac[fin_pair_unique]) >>
        metis_tac[]) >>
  BETA_TAC >> rpt conj_tac
  >- (asm_rewrite_tac[] >> metis_tac[fin_pair_sym])
  >- (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      rpt conj_tac
      >- fs[fin_pair_def]
      >- fs[fin_pair_def]
      >- (irule fin_pair_roles >> metis_tac[]) >>
      gen_tac >> Cases_on ‘t ≤ LENGTH rs’
      >- (irule fin_pair_at >> fs[Abbr ‘sf’, Abbr ‘csf’] >> metis_tac[]) >>
      ‘TAKE t rs = TAKE (LENGTH rs) rs’ by simp[TAKE_LENGTH_TOO_LONG] >>
      pop_assum SUBST1_TAC >>
      irule fin_pair_at >> fs[Abbr ‘sf’, Abbr ‘csf’] >> metis_tac[]) >>
  (* the quiet part *)
  rewrite_tac[b2_quiet_ab_def] >> BETA_TAC >> rpt gen_tac >>
  IF_CASES_TAC >- rewrite_tac[NOT_SOME_NONE] >>
  strip_tac >>
  qpat_x_assum ‘¬∃e'. _’ (assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM]) >>
  reverse (Cases_on ‘k < LENGTH ps’)
  >- (‘proc_events k rs = []’
        by (qspecl_then [‘s0’, ‘rs’, ‘ss’, ‘LENGTH ps’, ‘k’] mp_tac
              (Q.GENL [‘s0’, ‘RS’, ‘ss’, ‘n’, ‘k’] proc_events_out) >>
            impl_tac >- (asm_rewrite_tac[] >> decide_tac) >>
            disch_then (qspec_then ‘LENGTH rs’ mp_tac) >> rewrite_tac[TAKE_LENGTH_ID]) >>
      qpat_x_assum ‘l0_ep_role _ _ = SOME _’ mp_tac >>
      asm_rewrite_tac[] >> simp[l0_ep_role_def, ep_roles_def]) >>
  map_every qunabbrev_tac [‘sf’, ‘csf’] >>
  Cases_on ‘t ≤ LENGTH rs’
  >- (qspecl_then [‘ps’, ‘s0’, ‘ss’, ‘rs’, ‘a’, ‘b’, ‘t’, ‘k’, ‘j’, ‘r’] mp_tac quiet_at >>
      impl_tac >- asm_rewrite_tac[] >> rewrite_tac[]) >>
  ‘TAKE t rs = TAKE (LENGTH rs) rs’ by simp[TAKE_LENGTH_TOO_LONG] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘ps’, ‘s0’, ‘ss’, ‘rs’, ‘a’, ‘b’, ‘LENGTH rs’, ‘k’, ‘j’, ‘r’] mp_tac quiet_at >>
  impl_tac >- asm_rewrite_tac[LESS_EQ_REFL] >> rewrite_tac[]
QED
