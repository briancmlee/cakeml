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
