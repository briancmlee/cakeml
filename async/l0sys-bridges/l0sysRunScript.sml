(*
  B2 across time: how one system step relates the states before and after
  it (sys_ext), and the system invariant along a whole run.
*)
Theory l0sysRun
Ancestors
  honestL0World honestL0Rely l0sys l0sysEpisodes l0sysInv l0sysInvCall l0sysMono
  l0sysCausal l0sysStep
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* One process's channels: none disappears, none starts connecting again,
   and no queue gains an old channel *)

Definition wext_def:
  wext (w : l0world) w' ⇔
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀c. c < LENGTH w.chans ∧ (EL c w'.chans).connecting ⇒ (EL c w.chans).connecting) ∧
    (∀c. c < LENGTH w.chans ∧ queued w' c ⇒ queued w c)
End

Theorem wext_refl[simp]:
  wext w w
Proof
  simp[wext_def]
QED

Theorem wext_trans:
  wext w1 w2 ∧ wext w2 w3 ⇒ wext w1 w3
Proof
  rw[wext_def] >> res_tac >> fs[] >> rpt strip_tac >>
  ‘c < LENGTH w2.chans’ by fs[] >> res_tac >> fs[]
QED

Theorem lsub_queued:
  lsub w w' ∧ queued w' c ⇒ queued w c
Proof
  rw[lsub_def, queued_def] >> metis_tac[]
QED

Theorem wext_wmono:
  wmono w w' ∧ lsub w w' ⇒ wext w w'
Proof
  rw[wext_def, wmono_def, cmono_def] >> metis_tac[lsub_queued]
QED

Theorem wext_deliver:
  wext w (l0_deliver w a)
Proof
  Cases_on ‘∃j bs. a = LData j bs’
  >- (fs[] >> rw[wext_def, deliver_data] >>
      TRY (drule queued_deliver >> simp[] >> NO_TAC) >> metis_tac[deliver_data]) >>
  ‘wmono w (l0_deliver w a)’ by (irule wmono_deliver >> metis_tac[]) >>
  fs[wext_def, wmono_def, cmono_def] >> rw[] >>
  TRY (drule queued_deliver >> simp[] >> NO_TAC) >> metis_tac[]
QED

Theorem wext_call:
  l0_rely w ∧ l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  wext w (w1 with <| clock := n; hist := h |>)
Proof
  strip_tac >> irule wext_wmono >> conj_tac
  >- (drule lsub_call >> simp[lsub_def]) >>
  metis_tac[wmono_fields, wmono_call]
QED

Theorem wext_close_all:
  wext w (close_all w)
Proof
  irule wext_wmono >> simp[wmono_close_all, lsub_close_all]
QED

(*---------------------------------------------------------------------------*)
(* The system: ends and pairs persist, and a new pair has a new end, its
   other end new too or an unpaired connecting end *)

Definition new_pair_def:
  new_pair s e e' ⇔
    ¬is_end s e ∧ (¬is_end s e' ∨ s.peer e' = NONE ∧ (sys_chan s e').connecting)
End

Definition sys_ext_def:
  sys_ext s s' ⇔
    LENGTH s'.procs = LENGTH s.procs ∧
    (∀k. k < LENGTH s.procs ⇒ wext (EL k s.procs) (EL k s'.procs)) ∧
    (∀e e'. s.peer e = SOME e' ⇒ s'.peer e = SOME e') ∧
    (∀e e'. s'.peer e = SOME e' ∧ s.peer e ≠ SOME e' ⇒ new_pair s e e' ∨ new_pair s e' e)
End

Theorem sys_ext_fields[simp]:
  (sys_ext s (s' with target := X1) ⇔ sys_ext s s') ∧
  (sys_ext s (s' with moved := X2) ⇔ sys_ext s s') ∧
  (sys_ext s (s' with acked := X3) ⇔ sys_ext s s') ∧
  (sys_ext s (s' with finned := X4) ⇔ sys_ext s s') ∧
  (sys_ext s (s' with alive := X5) ⇔ sys_ext s s')
Proof
  simp[sys_ext_def]
QED

Theorem sys_ext_local:
  k < LENGTH s.procs ∧ wext (EL k s.procs) w' ⇒ sys_ext s (s with procs := LUPDATE w' k s.procs)
Proof
  rw[sys_ext_def, EL_LUPDATE] >> rw[]
QED

Theorem sys_ext_deliver:
  k < LENGTH s.procs ⇒ sys_ext s (sys_deliver k a s)
Proof
  rw[sys_deliver_def] >> irule sys_ext_local >> simp[wext_deliver]
QED

Theorem is_end_ext:
  sys_ext s s' ∧ is_end s e ⇒ is_end s' e
Proof
  Cases_on ‘e’ >> rw[sys_ext_def, is_end_def] >> res_tac >> fs[wext_def]
QED

Theorem connecting_ext:
  sys_ext s s' ∧ is_end s e ∧ (sys_chan s' e).connecting ⇒ (sys_chan s e).connecting
Proof
  Cases_on ‘e’ >> rw[sys_ext_def, is_end_def, sys_chan_def] >> res_tac >> fs[wext_def]
QED

Theorem new_pair_ext:
  sys_ext s s1 ∧ s1.peer = s.peer ∧ new_pair s1 x y ⇒ new_pair s x y
Proof
  strip_tac >>
  ‘∀e. is_end s e ⇒ is_end s1 e’
    by (rpt strip_tac >> irule is_end_ext >> qexists_tac ‘s’ >> fs[]) >>
  ‘∀e. is_end s e ∧ (sys_chan s1 e).connecting ⇒ (sys_chan s e).connecting’
    by (rpt strip_tac >> irule connecting_ext >> fs[] >> qexists_tac ‘s1’ >> fs[]) >>
  ‘¬is_end s1 x’ by fs[new_pair_def] >>
  ‘¬is_end s x’ by (strip_tac >> res_tac) >>
  qpat_x_assum ‘s1.peer = s.peer’ (fn th => fs[th, new_pair_def]) >>
  Cases_on ‘is_end s y’ >> fs[] >> res_tac >> fs[]
QED

(* Two steps whose first changes no peer *)
Theorem sys_ext_trans:
  sys_ext s s1 ∧ s1.peer = s.peer ∧ sys_ext s1 s2 ⇒ sys_ext s s2
Proof
  strip_tac >> rewrite_tac[sys_ext_def] >> rpt conj_tac
  >- fs[sys_ext_def]
  >- (rpt strip_tac >> irule wext_trans >> qexists_tac ‘EL k s1.procs’ >>
      fs[sys_ext_def])
  >- (rpt strip_tac >> fs[sys_ext_def] >> first_x_assum irule >> fs[]) >>
  rpt strip_tac >>
  ‘new_pair s1 e e' ∨ new_pair s1 e' e’
    by (qpat_x_assum ‘sys_ext s1 s2’ mp_tac >> rewrite_tac[sys_ext_def] >> strip_tac >>
        first_x_assum irule >> fs[]) >>
  metis_tac[new_pair_ext]
QED

Theorem sys_ext_pair:
  kinv s ∧ sys_ext s s1 ∧ s1.peer = s.peer ∧ s.peer e = NONE ∧ is_end s1 e ∧
  (is_end s e ⇒ (sys_chan s e).connecting) ∧ k' < LENGTH s1.procs ⇒
  sys_ext s (sys_pair e k' p s1)
Proof
  strip_tac >>
  qabbrev_tac ‘s2 = sys_deliver k' (LIncoming p) s1’ >>
  qabbrev_tac ‘e' = (k', LENGTH (EL k' s1.procs).chans)’ >>
  ‘sys_ext s s2’
    by (irule sys_ext_trans >> qexists_tac ‘s1’ >> simp[Abbr ‘s2’] >>
        irule sys_ext_deliver >> simp[]) >>
  ‘¬is_end s1 e'’ by simp[Abbr ‘e'’, is_end_def] >>
  ‘¬is_end s e'’
    by (strip_tac >> ‘is_end s1 e'’ by (irule is_end_ext >> qexists_tac ‘s’ >> fs[]) >> fs[]) >>
  ‘s.peer e' = NONE’ by fs[kinv_def] >>
  ‘e ≠ e'’ by (strip_tac >> fs[]) >>
  simp[sys_pair_def] >> qpat_x_assum ‘sys_ext s s2’ mp_tac >>
  simp[sys_ext_def, Abbr ‘s2’] >> strip_tac >> rpt conj_tac
  >- (rw[APPLY_UPDATE_THM] >> fs[] >> strip_tac >> fs[])
  >- (rpt gen_tac >> rw[APPLY_UPDATE_THM] >> simp[new_pair_def] >> fs[] >>
      Cases_on ‘is_end s e’ >> fs[])
QED

Theorem sys_ext_call_state:
  k < LENGTH s.procs ∧ l0_rely (EL k s.procs) ∧
  l0_call nm (unblock nm conf) bytes (EL k s.procs) = SOME (FFIreturn out w1) ⇒
  sys_ext s (call_state s k nm conf bytes w1)
Proof
  strip_tac >>
  ‘call_state s k nm conf bytes w1 =
   (s with procs := LUPDATE (w1 with <| clock := (EL k s.procs).clock + 1;
                                        hist := (EL k s.procs).hist ++ [(nm, conf, bytes)] |>)
                            k s.procs) with target := call_target s k nm conf w1’
    by simp[call_state_def] >>
  pop_assum SUBST1_TAC >> simp[] >> irule sys_ext_local >> simp[] >>
  irule wext_call >> metis_tac[]
QED

Theorem sys_ext_step:
  sinv rs s css ∧ sys_step s r s' ⇒ sys_ext s s'
Proof
  strip_tac >> ‘kinv s’ by fs[sinv_def] >>
  Cases_on ‘r’ >> fs[sys_step_def]
  >- ((* Call *)
      rename1 ‘l0_call nm (unblock nm conf) bytes (EL k s.procs) = SOME (FFIreturn out w1)’ >>
      ‘l0_rely (EL k s.procs)’ by fs[sinv_def, pk_def] >>
      ‘sys_ext s (call_state s k nm conf bytes w1)’ by (irule sys_ext_call_state >> simp[]) >>
      qabbrev_tac ‘s2 = call_state s k nm conf bytes w1’ >>
      qabbrev_tac ‘n = LENGTH (EL k s.procs).chans’ >>
      ‘s' = s2 ∨
       LENGTH w1.chans = n + 1 ∧
       ∃k'. sys_room s2 k' (w22n conf) ∧ s' = sys_pair (k, n) k' (w22n conf) s2’
        by (qpat_x_assum ‘if _ then _ else _’ mp_tac >>
            simp[Abbr ‘s2’, call_state_def, call_target_def] >>
            rw[] >> fs[l0sysTheory.sysstate_component_equality] >> metis_tac[]) >>
      fs[] >> irule sys_ext_pair >>
      ‘¬is_end s (k, n)’ by simp[is_end_def, Abbr ‘n’] >>
      fs[sys_room_def] >>
      simp[Abbr ‘s2’, call_state_def, is_end_def, EL_LUPDATE] >> fs[kinv_def])
  >- ((* Kern *)
      rename1 ‘Kern ks’ >>
      ‘∀a b c d. s.peer (a, b) = SOME (c, d) ⇒ c < LENGTH s.procs’
        by (rpt strip_tac >> fs[kinv_def] >> res_tac >> res_tac >> fs[is_end_def]) >>
      Cases_on ‘ks’ >> fs[sys_step_def, is_end_def, sys_ext_deliver] >>
      TRY (irule sys_ext_deliver >> res_tac >> fs[] >> NO_TAC) >>
      (* Handshake *)
      irule sys_ext_pair >> fs[sys_room_def, sys_ext_deliver] >>
      ‘s.peer (n, n0) = NONE’
        by (Cases_on ‘s.peer (n, n0)’ >> simp[] >> fs[kinv_def] >> res_tac >> fs[]) >>
      simp[is_end_def, sys_deliver_def, EL_LUPDATE, conn_up_fields])
  >- ((* Env *)
      rename1 ‘Env es’ >> Cases_on ‘es’ >>
      fs[sys_step_def, is_end_def, sys_ext_deliver, sys_room_def]) >>
  (* Exit *)
  ‘s with <| procs := LUPDATE (close_all (EL n s.procs)) n s.procs; alive := (n =+ F) s.alive |> =
   (s with procs := LUPDATE (close_all (EL n s.procs)) n s.procs) with alive := (n =+ F) s.alive’
    by simp[] >>
  pop_assum SUBST1_TAC >> simp[] >> irule sys_ext_local >> simp[wext_close_all]
QED

(*---------------------------------------------------------------------------*)
(* The ghost episode channels: they only grow, and an old channel joins
   them only off a queue *)

Theorem step_css_prefix:
  css k ≼ step_css s r css k
Proof
  Cases_on ‘r’ >> rw[step_css_def, call_css_def, APPLY_UPDATE_THM]
QED

Theorem new_chans_queued:
  l0_rely w ∧ l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
  MEM c (new_chans w (IO_event (ExtCall nm) conf (ZIP (bytes, out)))) ∧ c < LENGTH w.chans ⇒
  queued w c
Proof
  rw[new_chans_def] >> every_case_tac >> fs[] >> rveq >>
  rename1 ‘ev_new _ = SOME (f, INR l)’ >>
  drule ev_new_INR >> strip_tac >> rveq >> fs[unblock_other] >>
  drule_all accept_new_chan >> strip_tac >>
  ‘MEM (l1, p, pop_chan w l :: q) (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
  pop_assum mp_tac >> rewrite_tac[MEM_FILTER] >> strip_tac >>
  simp[queued_def] >> metis_tac[MEM]
QED

Theorem step_css_queued:
  sinv rs s css ∧ sys_step s r s' ∧ MEM c (step_css s r css k) ∧
  c < LENGTH (EL k s.procs).chans ⇒
  MEM c (css k) ∨ queued (EL k s.procs) c
Proof
  Cases_on ‘r’ >> rw[step_css_def] >>
  rename1 ‘call_css s k0 nm conf bytes out css’ >>
  Cases_on ‘k = k0’ >> fs[call_css_def, APPLY_UPDATE_THM] >> rveq >>
  disj2_tac >> fs[sys_step_def] >> irule new_chans_queued >>
  fs[sinv_def, pk_def] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* A run: the states, the ghost episode channels, and the invariant at every
   instant *)

Theorem sys_steps_EL:
  ∀rs s ss. sys_steps s rs ss ⇒
    LENGTH ss = LENGTH rs + 1 ∧ HD ss = s ∧
    ∀t. t < LENGTH rs ⇒ sys_step (EL t ss) (EL t rs) (EL (t + 1) ss)
Proof
  Induct >> rw[sys_steps_def] >> res_tac >> fs[] >>
  Cases_on ‘t’ >- (Cases_on ‘ss'’ >> fs[]) >>
  fs[] >> res_tac >> fs[ADD_CLAUSES]
QED

Definition ghost_def:
  ghost ss rs css 0 = css ∧
  ghost ss rs css (SUC t) = step_css (EL t ss) (EL t rs) (ghost ss rs css t)
End

Theorem TAKE_SUC_SNOC:
  t < LENGTH rs ⇒ TAKE (t + 1) rs = TAKE t rs ++ [EL t rs]
Proof
  metis_tac[SNOC_EL_TAKE, SNOC_APPEND, ADD1]
QED

Theorem sinv_run:
  sys_steps s0 rs ss ∧ sinv [] s0 css0 ⇒
  ∀t. t ≤ LENGTH rs ⇒ sinv (TAKE t rs) (EL t ss) (ghost ss rs css0 t)
Proof
  strip_tac >> drule sys_steps_EL >> strip_tac >>
  Induct >- (simp[ghost_def] >> Cases_on ‘ss’ >> fs[]) >>
  strip_tac >> ‘t < LENGTH rs’ by simp[] >> fs[] >>
  simp[ghost_def, ADD1, TAKE_SUC_SNOC] >> irule sinv_step >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Two instants of a run, st (ghost cst) and a later s (ghost css): what a
   pair or a channel at s says about it at st *)

Definition hist_inv_def:
  hist_inv st cst s css ⇔
    LENGTH s.procs = LENGTH st.procs ∧ (∀k. cst k ≼ css k) ∧
    (∀e. is_end st e ⇒ is_end s e) ∧
    (∀e. is_end st e ∧ (sys_chan s e).connecting ⇒ (sys_chan st e).connecting) ∧
    (∀e e'. st.peer e = SOME e' ⇒ s.peer e = SOME e') ∧
    (∀e e'. s.peer e = SOME e' ∧ is_end st e ∧ is_end st e' ⇒ st.peer e = SOME e') ∧
    (∀e e'. s.peer e = SOME e' ∧ is_end st e' ∧ ¬is_end st e ⇒
            st.peer e' = NONE ∧ (sys_chan st e').connecting) ∧
    (∀k c. k < LENGTH st.procs ∧ c < LENGTH (EL k st.procs).chans ∧
           (MEM c (css k) ∨ queued (EL k s.procs) c) ⇒
           MEM c (cst k) ∨ queued (EL k st.procs) c)
End

Theorem hist_refl:
  kinv st ⇒ hist_inv st cst st cst
Proof
  rw[hist_inv_def] >> fs[kinv_def] >> res_tac
QED

Theorem hist_step:
  hist_inv st cst s css ∧ sinv rs s css ∧ sys_step s r s' ⇒
  hist_inv st cst s' (step_css s r css)
Proof
  strip_tac >> drule_all sys_ext_step >> strip_tac >>
  ‘∀e. is_end st e ⇒ is_end s e’ by fs[hist_inv_def] >>
  rewrite_tac[hist_inv_def] >> rpt conj_tac
  >- fs[sys_ext_def, hist_inv_def]
  >- (gen_tac >> irule IS_PREFIX_TRANS >> qexists_tac ‘css k’ >>
      fs[hist_inv_def, step_css_prefix])
  >- (rpt strip_tac >> irule is_end_ext >> metis_tac[])
  >- (rpt strip_tac >> ‘is_end s e’ by res_tac >>
      ‘(sys_chan s e).connecting’ by (irule connecting_ext >> fs[] >> metis_tac[]) >>
      fs[hist_inv_def])
  >- (rpt strip_tac >> fs[hist_inv_def, sys_ext_def])
  >- (rpt strip_tac >> ‘is_end s e ∧ is_end s e'’ by fs[] >>
      Cases_on ‘s.peer e = SOME e'’ >- fs[hist_inv_def] >>
      ‘new_pair s e e' ∨ new_pair s e' e’ by (fs[sys_ext_def] >> metis_tac[]) >>
      fs[new_pair_def])
  >- (rpt gen_tac >> strip_tac >> ‘is_end s e'’ by fs[] >>
      Cases_on ‘s.peer e = SOME e'’
      >- (qpat_x_assum ‘hist_inv _ _ _ _’ mp_tac >> rewrite_tac[hist_inv_def] >>
          metis_tac[]) >>
      ‘new_pair s e e' ∨ new_pair s e' e’ by (fs[sys_ext_def] >> metis_tac[]) >>
      fs[new_pair_def] >>
      ‘st.peer e' = NONE’
        by (Cases_on ‘st.peer e'’ >> simp[] >> fs[hist_inv_def] >> res_tac >> fs[]) >>
      fs[hist_inv_def]) >>
  rpt gen_tac >> strip_tac >>
  ‘is_end s (k, c)’ by (first_x_assum irule >> simp[is_end_def]) >>
  ‘k < LENGTH s.procs ∧ c < LENGTH (EL k s.procs).chans’ by fs[is_end_def] >>
  ‘MEM c (css k) ∨ queued (EL k s.procs) c’
    by (FIRST [drule_all step_css_queued >> simp[] >> NO_TAC,
               disj2_tac >> fs[sys_ext_def] >> res_tac >> fs[wext_def]]) >>
  fs[hist_inv_def]
QED

Theorem hist_run:
  sys_steps s0 rs ss ∧ sinv [] s0 css0 ∧ t ≤ LENGTH rs ⇒
  ∀d. t + d ≤ LENGTH rs ⇒
      hist_inv (EL t ss) (ghost ss rs css0 t) (EL (t + d) ss) (ghost ss rs css0 (t + d))
Proof
  strip_tac >>
  ‘∀t. t ≤ LENGTH rs ⇒ sinv (TAKE t rs) (EL t ss) (ghost ss rs css0 t)’
    by metis_tac[sinv_run] >>
  drule sys_steps_EL >> strip_tac >>
  Induct
  >- (simp[] >> irule hist_refl >> ‘sinv (TAKE t rs) (EL t ss) (ghost ss rs css0 t)’ by simp[] >>
      fs[sinv_def]) >>
  strip_tac >>
  ‘t + SUC d = SUC (t + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘sys_step (EL (t + d) ss) (EL (t + d) rs) (EL (SUC (t + d)) ss)’
    by (first_assum (qspec_then ‘t + d’ mp_tac) >> impl_tac >- fs[] >> rewrite_tac[ADD1]) >>
  ‘sinv (TAKE (t + d) rs) (EL (t + d) ss) (ghost ss rs css0 (t + d))’ by simp[] >>
  simp[ghost_def] >> irule hist_step >> fs[] >> qexists_tac ‘TAKE (t + d) rs’ >> fs[]
QED
