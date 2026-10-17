(*
  Moonshot liveness, N2's kernel fact: what a process's L0 world calls
  "in flight" on a channel is, for a channel with a peer in the system,
  exactly what the kernel has not yet acknowledged:
      inflight + acked = LENGTH sent
  (and, for any channel, inflight ≤ LENGTH sent).  A send adds the bytes
  it took to both sides; an Ack moves n from inflight to acked; nothing
  else touches either.  infl_inv holds along every l0sys run.
*)
Theory moonshotLiveInfl
Ancestors
  moonshotLiveDeliver moonshotLiveDrains l0sysFair l0sys l0sysCausal l0sysMono l0sysRun
  l0sysStep l0sysInvCall honestL0World
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* Channels: a call either leaves inflight and sent alone, or sends *)

Definition ikeep_def:
  ikeep (x : lchan) y ⇔
    (y.inflight = x.inflight ∧ y.sent = x.sent) ∨
    ∃d. y.sent = x.sent ++ d ∧ y.inflight = x.inflight + LENGTH d
End

Definition wikeep_def:
  wikeep (w : l0world) w' ⇔
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀c. c < LENGTH w.chans ⇒ ikeep (EL c w.chans) (EL c w'.chans)) ∧
    (∀c. LENGTH w.chans ≤ c ∧ c < LENGTH w'.chans ⇒
         (EL c w'.chans).inflight = LENGTH (EL c w'.chans).sent)
End

Theorem ikeep_refl[simp]:
  ikeep x x
Proof
  simp[ikeep_def]
QED

Theorem wikeep_refl[simp]:
  wikeep w w
Proof
  simp[wikeep_def]
QED

Theorem ikeep_alt:
  ikeep x y ⇔ ∃d. y.sent = x.sent ++ d ∧ y.inflight = x.inflight + LENGTH d
Proof
  rw[ikeep_def, EQ_IMP_THM] >> TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC) >> metis_tac[]
QED

Theorem ikeep_trans:
  ikeep x y ∧ ikeep y z ⇒ ikeep x z
Proof
  rw[ikeep_alt] >> qexists_tac ‘d ++ d'’ >> simp[]
QED

Theorem wikeep_trans:
  wikeep w1 w2 ∧ wikeep w2 w3 ⇒ wikeep w1 w3
Proof
  rw[wikeep_def]
  >- (irule ikeep_trans >> qexists_tac ‘EL c w2.chans’ >> simp[])
  >> Cases_on ‘c < LENGTH w2.chans’ >> simp[] >>
  ‘ikeep (EL c w2.chans) (EL c w3.chans)’ by simp[] >>
  ‘(EL c w2.chans).inflight = LENGTH (EL c w2.chans).sent’ by simp[] >>
  fs[ikeep_alt]
QED

Theorem wikeep_upd_same:
  j < LENGTH w.chans ∧ (g (EL j w.chans)).inflight = (EL j w.chans).inflight ∧
  (g (EL j w.chans)).sent = (EL j w.chans).sent ⇒
  wikeep w (upd_lchan j g w)
Proof
  rw[wikeep_def, upd_lchan_def, EL_LUPDATE] >> rw[ikeep_def]
QED

Theorem wikeep_upd_any:
  wikeep w w' ∧ (∀c. (g c).inflight = c.inflight ∧ (g c).sent = c.sent) ⇒
  wikeep w (upd_lchan j g w')
Proof
  rw[wikeep_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> fs[ikeep_def] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> rw[] >> simp[]
QED

Theorem wikeep_fields:
  wikeep w w' ⇒
  wikeep w (w' with open_fds := X) ∧ wikeep w (w' with listeners := L) ∧
  wikeep w (w' with <| clock := n; hist := h |>) ∧
  wikeep w (w' with <| listeners := L; open_fds := X |>)
Proof
  simp[wikeep_def]
QED

Theorem wikeep_breaks:
  ∀q w'. wikeep w w' ∧ LENGTH w'.chans = LENGTH w.chans ⇒
         wikeep w (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w' q)
Proof
  Induct >> rw[] >> first_x_assum irule >>
  rw[wikeep_def, upd_lchan_def, EL_LUPDATE] >> fs[wikeep_def] >> rw[] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> rw[break_lchan_def, ikeep_def] >> rw[] >> fs[]
QED

Theorem breaks_infl[local]:
  ∀q (w : l0world).
    LENGTH (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q).chans = LENGTH w.chans ∧
    ∀c. c < LENGTH w.chans ⇒
        (EL c (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q).chans).inflight =
        (EL c w.chans).inflight ∧
        (EL c (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q).chans).sent =
        (EL c w.chans).sent
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘upd_lchan h (break_lchan e k) w’ mp_tac) >>
  simp[upd_lchan_def, EL_LUPDATE] >> rw[] >> rw[break_lchan_def]
QED

Theorem close_fd_infl:
  LENGTH (close_fd f w).chans = LENGTH w.chans ∧
  ∀c. c < LENGTH w.chans ⇒
      (EL c (close_fd f w).chans).inflight = (EL c w.chans).inflight ∧
      (EL c (close_fd f w).chans).sent = (EL c w.chans).sent
Proof
  rw[close_fd_def] >> every_case_tac >> fs[upd_lchan_def, EL_LUPDATE, breaks_infl] >> rw[]
QED

Theorem wikeep_close_fd:
  wikeep w (close_fd f w)
Proof
  rw[wikeep_def, close_fd_infl, ikeep_def]
QED

Theorem close_all_infl:
  LENGTH (close_all w).chans = LENGTH w.chans ∧
  ∀c. c < LENGTH w.chans ⇒
      (EL c (close_all w).chans).inflight = (EL c w.chans).inflight ∧
      (EL c (close_all w).chans).sent = (EL c w.chans).sent
Proof
  simp[close_all_def] >>
  ‘∀fs (w : l0world). LENGTH (FOLDL (λw f. close_fd f w) w fs).chans = LENGTH w.chans ∧
       ∀c. c < LENGTH w.chans ⇒
           (EL c (FOLDL (λw f. close_fd f w) w fs).chans).inflight = (EL c w.chans).inflight ∧
           (EL c (FOLDL (λw f. close_fd f w) w fs).chans).sent = (EL c w.chans).sent’
    suffices_by simp[] >>
  Induct >> simp[] >> rpt gen_tac >> first_x_assum (qspec_then ‘close_fd h w’ mp_tac) >>
  simp[close_fd_infl]
QED

Theorem wikeep_close_all:
  wikeep w (close_all w)
Proof
  rw[wikeep_def, close_all_infl, ikeep_def]
QED

Theorem wikeep_recv:
  l0_recv f n w = (r, d, w') ⇒ wikeep w w'
Proof
  strip_tac >> drule l0_recv_cases >> rw[] >> rw[] >>
  irule wikeep_upd_same >> simp[] >> metis_tac[l0_chan_of_lt]
QED

Theorem wikeep_send:
  l0_send f bs w = (r, w') ⇒ wikeep w w'
Proof
  rw[l0_send_def, AllCaseEqs()] >> rw[] >>
  TRY (irule wikeep_upd_same >> simp[] >> metis_tac[l0_chan_of_lt] >> NO_TAC) >>
  rw[wikeep_def, upd_lchan_def, EL_LUPDATE] >> rw[ikeep_def] >>
  qexists_tac ‘TAKE (MIN (LENGTH bs) (w.ch.takes c w.hist (EL c w.chans).inflight (LENGTH bs))) bs’ >>
  simp[LENGTH_TAKE_EQ, MIN_DEF]
QED

Theorem wikeep_shutdown:
  l0_shutdown f w = (r, w') ⇒ wikeep w w'
Proof
  rw[l0_shutdown_def, AllCaseEqs()] >> rw[] >>
  irule wikeep_upd_same >> simp[] >> metis_tac[l0_chan_of_lt]
QED

Theorem wikeep_connerr:
  l0_connerr f w = (r, w') ⇒ wikeep w w'
Proof
  rw[l0_connerr_def, AllCaseEqs()] >> rw[] >>
  irule wikeep_upd_same >> simp[] >> metis_tac[l0_chan_of_lt]
QED

Theorem wikeep_connect:
  l0_connect p w = (r, v, w') ⇒ wikeep w w'
Proof
  strip_tac >> drule l0_connect_cases >> rw[] >> rw[] >>
  rw[wikeep_def, upd_lchan_def, EL_LUPDATE, EL_APPEND1, EL_APPEND2] >> rw[] >>
  fs[EL_APPEND1, EL_APPEND2, fresh_lchan_def] >>
  ‘c − LENGTH w.chans = 0’ by simp[] >> simp[]
QED

Theorem wikeep_close:
  l0_close f w = (r, w') ⇒ wikeep w w'
Proof
  rw[l0_close_def, AllCaseEqs()] >> rw[wikeep_close_fd]
QED

Theorem wikeep_accept:
  l0_accept l w = (r, w') ⇒ wikeep w w'
Proof
  strip_tac >> drule l0_accept_cases >> strip_tac >> gvs[wikeep_fields] >>
  TRY (irule wikeep_upd_any >> simp[wikeep_fields] >> rw[break_lchan_def] >> NO_TAC) >>
  simp[wikeep_def]
QED

Theorem wikeep_call:
  l0_call nm (unblock nm conf) (bs : word8 list) w = SOME (FFIreturn out w1) ⇒ wikeep w w1
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> imp_res_tac l0_call_poll_unblock >> gvs[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [
    gvs[l0_listen_def, AllCaseEqs(), wikeep_fields] >> NO_TAC,
    metis_tac[wikeep_recv, wikeep_send, wikeep_shutdown, wikeep_connerr, wikeep_connect,
              wikeep_close, wikeep_accept]]
QED

(* Arrivals other than a drain *)
Theorem wikeep_deliver:
  (∀j n. a ≠ LDrain j n) ⇒ wikeep w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  TRY (rw[wikeep_def, EL_APPEND1, EL_APPEND2] >> rw[EL_APPEND1, EL_APPEND2] >>
       fs[EL_APPEND1, EL_APPEND2, fresh_lchan_def] >>
       TRY (‘c − LENGTH w.chans = 0’ by simp[] >> simp[]) >> NO_TAC) >>
  irule wikeep_upd_any >> simp[break_lchan_def] >> rw[break_lchan_def]
QED

(*---------------------------------------------------------------------------*)
(* The system invariant *)

Definition infl_inv_def:
  infl_inv (s : sysstate) ⇔
    ∀e. is_end s e ⇒
        (sys_chan s e).inflight ≤ LENGTH (sys_chan s e).sent ∧
        (s.peer e ≠ NONE ⇒ (sys_chan s e).inflight + s.acked e = LENGTH (sys_chan s e).sent)
End

Definition sikeep_def:
  sikeep (s : sysstate) s' ⇔
    LENGTH s'.procs = LENGTH s.procs ∧
    (∀k. k < LENGTH s.procs ⇒ wikeep (EL k s.procs) (EL k s'.procs)) ∧
    s'.acked = s.acked
End

Theorem sikeep_end:
  sikeep s s' ∧ is_end s e ⇒ is_end s' e ∧ ikeep (sys_chan s e) (sys_chan s' e)
Proof
  Cases_on ‘e’ >> rw[sikeep_def, is_end_def, sys_chan_def] >> res_tac >> fs[wikeep_def]
QED

Theorem sikeep_new:
  sikeep s s' ∧ ¬is_end s e ∧ is_end s' e ⇒
  (sys_chan s' e).inflight = LENGTH (sys_chan s' e).sent
Proof
  Cases_on ‘e’ >> rw[sikeep_def, is_end_def, sys_chan_def] >> gvs[] >>
  first_x_assum (qspec_then ‘q’ mp_tac) >> simp[wikeep_def]
QED

Theorem sikeep_trans:
  sikeep s1 s2 ∧ sikeep s2 s3 ⇒ sikeep s1 s3
Proof
  rw[sikeep_def] >> irule wikeep_trans >> qexists_tac ‘EL k s2.procs’ >> simp[]
QED

Theorem sikeep_local:
  k < LENGTH s.procs ∧ wikeep (EL k s.procs) w' ⇒
  sikeep s (s with procs := LUPDATE w' k s.procs)
Proof
  rw[sikeep_def, EL_LUPDATE] >> rw[]
QED

Theorem sikeep_fields[simp]:
  (sikeep s (s' with target := X1) ⇔ sikeep s s') ∧ (sikeep s (s' with peer := X2) ⇔ sikeep s s') ∧
  (sikeep s (s' with moved := X3) ⇔ sikeep s s') ∧ (sikeep s (s' with finned := X4) ⇔ sikeep s s') ∧
  (sikeep s (s' with alive := X5) ⇔ sikeep s s')
Proof
  simp[sikeep_def]
QED

Theorem sikeep_deliver:
  k < LENGTH s.procs ∧ (∀j n. a ≠ LDrain j n) ⇒ sikeep s (sys_deliver k a s)
Proof
  rw[sys_deliver_def] >> irule sikeep_local >> simp[wikeep_deliver]
QED

Theorem sikeep_pair:
  k' < LENGTH s.procs ⇒ sikeep s (sys_pair e k' p s)
Proof
  rw[sys_pair_def] >> irule sikeep_deliver >> simp[]
QED

Theorem sikeep_with_procs:
  k < LENGTH s.procs ∧ wikeep (EL k s.procs) w ⇒
  sikeep s (s with <| procs := LUPDATE w k s.procs; target := T1 |>)
Proof
  strip_tac >> drule_all sikeep_local >> simp[sikeep_def]
QED

(* Steps that keep inflight and sent but for sends (which add to both) *)
Theorem infl_inv_sikeep:
  kinv s ∧ infl_inv s ∧ sikeep s s' ∧ sys_ext s s' ∧ (∀e. s.acked e ≤ s.moved e) ⇒ infl_inv s'
Proof
  strip_tac >> ‘s'.acked = s.acked’ by fs[sikeep_def] >>
  rewrite_tac[infl_inv_def] >> gen_tac >> strip_tac >> Cases_on ‘is_end s e’
  >- (drule_all sikeep_end >> rw[ikeep_alt] >> simp[]
      >- (qpat_x_assum ‘infl_inv s’ mp_tac >> rw[infl_inv_def] >> res_tac >> simp[]) >>
      Cases_on ‘s.peer e’
      >- ((* a connecting end paired now: it has sent nothing, nothing moved *)
          ‘∃e'. s'.peer e = SOME e'’ by (Cases_on ‘s'.peer e’ >> fs[]) >>
          ‘new_pair s e' e’ by
            (qpat_x_assum ‘sys_ext _ _’ mp_tac >> rw[sys_ext_def] >>
             first_x_assum (qspecl_then [‘e’, ‘e'’] mp_tac) >> simp[new_pair_def]) >>
          ‘(sys_chan s e).connecting’ by (qpat_x_assum ‘new_pair _ _ _’ mp_tac >> simp[new_pair_def]) >>
          qpat_x_assum ‘kinv s’ (fn th => mp_tac (CONJUNCT2 (CONJUNCT2 (REWRITE_RULE [kinv_def] th)))) >>
          disch_then (qspec_then ‘e’ mp_tac) >> simp[] >> strip_tac >>
          ‘(sys_chan s e).inflight ≤ LENGTH (sys_chan s e).sent’ by
            (qpat_x_assum ‘infl_inv s’ mp_tac >> rw[infl_inv_def]) >>
          gvs[] >> qpat_x_assum ‘∀e. s.acked e ≤ _’ (qspec_then ‘e’ mp_tac) >> simp[]) >>
      qpat_x_assum ‘infl_inv s’ mp_tac >> rw[infl_inv_def] >>
      first_x_assum (qspec_then ‘e’ mp_tac) >> simp[])
  >> (* a new end *)
  drule_all sikeep_new >> strip_tac >>
  ‘s.acked e ≤ s.moved e’ by simp[] >>
  ‘s.moved e = 0’ by (qpat_x_assum ‘kinv s’ mp_tac >> rw[kinv_def]) >> simp[]
QED

(* An acknowledgement arriving *)
Theorem drain_facts:
  k < LENGTH s.procs ⇒
  (∀e. is_end (sys_deliver k (LDrain j n) s) e ⇔ is_end s e) ∧
  ∀e. is_end s e ⇒
      (sys_chan (sys_deliver k (LDrain j n) s) e).sent = (sys_chan s e).sent ∧
      (sys_chan (sys_deliver k (LDrain j n) s) e).inflight =
      if e = (k, j) then (sys_chan s e).inflight − n else (sys_chan s e).inflight
Proof
  strip_tac >> conj_tac >> Cases >>
  rw[is_end_def, sys_chan_def, sys_deliver_def, EL_LUPDATE, l0_deliver_def, upd_lchan_def] >>
  gvs[EL_LUPDATE]
QED

Theorem infl_inv_drain:
  kinv s ∧ infl_inv s ∧ is_end s (k, j) ∧
  (s.peer (k, j) = NONE ∧ A = s.acked ∨
   s.peer (k, j) ≠ NONE ∧ s.acked (k, j) + n ≤ s.moved (k, j) ∧
   A = ((k, j) =+ s.acked (k, j) + n) s.acked) ⇒
  infl_inv ((sys_deliver k (LDrain j n) s) with acked := A)
Proof
  strip_tac >> ‘k < LENGTH s.procs’ by fs[is_end_def] >>
  qspecl_then [‘k’, ‘s’, ‘j’, ‘n’] mp_tac (Q.GENL [‘k’, ‘s’, ‘j’, ‘n’] drain_facts) >>
  simp[] >> strip_tac >>
  ‘s.peer (k, j) ≠ NONE ⇒ s.moved (k, j) ≤ LENGTH (sys_chan s (k, j)).sent’ by
    (strip_tac >> Cases_on ‘s.peer (k, j)’ >> fs[] >>
     qpat_x_assum ‘kinv s’ mp_tac >> rw[kinv_def] >> res_tac) >>
  qpat_x_assum ‘infl_inv s’ (strip_assume_tac o REWRITE_RULE [infl_inv_def]) >>
  rewrite_tac[infl_inv_def] >> gen_tac >> simp[] >> strip_tac >>
  qpat_x_assum ‘∀e. is_end s e ⇒ _ = _ ∧ _’ (qspec_then ‘e’ mp_tac) >>
  qpat_x_assum ‘∀e. is_end s e ⇒ _ ≤ _ ∧ _’ (qspec_then ‘e’ mp_tac) >>
  simp[] >> rpt strip_tac >> Cases_on ‘e = (k, j)’ >> gvs[combinTheory.APPLY_UPDATE_THM]
QED

(*---------------------------------------------------------------------------*)
(* infl_inv along a run *)

Theorem infl_inv_step:
  kinv s ∧ infl_inv s ∧ sys_ext s s' ∧ sys_step s r s' ∧ (∀e. s.acked e ≤ s.moved e) ⇒
  infl_inv s'
Proof
  strip_tac >>
  ‘sikeep s s' ⇒ infl_inv s'’ by metis_tac[infl_inv_sikeep] >>
  Cases_on ‘r’
  >- ((* Call *)
      first_x_assum irule >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def, LET_THM] >> strip_tac >>
      ‘∀c h. wikeep (EL n s.procs) (w1 with <| clock := c; hist := h |>)’ by
        (rpt gen_tac >> irule (cj 3 wikeep_fields) >> drule wikeep_call >> simp[]) >>
      every_case_tac >> gvs[] >>
      FIRST [irule sikeep_local >> fs[] >> NO_TAC,
             irule sikeep_with_procs >> fs[] >> NO_TAC,
             irule sikeep_trans >> irule_at (Pos last) sikeep_pair >> rpt conj_tac >>
             FIRST [fs[sys_room_def] >> NO_TAC, irule sikeep_with_procs >> fs[]]])
  >- ((* Kern *)
      rename1 ‘Kern kk’ >> Cases_on ‘kk’ >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def] >> strip_tac >> gvs[]
      >- (first_x_assum irule >> irule sikeep_trans >>
          qexists_tac ‘sys_deliver n (LConnUp n0) s’ >>
          ‘n < LENGTH s.procs ∧ n1 < LENGTH s.procs’ by fs[is_end_def, sys_room_def] >>
          simp[sikeep_deliver] >> irule sikeep_pair >> fs[sys_room_def])
      >- (first_x_assum irule >> rename1 ‘s.peer (n, n0) = SOME (k', j')’ >>
          ‘k' < LENGTH s.procs’ by (drule_all kinv_peer_end >> simp[is_end_def]) >>
          simp[sikeep_deliver])
      >- (irule infl_inv_drain >> simp[])
      >- (first_x_assum irule >> rename1 ‘s.peer (n, n0) = SOME (k', j')’ >>
          ‘k' < LENGTH s.procs’ by (drule_all kinv_peer_end >> simp[is_end_def]) >>
          simp[sikeep_deliver])
      >> first_x_assum irule >> ‘n < LENGTH s.procs’ by fs[is_end_def] >> simp[sikeep_deliver])
  >- ((* Env *)
      rename1 ‘Env ee’ >> Cases_on ‘ee’ >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def] >> strip_tac >> gvs[]
      >- (first_x_assum irule >> fs[sys_room_def] >> simp[sikeep_deliver])
      >- (first_x_assum irule >> ‘n < LENGTH s.procs’ by fs[is_end_def] >>
          simp[sikeep_deliver]) >>
      ‘n < LENGTH s.procs’ by fs[is_end_def] >>
      Cases_on ‘l’ >> gvs[env_arrival_chan_def] >>
      FIRST [first_x_assum irule >> simp[sikeep_deliver] >> NO_TAC,
             rename1 ‘LDrain j m’ >>
             ‘infl_inv ((sys_deliver n (LDrain j m) s) with acked := s.acked)’ suffices_by
               simp[sysstate_component_equality, sys_deliver_def] >>
             irule infl_inv_drain >> simp[]])
  >> (* Exit *)
  first_x_assum irule >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >> simp[sys_step_def] >>
  strip_tac >> gvs[] >>
  ‘sikeep s (s with procs := LUPDATE (close_all (EL n s.procs)) n s.procs)’ by
    (irule sikeep_local >> simp[wikeep_close_all]) >>
  fs[sikeep_def]
QED

Theorem infl_inv_init:
  sys_init ps s ⇒ infl_inv s
Proof
  rw[sys_init_def, infl_inv_def, LET_THM] >> Cases_on ‘e’ >> fs[is_end_def, sys_chan_def] >>
  ‘(EL q s.procs).chans = []’ by metis_tac[] >> fs[]
QED

Theorem irun_infl_inv:
  l0sys_irun ps ss rs ⇒ ∀n. infl_inv (ss n)
Proof
  strip_tac >> Induct
  >- (irule infl_inv_init >> fs[l0sys_irun_def] >> metis_tac[]) >>
  ‘kinv (ss n) ∧ sys_ext (ss n) (ss (SUC n)) ∧ sys_step (ss n) (rs n) (ss (SUC n)) ∧
   ∀e. (ss n).acked e ≤ (ss n).moved e’ by metis_tac[irun_kinv, irun_ext, l0sys_irun_def, irun_acked_le] >>
  metis_tac[infl_inv_step]
QED
