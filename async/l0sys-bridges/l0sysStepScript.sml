(*
  B2's system invariant (sinv) and one step of an l0sys run.

  sinv rs s css: the kernel invariant (kinv), and for each process k its
  per-process invariant (pinv) against its own events in rs, with css k
  its episodes' channels, and how the episodes' roles sit on the kernel's
  targets: a connected episode's end has the port it connected to as its
  target; an accepted episode's end, and a queued connection, has none, and
  its peer's target is the port of the listener it was queued on.
*)
Theory l0sysStep
Ancestors
  honestL0 honestL0World honestL0Rely honestL0WorldProps l0sys l0sysEpisodes
  l0sysEpisodesEcho l0sysInv l0sysInvCall l0sysMono l0sysCausal
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The traces *)

Theorem proc_events_SNOC:
  ∀rs. proc_events k (rs ++ [r]) =
       proc_events k rs ++
       (case r of
        | Call k' nm conf bytes out =>
            if k' = k then [IO_event (ExtCall nm) conf (ZIP (bytes, out))] else []
        | _ => [])
Proof
  Induct >> TRY (Cases_on ‘r’) >> TRY (Cases_on ‘h’) >> rw[proc_events_def] >>
  every_case_tac >> gvs[proc_events_def]
QED

Definition ev_role_def:
  ev_role lst ev =
    case ev_new ev of
    | SOME (_, INL p) => [Connected p]
    | SOME (_, INR l) => [Accepted (case ALOOKUP lst l of SOME p => p | NONE => 0)]
    | NONE => []
End

Theorem ep_roles_SNOC:
  ∀evs lst. ep_roles lst (evs ++ [ev]) = ep_roles lst evs ++ ev_role (FOLDL lsn_step lst evs) ev
Proof
  Induct >> simp[ep_roles_def, ev_role_def, lsn_step_def] >> rw[] >>
  every_case_tac >> gvs[]
QED

Theorem LENGTH_ep_roles:
  ∀evs lst. LENGTH (ep_roles lst evs) = LENGTH (ep_fds evs)
Proof
  Induct >> simp[ep_roles_def, ep_fds_def] >> rw[] >> every_case_tac >> gvs[] >>
  simp[GSYM ep_fds_def]
QED

(*---------------------------------------------------------------------------*)
(* Fields the invariants do not read *)

Theorem kinv_fields[simp]:
  (kinv (s with acked := X1) ⇔ kinv s) ∧ (kinv (s with finned := X2) ⇔ kinv s) ∧
  (kinv (s with alive := X3) ⇔ kinv s)
Proof
  simp[kinv_def]
QED

Theorem wmono_close_all:
  wmono w (close_all w)
Proof
  simp[close_all_def] >>
  qspec_tac (‘MAP FST w.open_fds ++ MAP FST w.listeners’, ‘fs’) >>
  ‘∀fs w'. wmono w w' ⇒ wmono w (FOLDL (λw f. close_fd f w) w' fs)’
    by (Induct >> rw[] >> first_x_assum irule >> irule wmono_close_fd >> simp[]) >>
  rw[]
QED

(*---------------------------------------------------------------------------*)
(* The invariant *)

Definition pk_def:
  pk rs (s : sysstate) css k ⇔
    let w = EL k s.procs; evs = proc_events k rs; rl = ep_roles [] evs in
      l0_rely w ∧ small_ch w.ch ∧ pinv evs w (css k) ∧
      (∀j p. j < LENGTH (css k) ∧ EL j rl = Connected p ⇒
             s.target (k, EL j (css k)) = SOME p) ∧
      (∀j p. j < LENGTH (css k) ∧ EL j rl = Accepted p ⇒
             s.target (k, EL j (css k)) = NONE ∧
             ∀e. s.peer (k, EL j (css k)) = SOME e ⇒ s.target e = SOME p) ∧
      (∀l p q c. MEM (l, p, q) w.listeners ∧ MEM c q ⇒
             s.target (k, c) = NONE ∧ ∀e. s.peer (k, c) = SOME e ⇒ s.target e = SOME p)
End

Definition sinv_def:
  sinv rs s css ⇔ kinv s ∧ ∀k. k < LENGTH s.procs ⇒ pk rs s css k
End

Theorem pk_fields[simp]:
  (pk rs (s with moved := X1) css k ⇔ pk rs s css k) ∧
  (pk rs (s with acked := X2) css k ⇔ pk rs s css k) ∧
  (pk rs (s with finned := X3) css k ⇔ pk rs s css k) ∧
  (pk rs (s with alive := X4) css k ⇔ pk rs s css k)
Proof
  simp[pk_def]
QED

(* An arrival other than a new connection, at any process *)
Theorem pk_deliver_other:
  pk rs s css k ∧ k' < LENGTH s.procs ∧ (∀p. a ≠ LIncoming p) ⇒
  pk rs (sys_deliver k' a s) css k
Proof
  strip_tac >>
  ‘(l0_deliver (EL k' s.procs) a).listeners = (EL k' s.procs).listeners ∧
   (l0_deliver (EL k' s.procs) a).ch = (EL k' s.procs).ch ∧
   (l0_deliver (EL k' s.procs) a).fd_limit = (EL k' s.procs).fd_limit’
    by (Cases_on ‘a’ >> gvs[] >> rw[l0_deliver_def]) >>
  ‘l0_rely (EL k' s.procs) ⇒ l0_rely (l0_deliver (EL k' s.procs) a)’
    by (strip_tac >> irule l0_rely_ch >> qexists_tac ‘EL k' s.procs’ >> simp[]) >>
  Cases_on ‘k = k'’ >> gvs[pk_def, sys_deliver_def, EL_LUPDATE, pinv_deliver] >>
  rpt strip_tac >> res_tac >> fs[]
QED

Theorem sinv_init:
  sys_init ps s0 ∧ (∀k. k < LENGTH ps ⇒ small_ch (EL k s0.procs).ch) ⇒ sinv [] s0 (K [])
Proof
  rw[sys_init_def, sinv_def, kinv_def, pk_def] >> gvs[] >>
  TRY (rename1 ‘is_end s0 e’ >> Cases_on ‘e’ >> gvs[is_end_def] >> res_tac >> gvs[] >> NO_TAC) >>
  res_tac >> gvs[proc_events_def] >> irule pinv_init >> simp[fds_lt_def]
QED

(*---------------------------------------------------------------------------*)
(* Queues only shrink, keeping their listener's port, except for an arrival *)

Definition lsub_def:
  lsub (w : l0world) w' ⇔
    ∀l p q c. MEM (l, p, q) w'.listeners ∧ MEM c q ⇒
              ∃q0. MEM (l, p, q0) w.listeners ∧ MEM c q0
End

Theorem lsub_refl[simp]:
  lsub w w
Proof
  simp[lsub_def] >> metis_tac[]
QED

Theorem lsub_close_fd:
  lsub w w' ⇒ lsub w (close_fd f w')
Proof
  rw[close_fd_def, lsub_def] >> every_case_tac >> gvs[] >>
  TRY (‘∀q w''. (FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) w'' q).listeners =
                w''.listeners’ by (Induct >> simp[]) >> gvs[]) >>
  gvs[MEM_FILTER] >> metis_tac[]
QED

Theorem lsub_close_all:
  lsub w (close_all w)
Proof
  simp[close_all_def] >>
  qspec_tac (‘MAP FST w.open_fds ++ MAP FST w.listeners’, ‘fs’) >>
  ‘∀fs w'. lsub w w' ⇒ lsub w (FOLDL (λw f. close_fd f w) w' fs)’
    by (Induct >> rw[] >> first_x_assum irule >> irule lsub_close_fd >> simp[]) >>
  rw[]
QED

Theorem lsub_fields:
  lsub w w' ⇒
  lsub w (upd_lchan j g w') ∧ lsub w (w' with open_fds := X) ∧
  lsub w (w' with <| chans := C; open_fds := X |>) ∧ lsub w (w' with <| clock := n; hist := h |>)
Proof
  simp[lsub_def]
QED

Theorem lsub_pop:
  FILTER (λ(l', p, q). l' = l0) w.listeners = (l1, p1, j1 :: q1) :: t1 ⇒
  lsub w (w with listeners := AFUPDKEY l0 (K (p1, q1)) w.listeners)
Proof
  strip_tac >>
  ‘MEM (l1, p1, j1 :: q1) (FILTER (λ(l', p, q). l' = l0) w.listeners)’ by simp[] >>
  ‘l1 = l0 ∧ MEM (l0, p1, j1 :: q1) w.listeners’ by gvs[MEM_FILTER] >>
  simp[lsub_def] >> rpt strip_tac >> drule MEM_AFUPDKEY_imp >> rw[] >- metis_tac[] >>
  metis_tac[MEM]
QED

Theorem lsub_call:
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒ lsub w w1
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> simp[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [
    gvs[l0_listen_def, AllCaseEqs(), lsub_def] >> metis_tac[MEM] >> NO_TAC,
    drule l0_accept_cases >> strip_tac >> rveq >>
    FIRST [simp[] >> NO_TAC, drule lsub_pop >> simp[lsub_def]] >> NO_TAC,
    drule l0_recv_cases >> strip_tac >> gvs[lsub_fields] >> NO_TAC,
    drule l0_send_cases >> strip_tac >> gvs[lsub_fields] >> NO_TAC,
    gvs[l0_shutdown_def, AllCaseEqs(), lsub_fields] >> NO_TAC,
    drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[lsub_fields] >> NO_TAC,
    gvs[l0_connerr_def, AllCaseEqs(), lsub_fields] >> NO_TAC,
    gvs[l0_close_def, AllCaseEqs()] >> rw[lsub_close_fd] >> NO_TAC]
QED

(*---------------------------------------------------------------------------*)
(* Steps that are arrivals only *)

Theorem LENGTH_sys_deliver[simp]:
  LENGTH (sys_deliver k a s).procs = LENGTH s.procs
Proof
  simp[sys_deliver_def]
QED

Theorem sys_deliver_fields[simp]:
  (sys_deliver k a s).peer = s.peer ∧ (sys_deliver k a s).target = s.target ∧
  (sys_deliver k a s).moved = s.moved
Proof
  simp[sys_deliver_def]
QED

Theorem proc_events_other:
  (∀k nm conf bytes out. r ≠ Call k nm conf bytes out) ⇒
  proc_events k (rs ++ [r]) = proc_events k rs
Proof
  rw[proc_events_SNOC] >> Cases_on ‘r’ >> gvs[]
QED

Theorem sinv_other_deliver:
  sinv rs s css ∧ k' < LENGTH s.procs ∧ (∀p. a ≠ LIncoming p) ∧
  kinv s' ∧ (s' = sys_deliver k' a s ∨ (∃X. s' = (sys_deliver k' a s) with moved := X) ∨
             (∃X. s' = (sys_deliver k' a s) with acked := X) ∨
             (∃Y. s' = (sys_deliver k' a s) with finned := Y)) ∧
  (∀k nm conf bytes out. r ≠ Call k nm conf bytes out) ⇒
  sinv (rs ++ [r]) s' css
Proof
  strip_tac >>
  ‘∀k. k < LENGTH s.procs ⇒ pk (rs ++ [r]) (sys_deliver k' a s) css k’
    by (rpt strip_tac >>
        ‘pk rs s css k’ by fs[sinv_def] >>
        ‘pk rs (sys_deliver k' a s) css k’ by (irule pk_deliver_other >> simp[]) >>
        ‘proc_events k (rs ++ [r]) = proc_events k rs’
          by (irule proc_events_other >> first_x_assum ACCEPT_TAC) >>
        qpat_x_assum ‘pk rs (sys_deliver _ _ _) _ _’ mp_tac >> simp[pk_def] >>
        rpt strip_tac >> res_tac >> fs[]) >>
  gvs[sinv_def]
QED
