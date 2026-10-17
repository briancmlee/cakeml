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
    ∃k bs. k ≤ LENGTH bs ∧ y.sent = x.sent ++ TAKE k bs ∧ y.inflight = x.inflight + k
End

Definition wikeep_def:
  wikeep (w : l0world) w' ⇔
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀c. c < LENGTH w.chans ⇒ ikeep (EL c w.chans) (EL c w'.chans)) ∧
    (∀c. LENGTH w.chans ≤ c ∧ c < LENGTH w'.chans ⇒
         (EL c w'.chans).inflight = 0 ∧ (EL c w'.chans).sent = [])
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
  qexistsl_tac [‘MIN (LENGTH bs) (w.ch.takes c w.hist (EL c w.chans).inflight (LENGTH bs))’,
                ‘bs’] >> simp[]
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
  (sys_chan s' e).inflight = 0 ∧ (sys_chan s' e).sent = []
Proof
  Cases_on ‘e’ >> rw[sikeep_def, is_end_def, sys_chan_def] >> gvs[] >>
  first_x_assum (qspec_then ‘q’ mp_tac) >> simp[wikeep_def]
QED

