(*
  Moonshot liveness, N5b (sys_delivers_claim, moonshotLiveChain): the
  kernel delivers everything an end sent to a receiver that keeps asking,
  unless the receiving end is lost (broken or closed) by then.

  B2's kinv says, of a pair e ↦ e', that e''s arrived bytes are e's first
  `moved` bytes UNLESS e' is frozen (peer EOF, broken or closed).  A peer
  EOF is no loss: it is delivered only by Fin, after every byte has moved.
  fin_inv makes that precise, as an invariant of every run:
   - a receiver at EOF has a FINNED sender;
   - a finned end is shut, has moved all it sent, and its receiver holds
     all of it, or is lost;
   - a finned end has a peer, and a connecting end is not at EOF.
  The channel-level facts (ckeep: what a call or an arrival other than data
  and EOF keeps) mirror m4-server's cmono (l0sysMono).
*)
Theory moonshotLiveDeliver
Ancestors
  moonshotLiveChain moonshotLiveDrains l0sysFair l0sys l0sysCausal l0sysMono l0sysRun
  l0sysStep l0sysInvCall honestL0World
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* Channels *)

Definition lostc_def:
  lostc (c : lchan) ⇔ c.broken ∨ c.closed
End

Definition ckeep_def:
  ckeep (x : lchan) y ⇔
    y.peer_sent = x.peer_sent ∧ y.peer_eof = x.peer_eof ∧ x.sent ≼ y.sent ∧
    (x.shut ⇒ y.shut ∧ y.sent = x.sent) ∧ (lostc x ⇒ lostc y) ∧
    (y.connecting ⇒ x.connecting)
End

Definition wkeep_def:
  wkeep (w : l0world) w' ⇔
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀c. c < LENGTH w.chans ⇒ ckeep (EL c w.chans) (EL c w'.chans)) ∧
    (∀c. LENGTH w.chans ≤ c ∧ c < LENGTH w'.chans ⇒ ¬(EL c w'.chans).peer_eof)
End

Theorem ckeep_refl[simp]:
  ckeep x x
Proof
  simp[ckeep_def]
QED

Theorem ckeep_trans:
  ckeep x y ∧ ckeep y z ⇒ ckeep x z
Proof
  rw[ckeep_def] >> fs[] >> metis_tac[IS_PREFIX_TRANS]
QED

Theorem wkeep_refl[simp]:
  wkeep w w
Proof
  simp[wkeep_def]
QED

Theorem wkeep_upd:
  wkeep w w' ∧ (j < LENGTH w'.chans ⇒ ckeep (EL j w'.chans) (g (EL j w'.chans))) ∧
  (LENGTH w.chans ≤ j ∧ j < LENGTH w'.chans ⇒ ((g (EL j w'.chans)).peer_eof ⇔ (EL j w'.chans).peer_eof)) ⇒
  wkeep w (upd_lchan j g w')
Proof
  rw[wkeep_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[] >>
  TRY (irule ckeep_trans >> qexists_tac ‘EL c w'.chans’ >> fs[] >> NO_TAC) >>
  fs[ckeep_def]
QED

Theorem wkeep_fields:
  wkeep w w' ⇒
  wkeep w (w' with open_fds := X) ∧ wkeep w (w' with listeners := L) ∧
  wkeep w (w' with reserved := R) ∧ wkeep w (w' with <| clock := n; hist := h |>) ∧
  wkeep w (w' with <| listeners := L; open_fds := X |>)
Proof
  simp[wkeep_def]
QED

Theorem wkeep_append:
  wkeep w w' ∧ ¬c0.peer_eof ⇒
  wkeep w (w' with chans := w'.chans ++ [c0]) ∧
  wkeep w (w' with <| chans := w'.chans ++ [c0]; open_fds := X |>) ∧
  wkeep w (w' with <| listeners := L; chans := w'.chans ++ [c0] |>)
Proof
  rw[wkeep_def] >> rw[EL_APPEND1, EL_APPEND2] >>
  Cases_on ‘c < LENGTH w'.chans’ >> gvs[EL_APPEND1, EL_APPEND2] >>
  ‘c = LENGTH w'.chans’ by simp[] >> gvs[]
QED

Theorem ckeep_break[simp]:
  ckeep x (break_lchan e k x)
Proof
  rw[ckeep_def, break_lchan_def, lostc_def]
QED

Theorem wkeep_breaks:
  ∀q w'. wkeep w w' ⇒ wkeep w (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w' q)
Proof
  Induct >> rw[] >> first_x_assum irule >> irule wkeep_upd >> simp[] >>
  rw[break_lchan_def]
QED

Theorem wkeep_close_fd:
  wkeep w w' ⇒ wkeep w (close_fd f w')
Proof
  rw[close_fd_def] >> every_case_tac >> gvs[wkeep_fields] >>
  TRY (irule wkeep_breaks >> simp[wkeep_fields] >> NO_TAC) >>
  irule wkeep_upd >> simp[wkeep_fields, ckeep_def, lostc_def]
QED

Theorem wkeep_close_all:
  wkeep w (close_all w)
Proof
  simp[close_all_def] >>
  ‘∀fs w'. wkeep w w' ⇒ wkeep w (FOLDL (λw f. close_fd f w) w' fs)’ suffices_by simp[] >>
  Induct >> rw[] >> first_x_assum irule >> irule wkeep_close_fd >> simp[]
QED

(* Calls *)
Theorem wkeep_upd_old[local]:
  j < LENGTH w.chans ∧ ckeep (EL j w.chans) (g (EL j w.chans)) ⇒ wkeep w (upd_lchan j g w)
Proof
  strip_tac >> irule wkeep_upd >> simp[]
QED

Theorem wkeep_recv:
  l0_recv f n w = (r, d, w') ⇒ wkeep w w'
Proof
  strip_tac >> drule l0_recv_cases >> rw[] >> rw[] >>
  irule wkeep_upd_old >> simp[ckeep_def, lostc_def] >> metis_tac[l0_chan_of_lt]
QED

Theorem wkeep_send:
  l0_send f bs w = (r, w') ⇒ wkeep w w'
Proof
  strip_tac >> drule l0_send_cases >> rw[] >> rw[] >>
  irule wkeep_upd_old >> simp[ckeep_def, lostc_def] >>
  TRY (metis_tac[l0_chan_of_lt]) >>
  drule l0_chan_of_lt >> strip_tac >> simp[] >> strip_tac >>
  qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >> simp[l0_send_def] >>
  every_case_tac >> simp[LET_THM] >> rw[] >> gvs[fail_def]
QED

Theorem wkeep_shutdown:
  l0_shutdown f w = (r, w') ⇒ wkeep w w'
Proof
  rw[l0_shutdown_def, AllCaseEqs()] >> rw[] >>
  irule wkeep_upd_old >> simp[ckeep_def, lostc_def] >> metis_tac[l0_chan_of_lt]
QED

Theorem wkeep_connerr:
  l0_connerr f w = (r, w') ⇒ wkeep w w'
Proof
  rw[l0_connerr_def, AllCaseEqs()] >> rw[] >>
  irule wkeep_upd_old >> simp[ckeep_def, lostc_def] >> metis_tac[l0_chan_of_lt]
QED

Theorem wkeep_connect:
  l0_connect p w = (r, v, w') ⇒ wkeep w w'
Proof
  strip_tac >> drule l0_connect_cases >> rw[] >> rw[] >>
  TRY (irule wkeep_upd >> simp[ckeep_def, lostc_def, EL_APPEND2, fresh_lchan_def]) >>
  irule (cj 2 wkeep_append) >> simp[fresh_lchan_def]
QED

Theorem wkeep_close:
  l0_close f w = (r, w') ⇒ wkeep w w'
Proof
  rw[l0_close_def, AllCaseEqs()] >> rw[wkeep_close_fd]
QED

Theorem wkeep_call:
  l0_call nm (unblock nm conf) (bs : word8 list) w = SOME (FFIreturn out w1) ⇒ wkeep w w1
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> simp[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [
    gvs[l0_listen_def, AllCaseEqs(), wkeep_fields] >> NO_TAC,
    drule l0_accept_cases >> strip_tac >> gvs[wkeep_fields] >>
    TRY (irule wkeep_upd >> simp[wkeep_fields] >> rw[break_lchan_def]) >> NO_TAC,
    metis_tac[wkeep_recv, wkeep_send, wkeep_shutdown, wkeep_connerr, wkeep_connect,
              wkeep_close]]
QED

(* Arrivals other than data and EOF *)
Theorem wkeep_deliver:
  (∀j bs. a ≠ LData j bs) ∧ (∀j. a ≠ LEof j) ⇒ wkeep w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  TRY (irule (cj 3 wkeep_append) >> simp[fresh_lchan_def] >> NO_TAC) >>
  irule wkeep_upd >> simp[ckeep_def, break_lchan_def, lostc_def] >> rw[]
QED

(* Data and EOF arrivals, at channel j *)
Theorem deliver_data_keep:
  LENGTH (l0_deliver w (LData j bs)).chans = LENGTH w.chans ∧
  ∀c. c < LENGTH w.chans ⇒
      let x = EL c w.chans; y = EL c (l0_deliver w (LData j bs)).chans in
        y.peer_eof = x.peer_eof ∧ y.shut = x.shut ∧ y.sent = x.sent ∧
        (lostc y ⇔ lostc x) ∧ y.connecting = x.connecting ∧
        y.peer_sent = if c = j ∧ ¬x.peer_eof ∧ ¬lostc x ∧ ¬x.connecting
                      then x.peer_sent ++ bs else x.peer_sent
Proof
  rw[l0_deliver_def, upd_lchan_def, EL_LUPDATE, lostc_def] >> rw[] >> gvs[]
QED

Theorem deliver_eof_keep:
  LENGTH (l0_deliver w (LEof j)).chans = LENGTH w.chans ∧
  ∀c. c < LENGTH w.chans ⇒
      let x = EL c w.chans; y = EL c (l0_deliver w (LEof j)).chans in
        y.peer_sent = x.peer_sent ∧ y.shut = x.shut ∧ y.sent = x.sent ∧
        (lostc y ⇔ lostc x) ∧ y.connecting = x.connecting ∧
        (y.peer_eof ⇔ x.peer_eof ∨ c = j ∧ ¬x.broken ∧ ¬x.connecting)
Proof
  rw[l0_deliver_def, upd_lchan_def, EL_LUPDATE, lostc_def] >> Cases_on ‘c = j’ >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* System steps that keep every channel (all but Move, Fin and an outside
   arrival of data or EOF) *)

Definition skeep_def:
  skeep (s : sysstate) s' ⇔
    LENGTH s'.procs = LENGTH s.procs ∧
    (∀k. k < LENGTH s.procs ⇒ wkeep (EL k s.procs) (EL k s'.procs)) ∧
    s'.moved = s.moved ∧ s'.finned = s.finned
End

Theorem skeep_end:
  skeep s s' ∧ is_end s e ⇒ is_end s' e ∧ ckeep (sys_chan s e) (sys_chan s' e)
Proof
  Cases_on ‘e’ >> rw[skeep_def, is_end_def, sys_chan_def] >> res_tac >> fs[wkeep_def]
QED

Theorem skeep_new:
  skeep s s' ∧ ¬is_end s e ∧ is_end s' e ⇒ ¬(sys_chan s' e).peer_eof
Proof
  Cases_on ‘e’ >> rw[skeep_def, is_end_def, sys_chan_def] >> gvs[] >>
  first_x_assum (qspec_then ‘q’ mp_tac) >> simp[wkeep_def]
QED

Theorem skeep_trans:
  skeep s1 s2 ∧ skeep s2 s3 ⇒ skeep s1 s3
Proof
  rw[skeep_def] >> rw[] >> fs[] >>
  ‘wkeep (EL k s1.procs) (EL k s2.procs) ∧ wkeep (EL k s2.procs) (EL k s3.procs)’ by simp[] >>
  fs[wkeep_def] >> rw[]
  >- (irule ckeep_trans >> qexists_tac ‘EL c (EL k s2.procs).chans’ >> simp[])
  >> Cases_on ‘c < LENGTH (EL k s2.procs).chans’ >> fs[ckeep_def] >>
  ‘¬(EL c (EL k s2.procs).chans).peer_eof’ by simp[] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> simp[]
QED

Theorem skeep_local:
  k < LENGTH s.procs ∧ wkeep (EL k s.procs) w' ⇒
  skeep s (s with procs := LUPDATE w' k s.procs)
Proof
  rw[skeep_def, EL_LUPDATE] >> rw[]
QED

Theorem skeep_fields[simp]:
  (skeep s (s' with target := X1) ⇔ skeep s s') ∧ (skeep s (s' with peer := X2) ⇔ skeep s s') ∧
  (skeep s (s' with acked := X3) ⇔ skeep s s') ∧ (skeep s (s' with alive := X4) ⇔ skeep s s')
Proof
  simp[skeep_def]
QED

Theorem skeep_deliver:
  k < LENGTH s.procs ∧ (∀j bs. a ≠ LData j bs) ∧ (∀j. a ≠ LEof j) ⇒ skeep s (sys_deliver k a s)
Proof
  rw[sys_deliver_def] >> irule skeep_local >> simp[wkeep_deliver]
QED

Theorem skeep_pair:
  k' < LENGTH s.procs ⇒ skeep s (sys_pair e k' p s)
Proof
  rw[sys_pair_def] >> irule skeep_deliver >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* The invariant *)

Definition fin_inv_def:
  fin_inv (s : sysstate) ⇔
    (∀e. s.finned e ⇒ s.peer e ≠ NONE) ∧
    (∀e. is_end s e ∧ (sys_chan s e).connecting ⇒ ¬(sys_chan s e).peer_eof) ∧
    (∀e e'. s.peer e = SOME e' ∧ (sys_chan s e').peer_eof ⇒ s.finned e) ∧
    (∀e e'. s.peer e = SOME e' ∧ s.finned e ⇒
            (sys_chan s e).shut ∧ s.moved e = LENGTH (sys_chan s e).sent ∧
            (lostc (sys_chan s e') ∨ (sys_chan s e').peer_sent = (sys_chan s e).sent))
End

Theorem kinv_peer_inj:
  kinv s ∧ s.peer e1 = SOME e' ∧ s.peer e2 = SOME e' ⇒ e1 = e2
Proof
  rw[kinv_def] >> res_tac >> fs[]
QED

Theorem kinv_peer_end:
  kinv s ∧ s.peer e = SOME e' ⇒ is_end s e ∧ is_end s e' ∧ s.peer e' = SOME e
Proof
  rw[kinv_def] >> res_tac >> fs[] >> res_tac
QED

Theorem fin_inv_skeep:
  kinv s ∧ kinv s' ∧ fin_inv s ∧ skeep s s' ∧ sys_ext s s' ⇒ fin_inv s'
Proof
  strip_tac >> simp[fin_inv_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- ((* a finned end has a peer *)
      ‘s.finned e’ by (‘s'.finned = s.finned’ by fs[skeep_def] >> fs[]) >>
      ‘s.peer e ≠ NONE’ by (qpat_x_assum ‘fin_inv s’ mp_tac >> rw[fin_inv_def]) >>
      Cases_on ‘s.peer e’ >> fs[] >>
      qpat_x_assum ‘sys_ext _ _’ mp_tac >> rw[sys_ext_def] >> res_tac >> fs[])
  >- ((* a connecting end is not at EOF *)
      Cases_on ‘is_end s e’
      >- (drule_all skeep_end >> rw[ckeep_def] >>
          qpat_x_assum ‘fin_inv s’ mp_tac >> rw[fin_inv_def] >> metis_tac[])
      >> drule_all skeep_new >> simp[])
  >- ((* a receiver at EOF has a finned sender *)
      ‘s'.finned e = s.finned e’ by (‘s'.finned = s.finned’ by fs[skeep_def] >> fs[]) >> simp[] >>
      Cases_on ‘s.peer e = SOME e'’
      >- (‘is_end s e'’ by metis_tac[kinv_peer_end] >>
          drule_all skeep_end >> rw[ckeep_def] >>
          qpat_x_assum ‘fin_inv s’ mp_tac >> rw[fin_inv_def] >> metis_tac[])
      >> ‘is_end s' e'’ by metis_tac[kinv_peer_end] >>
      ‘new_pair s e e' ∨ new_pair s e' e’ by
        (qpat_x_assum ‘sys_ext _ _’ mp_tac >> rw[sys_ext_def] >> metis_tac[]) >>
      ‘is_end s e' ⇒ ¬(sys_chan s' e').peer_eof’ by
        (strip_tac >> fs[new_pair_def] >>
         drule_all skeep_end >> rw[ckeep_def] >>
         qpat_x_assum ‘fin_inv s’ mp_tac >> rw[fin_inv_def] >> metis_tac[]) >>
      ‘¬is_end s e' ⇒ ¬(sys_chan s' e').peer_eof’ by
        (strip_tac >> drule_all skeep_new >> simp[]) >>
      metis_tac[])
  >> (* a finned end has delivered all it sent, unless its receiver is lost *)
  ‘s.finned e’ by (‘s'.finned = s.finned’ by fs[skeep_def] >> fs[]) >>
  ‘∃e''. s.peer e = SOME e''’ by
    (qpat_x_assum ‘fin_inv s’ mp_tac >> rw[fin_inv_def] >> Cases_on ‘s.peer e’ >> fs[] >>
     res_tac >> fs[]) >>
  ‘s'.peer e = SOME e''’ by (qpat_x_assum ‘sys_ext _ _’ mp_tac >> rw[sys_ext_def]) >>
  ‘e'' = e'’ by fs[] >> gvs[] >>
  ‘is_end s e ∧ is_end s e'’ by metis_tac[kinv_peer_end] >>
  ‘ckeep (sys_chan s e) (sys_chan s' e) ∧ ckeep (sys_chan s e') (sys_chan s' e')’ by
    metis_tac[skeep_end] >>
  ‘s'.moved = s.moved’ by fs[skeep_def] >>
  qpat_x_assum ‘fin_inv s’ mp_tac >> rw[fin_inv_def] >>
  first_x_assum (qspecl_then [‘e’, ‘e'’] mp_tac) >> simp[] >> fs[ckeep_def] >> rw[] >> fs[]
QED

(*---------------------------------------------------------------------------*)
(* Data and EOF arrivals, at system level *)

Theorem deliver_de_facts:
  k' < LENGTH s.procs ∧ (a = LData j' d ∨ a = LEof j') ⇒
  (∀e. is_end (sys_deliver k' a s) e ⇔ is_end s e) ∧
  ∀e. is_end s e ⇒
      (sys_chan (sys_deliver k' a s) e).sent = (sys_chan s e).sent ∧
      (sys_chan (sys_deliver k' a s) e).shut = (sys_chan s e).shut ∧
      (lostc (sys_chan (sys_deliver k' a s) e) ⇔ lostc (sys_chan s e)) ∧
      (sys_chan (sys_deliver k' a s) e).connecting = (sys_chan s e).connecting ∧
      (e ≠ (k', j') ⇒
         (sys_chan (sys_deliver k' a s) e).peer_sent = (sys_chan s e).peer_sent ∧
         (sys_chan (sys_deliver k' a s) e).peer_eof = (sys_chan s e).peer_eof) ∧
      ((sys_chan s e).connecting ∨ (∃d. a = LData j' d) ⇒
         (sys_chan (sys_deliver k' a s) e).peer_eof = (sys_chan s e).peer_eof) ∧
      (a = LEof j' ⇒ (sys_chan (sys_deliver k' a s) e).peer_sent = (sys_chan s e).peer_sent)
Proof
  strip_tac >> rpt var_eq_tac
  >- (assume_tac (Q.SPECL [‘EL k' s.procs’, ‘j'’, ‘d’] (Q.GENL [‘w’, ‘j’, ‘bs’] deliver_data_keep)) >>
      conj_tac
      >- (Cases >> rw[is_end_def, sys_deliver_def, EL_LUPDATE] >> rw[] >> fs[]) >>
      Cases >> rw[is_end_def, sys_chan_def, sys_deliver_def, EL_LUPDATE] >>
      qpat_x_assum ‘∀c. _’ (qspec_then ‘r’ mp_tac) >> simp[] >> rw[] >> gvs[])
  >> assume_tac (Q.SPECL [‘EL k' s.procs’, ‘j'’] (Q.GENL [‘w’, ‘j’] deliver_eof_keep)) >>
  conj_tac
  >- (Cases >> rw[is_end_def, sys_deliver_def, EL_LUPDATE] >> rw[] >> fs[]) >>
  Cases >> rw[is_end_def, sys_chan_def, sys_deliver_def, EL_LUPDATE] >>
  qpat_x_assum ‘∀c. _’ (qspec_then ‘r’ mp_tac) >> simp[] >> rw[] >> gvs[]
QED

Theorem deliver_fields[simp]:
  (sys_deliver k a s).peer = s.peer ∧ (sys_deliver k a s).finned = s.finned ∧
  (sys_deliver k a s).moved = s.moved
Proof
  simp[sys_deliver_def]
QED

Theorem fin_inv_move:
  kinv s ∧ fin_inv s ∧ s.peer e0 = SOME (k', j') ∧ 0 < n ∧
  s.moved e0 + n ≤ LENGTH (sys_chan s e0).sent ⇒
  fin_inv ((sys_deliver k' (LData j' d) s) with moved := (e0 =+ s.moved e0 + n) s.moved)
Proof
  strip_tac >>
  ‘is_end s e0 ∧ is_end s (k', j') ∧ s.peer (k', j') = SOME e0’ by metis_tac[kinv_peer_end] >>
  ‘k' < LENGTH s.procs’ by fs[is_end_def] >>
  qspecl_then [‘k'’, ‘s’, ‘LData j' d’, ‘j'’, ‘d’] mp_tac
    (Q.GENL [‘k'’, ‘s’, ‘a’, ‘j'’, ‘d’] deliver_de_facts) >>
  simp[] >> strip_tac >>
  qpat_x_assum ‘fin_inv s’ (strip_assume_tac o REWRITE_RULE [fin_inv_def]) >>
  PURE_REWRITE_TAC [fin_inv_def] >> rpt conj_tac >> rpt gen_tac >| [
    simp[] >> metis_tac[],
    simp[] >> strip_tac >> ‘is_end s e’ by metis_tac[] >> metis_tac[],
    simp[] >> strip_tac >> ‘is_end s e'’ by metis_tac[kinv_peer_end] >> metis_tac[],
    simp[] >> strip_tac >> Cases_on ‘e = e0’
    >- (gvs[] >> first_x_assum (qspecl_then [‘e0’, ‘(k', j')’] mp_tac) >> simp[]) >>
    ‘e' ≠ (k', j')’ by metis_tac[kinv_peer_inj] >>
    ‘is_end s e ∧ is_end s e'’ by metis_tac[kinv_peer_end] >>
    simp[combinTheory.APPLY_UPDATE_THM] >>
    first_x_assum (qspecl_then [‘e’, ‘e'’] mp_tac) >> simp[] >> metis_tac[]]
QED

Theorem fin_inv_fin:
  kinv s ∧ fin_inv s ∧ s.peer e0 = SOME (k', j') ∧ (sys_chan s e0).shut ∧ ¬s.finned e0 ∧
  s.moved e0 = LENGTH (sys_chan s e0).sent ⇒
  fin_inv ((sys_deliver k' (LEof j') s) with finned := (e0 =+ T) s.finned)
Proof
  strip_tac >>
  ‘is_end s e0 ∧ is_end s (k', j') ∧ s.peer (k', j') = SOME e0’ by metis_tac[kinv_peer_end] >>
  ‘k' < LENGTH s.procs’ by fs[is_end_def] >>
  qspecl_then [‘k'’, ‘s’, ‘LEof j'’, ‘j'’, ‘[]’] mp_tac
    (Q.GENL [‘k'’, ‘s’, ‘a’, ‘j'’, ‘d’] deliver_de_facts) >>
  simp[] >> strip_tac >>
  ‘¬frozen (sys_chan s (k', j')) ⇒
   (sys_chan s (k', j')).peer_sent = TAKE (s.moved e0) (sys_chan s e0).sent’ by
    (qpat_x_assum ‘kinv s’ (fn th => mp_tac (CONJUNCT1 (CONJUNCT2 (REWRITE_RULE [kinv_def] th)))) >>
     disch_then (qspecl_then [‘e0’, ‘(k', j')’] mp_tac) >> simp[] >> rw[] >> fs[]) >>
  qpat_x_assum ‘fin_inv s’ (strip_assume_tac o REWRITE_RULE [fin_inv_def]) >>
  qabbrev_tac ‘s1 = sys_deliver k' (LEof j') s’ >>
  PURE_REWRITE_TAC [fin_inv_def] >> rpt conj_tac >> rpt gen_tac >| [
    simp[] >> strip_tac >> Cases_on ‘e = e0’ >> fs[combinTheory.APPLY_UPDATE_THM] >>
    qunabbrev_tac ‘s1’ >> fs[],
    simp[] >> strip_tac >>
    ‘is_end s e’ by (qpat_x_assum ‘∀e. is_end s1 e ⇔ _’ (qspec_then ‘e’ mp_tac) >> simp[]) >>
    qpat_x_assum ‘∀e. is_end s e ⇒ _’ (qspec_then ‘e’ mp_tac) >> simp[] >> strip_tac >>
    qpat_x_assum ‘∀e. is_end s e ∧ _ ⇒ _’ (qspec_then ‘e’ mp_tac) >> fs[],
    simp[] >> strip_tac >> Cases_on ‘e = e0’ >> simp[combinTheory.APPLY_UPDATE_THM] >>
    ‘s.peer e = SOME e'’ by (qunabbrev_tac ‘s1’ >> fs[]) >>
    ‘e' ≠ (k', j')’ by (CCONTR_TAC >> fs[] >> metis_tac[kinv_peer_inj]) >>
    ‘is_end s e'’ by metis_tac[kinv_peer_end] >>
    qpat_x_assum ‘∀e. is_end s e ⇒ _’ (qspec_then ‘e'’ mp_tac) >> simp[] >> strip_tac >>
    qpat_x_assum ‘∀e e'. s.peer e = SOME e' ∧ (sys_chan s e').peer_eof ⇒ _’
      (qspecl_then [‘e’, ‘e'’] mp_tac) >> fs[],
    simp[] >> strip_tac >>
    ‘s.peer e = SOME e'’ by (qunabbrev_tac ‘s1’ >> fs[]) >>
    Cases_on ‘e = e0’
    >- (gvs[] >>
        ‘¬(sys_chan s (k', j')).peer_eof’ by
          (strip_tac >> qpat_x_assum ‘∀e e'. s.peer e = SOME e' ∧ (sys_chan s e').peer_eof ⇒ _’
             (qspecl_then [‘e’, ‘(k', j')’] mp_tac) >> simp[]) >>
        qpat_x_assum ‘∀e. is_end s e ⇒ _’ (qspec_then ‘(k', j')’ mp_tac) >> simp[] >>
        strip_tac >> ‘s1.moved = s.moved’ by (qunabbrev_tac ‘s1’ >> simp[]) >>
        Cases_on ‘lostc (sys_chan s (k', j'))’ >> fs[] >>
        ‘¬frozen (sys_chan s (k', j'))’ by fs[frozen_def, lostc_def] >> fs[]) >>
    ‘s.finned e’ by fs[combinTheory.APPLY_UPDATE_THM] >>
    ‘e' ≠ (k', j')’ by (CCONTR_TAC >> fs[] >> metis_tac[kinv_peer_inj]) >>
    ‘is_end s e ∧ is_end s e'’ by metis_tac[kinv_peer_end] >>
    qpat_x_assum ‘∀e e'. s.peer e = SOME e' ∧ s.finned e ⇒ _’
      (qspecl_then [‘e’, ‘e'’] mp_tac) >> simp[] >> strip_tac >>
    qpat_x_assum ‘∀e. is_end s e ⇒ _’ (fn th =>
      assume_tac (Q.SPEC ‘e’ th) >> assume_tac (Q.SPEC ‘e'’ th)) >>
    ‘s1.moved = s.moved’ by (qunabbrev_tac ‘s1’ >> simp[]) >> rfs[]]
QED

Theorem fin_inv_arrive:
  kinv s ∧ fin_inv s ∧ is_end s (k, j) ∧ s.peer (k, j) = NONE ∧
  (a = LData j d ∨ a = LEof j) ∧ ¬(sys_chan s (k, j)).connecting ⇒
  fin_inv (sys_deliver k a s)
Proof
  disch_then (fn th => MAP_EVERY ASSUME_TAC (CONJUNCTS th)) >> ‘k < LENGTH s.procs’ by fs[is_end_def] >>
  qspecl_then [‘k’, ‘s’, ‘a’, ‘j’, ‘d’] mp_tac
    (Q.GENL [‘k'’, ‘s’, ‘a’, ‘j'’, ‘d’] deliver_de_facts) >>
  simp[] >> strip_tac >>
  ‘∀e. s.peer e ≠ SOME (k, j)’ by (rpt strip_tac >> metis_tac[kinv_peer_end, NOT_NONE_SOME]) >>
  qpat_x_assum ‘fin_inv s’ (strip_assume_tac o REWRITE_RULE [fin_inv_def]) >>
  PURE_REWRITE_TAC [fin_inv_def] >> rpt conj_tac >> rpt gen_tac >| [
    simp[] >> metis_tac[],
    simp[] >> strip_tac >> ‘is_end s e’ by metis_tac[] >> metis_tac[],
    simp[] >> strip_tac >> ‘is_end s e' ∧ e' ≠ (k, j)’ by metis_tac[kinv_peer_end] >>
    metis_tac[],
    simp[] >> strip_tac >>
    ‘is_end s e ∧ is_end s e' ∧ e' ≠ (k, j)’ by metis_tac[kinv_peer_end] >>
    first_x_assum (qspecl_then [‘e’, ‘e'’] mp_tac) >> simp[] >> metis_tac[]]
QED

(*---------------------------------------------------------------------------*)
(* fin_inv along a run *)

Theorem skeep_with_procs:
  k < LENGTH s.procs ∧ wkeep (EL k s.procs) w ⇒
  skeep s (s with <| procs := LUPDATE w k s.procs; target := T1 |>)
Proof
  strip_tac >> drule_all skeep_local >> simp[skeep_def]
QED

Theorem fin_inv_step:
  kinv s ∧ kinv s' ∧ fin_inv s ∧ sys_ext s s' ∧ sys_step s r s' ⇒ fin_inv s'
Proof
  strip_tac >>
  ‘skeep s s' ⇒ fin_inv s'’ by metis_tac[fin_inv_skeep] >>
  Cases_on ‘r’
  >- ((* Call *)
      first_x_assum irule >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def, LET_THM] >> strip_tac >>
      ‘∀c h. wkeep (EL n s.procs) (w1 with <| clock := c; hist := h |>)’ by
        (rpt gen_tac >> irule (cj 4 wkeep_fields) >> drule wkeep_call >> simp[]) >>
      every_case_tac >> gvs[] >>
      FIRST [irule skeep_local >> fs[] >> NO_TAC,
             irule skeep_with_procs >> fs[] >> NO_TAC,
             irule skeep_trans >> irule_at (Pos last) skeep_pair >> rpt conj_tac >>
             FIRST [fs[sys_room_def] >> NO_TAC, irule skeep_with_procs >> fs[]]])
  >- ((* Kern *)
      rename1 ‘Kern kk’ >> Cases_on ‘kk’ >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def] >> strip_tac >> gvs[]
      >- (first_x_assum irule >> irule skeep_trans >>
          qexists_tac ‘sys_deliver n (LConnUp n0) s’ >>
          ‘n < LENGTH s.procs ∧ n1 < LENGTH s.procs’ by fs[is_end_def, sys_room_def] >>
          simp[skeep_deliver] >> irule skeep_pair >> fs[sys_room_def])
      >- (‘n1 + s.moved (n, n0) = s.moved (n, n0) + n1’ by simp[] >>
          pop_assum SUBST1_TAC >> irule fin_inv_move >> simp[])
      >- (first_x_assum irule >> ‘n < LENGTH s.procs’ by fs[is_end_def] >>
          simp[skeep_deliver])
      >- (irule fin_inv_fin >> simp[])
      >- (first_x_assum irule >> ‘n < LENGTH s.procs’ by fs[is_end_def] >>
          simp[skeep_deliver])
      >> first_x_assum irule >> ‘n < LENGTH s.procs’ by fs[is_end_def] >> simp[skeep_deliver])
  >- ((* Env *)
      rename1 ‘Env ee’ >> Cases_on ‘ee’ >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def] >> strip_tac >> gvs[]
      >- (first_x_assum irule >> fs[sys_room_def] >> simp[skeep_deliver])
      >- (first_x_assum irule >> ‘n < LENGTH s.procs’ by fs[is_end_def] >>
          simp[skeep_deliver]) >>
      Cases_on ‘l’ >> gvs[env_arrival_chan_def]
      >- (irule fin_inv_arrive >> simp[] >> metis_tac[])
      >- (irule fin_inv_arrive >> simp[] >> metis_tac[])
      >> first_x_assum irule >> ‘n < LENGTH s.procs’ by fs[is_end_def] >> simp[skeep_deliver])
  >> (* Exit *)
  first_x_assum irule >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >> simp[sys_step_def] >>
  strip_tac >> gvs[] >>
  ‘skeep s (s with procs := LUPDATE (close_all (EL n s.procs)) n s.procs)’ by
    (irule skeep_local >> simp[wkeep_close_all]) >>
  fs[skeep_def]
QED

Theorem fin_inv_init:
  sys_init ps s ⇒ fin_inv s
Proof
  rw[sys_init_def, fin_inv_def, LET_THM] >> Cases_on ‘e’ >> fs[is_end_def, sys_chan_def] >>
  ‘(EL q s.procs).chans = []’ by metis_tac[] >> fs[]
QED

Theorem irun_fin_inv:
  l0sys_irun ps ss rs ⇒ ∀n. fin_inv (ss n)
Proof
  strip_tac >> Induct
  >- (irule fin_inv_init >> fs[l0sys_irun_def] >> metis_tac[]) >>
  ‘kinv (ss n) ∧ kinv (ss (SUC n)) ∧ sys_ext (ss n) (ss (SUC n)) ∧
   sys_step (ss n) (rs n) (ss (SUC n))’ by metis_tac[irun_kinv, irun_ext, l0sys_irun_def] >>
  metis_tac[fin_inv_step]
QED

(*---------------------------------------------------------------------------*)
(* What an end has sent only grows *)

Definition sent_keep_def:
  sent_keep (s : sysstate) s' ⇔
    ∀e. is_end s e ⇒ is_end s' e ∧ (sys_chan s e).sent ≼ (sys_chan s' e).sent
End

Theorem skeep_sent_keep:
  skeep s s' ⇒ sent_keep s s'
Proof
  rw[sent_keep_def] >> drule_all skeep_end >> rw[ckeep_def]
QED

Theorem deliver_sent_keep:
  k' < LENGTH s.procs ∧ (a = LData j' d ∨ a = LEof j') ⇒
  sent_keep s (sys_deliver k' a s with <| moved := M; finned := FN |>) ∧
  sent_keep s (sys_deliver k' a s with moved := M) ∧
  sent_keep s (sys_deliver k' a s with finned := FN) ∧
  sent_keep s (sys_deliver k' a s)
Proof
  disch_then (fn th => MAP_EVERY ASSUME_TAC (CONJUNCTS th)) >>
  qspecl_then [‘k'’, ‘s’, ‘a’, ‘j'’, ‘d’] mp_tac
    (Q.GENL [‘k'’, ‘s’, ‘a’, ‘j'’, ‘d’] deliver_de_facts) >>
  simp[] >> strip_tac >> rw[sent_keep_def]
QED

Theorem step_sent_keep:
  kinv s ∧ sys_step s r s' ⇒ sent_keep s s'
Proof
  strip_tac >> Cases_on ‘r’
  >- (irule skeep_sent_keep >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def, LET_THM] >> strip_tac >>
      ‘∀c h. wkeep (EL n s.procs) (w1 with <| clock := c; hist := h |>)’ by
        (rpt gen_tac >> irule (cj 4 wkeep_fields) >> drule wkeep_call >> simp[]) >>
      every_case_tac >> gvs[] >>
      FIRST [irule skeep_local >> fs[] >> NO_TAC,
             irule skeep_with_procs >> fs[] >> NO_TAC,
             irule skeep_trans >> irule_at (Pos last) skeep_pair >> rpt conj_tac >>
             FIRST [fs[sys_room_def] >> NO_TAC, irule skeep_with_procs >> fs[]]])
  >- (rename1 ‘Kern kk’ >> Cases_on ‘kk’ >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def] >> strip_tac >> gvs[] >>
      TRY (‘n < LENGTH s.procs’ by fs[is_end_def]) >>
      TRY (rename1 ‘s.peer (n, n0) = SOME (k', j')’ >>
           ‘k' < LENGTH s.procs’ by (drule_all kinv_peer_end >> simp[is_end_def])) >>
      FIRST [
        irule skeep_sent_keep >> irule skeep_trans >>
        qexists_tac ‘sys_deliver n (LConnUp n0) s’ >>
        ‘n1 < LENGTH s.procs’ by fs[sys_room_def] >>
        simp[skeep_deliver] >> irule skeep_pair >> fs[sys_room_def] >> NO_TAC,
        metis_tac[deliver_sent_keep],
        irule skeep_sent_keep >> simp[skeep_deliver]])
  >- (rename1 ‘Env ee’ >> Cases_on ‘ee’ >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >>
      simp[sys_step_def] >> strip_tac >> gvs[]
      >- (irule skeep_sent_keep >> fs[sys_room_def] >> simp[skeep_deliver])
      >- (irule skeep_sent_keep >> ‘n < LENGTH s.procs’ by fs[is_end_def] >>
          simp[skeep_deliver]) >>
      ‘n < LENGTH s.procs’ by fs[is_end_def] >>
      Cases_on ‘l’ >> gvs[env_arrival_chan_def] >>
      TRY (metis_tac[deliver_sent_keep]) >>
      irule skeep_sent_keep >> simp[skeep_deliver])
  >> irule skeep_sent_keep >> qpat_x_assum ‘sys_step _ _ _’ mp_tac >> simp[sys_step_def] >>
  strip_tac >> gvs[] >>
  ‘skeep s (s with procs := LUPDATE (close_all (EL n s.procs)) n s.procs)’ by
    (irule skeep_local >> simp[wkeep_close_all]) >>
  fs[skeep_def]
QED

Theorem irun_sent_mono:
  l0sys_irun ps ss rs ∧ is_end (ss n) e ∧ n ≤ n' ⇒
  is_end (ss n') e ∧ (sys_chan (ss n) e).sent ≼ (sys_chan (ss n') e).sent
Proof
  strip_tac >>
  ‘∀d. is_end (ss (n + d)) e ∧ (sys_chan (ss n) e).sent ≼ (sys_chan (ss (n + d)) e).sent’
    suffices_by (disch_then (qspec_then ‘n' − n’ mp_tac) >> simp[]) >>
  Induct >> simp[] >>
  ‘sent_keep (ss (n + d)) (ss (SUC (n + d)))’ by
    (‘kinv (ss (n + d))’ by metis_tac[irun_kinv] >>
     ‘sys_step (ss (n + d)) (rs (n + d)) (ss (SUC (n + d)))’ by fs[l0sys_irun_def] >>
     drule_all step_sent_keep >> simp[]) >>
  fs[sent_keep_def, ADD_CLAUSES] >> metis_tac[IS_PREFIX_TRANS]
QED

(*---------------------------------------------------------------------------*)
(* N5b *)

Theorem kfo_delivery[local]:
  kernel_fair_obs ss rs ∧ io (asks_in ss rs k' j') ∧
  (∀n. n0 ≤ n ⇒ is_end (ss n) e ∧ (ss n).peer e = SOME (k', j') ∧
                (ss n).moved e < LENGTH (sys_chan (ss n) e).sent) ⇒ F
Proof
  strip_tac >>
  qpat_x_assum ‘kernel_fair_obs _ _’ (mp_tac o CONJUNCT1 o REWRITE_RULE [kernel_fair_obs_def]) >>
  disch_then (qspecl_then [‘e’, ‘k'’, ‘j'’, ‘n0’] mp_tac) >> simp[] >>
  fs[io_def, io_from_def]
QED

Theorem kinv_pair_facts[local]:
  kinv s ∧ s.peer e = SOME e' ⇒
  s.moved e ≤ LENGTH (sys_chan s e).sent ∧
  (frozen (sys_chan s e') ∨ (sys_chan s e').peer_sent = TAKE (s.moved e) (sys_chan s e).sent)
Proof
  rw[kinv_def] >> res_tac >> fs[]
QED

Theorem fin_inv_eof[local]:
  fin_inv s ∧ s.peer e = SOME e' ∧ (sys_chan s e').peer_eof ∧ ¬lostc (sys_chan s e') ⇒
  (sys_chan s e').peer_sent = (sys_chan s e).sent
Proof
  rw[fin_inv_def] >> res_tac >> res_tac >> fs[]
QED

Theorem sys_delivers:
  l0sys_irun ps ss rs ∧ kernel_fair_obs ss rs ∧
  (ss m).peer e = SOME (k', j') ∧ io (asks_in ss rs k' j') ⇒
  ev_ext_unless m (lost ss (k', j')) (sent_at ss e) (dlv_at ss (k', j'))
Proof
  rw[ev_ext_unless_def, sent_at_def, dlv_at_def, lost_def] >>
  ‘∀n'. m ≤ n' ⇒ (ss n').peer e = SOME (k', j') ∧ is_end (ss n') e’ by
    (rpt gen_tac >> strip_tac >>
     ‘(ss n').peer e = SOME (k', j')’ by
       (drule irun_mono >> disch_then (qspec_then ‘e’ mp_tac) >>
        disch_then (qspecl_then [‘m’, ‘n'’] mp_tac) >> simp[]) >>
     ‘kinv (ss n')’ by metis_tac[irun_kinv] >>
     drule_all kinv_peer_end >> simp[]) >>
  ‘∃n'. n ≤ n' ∧ LENGTH (sys_chan (ss n') e).sent ≤ (ss n').moved e’ by
    (CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
     ‘∀n''. n ≤ n'' ⇒ is_end (ss n'') e ∧ (ss n'').peer e = SOME (k', j') ∧
                      (ss n'').moved e < LENGTH (sys_chan (ss n'') e).sent’ by
       (rpt gen_tac >> strip_tac >>
        qpat_x_assum ‘∀n'. m ≤ n' ⇒ _’ (qspec_then ‘n''’ mp_tac) >>
        qpat_x_assum ‘∀n'. n' < n ∨ _’ (qspec_then ‘n''’ mp_tac) >> simp[]) >>
     drule_all kfo_delivery >> simp[]) >>
  qexists_tac ‘n'’ >> simp[] >>
  ‘(ss n').peer e = SOME (k', j') ∧ is_end (ss n) e’ by simp[] >>
  ‘(sys_chan (ss n) e).sent ≼ (sys_chan (ss n') e).sent’ by
    (qspecl_then [‘ps’, ‘ss’, ‘rs’, ‘n’, ‘e’, ‘n'’] mp_tac
       (Q.GENL [‘ps’, ‘ss’, ‘rs’, ‘n’, ‘e’, ‘n'’] irun_sent_mono) >> simp[]) >>
  ‘kinv (ss n') ∧ fin_inv (ss n')’ by metis_tac[irun_kinv, irun_fin_inv] >>
  qspecl_then [‘ss n'’, ‘e’, ‘(k', j')’] mp_tac
    (Q.GENL [‘s’, ‘e’, ‘e'’] kinv_pair_facts) >> simp[] >> strip_tac >>
  ‘(ss n').moved e = LENGTH (sys_chan (ss n') e).sent’ by simp[] >>
  Cases_on ‘lostc (sys_chan (ss n') (k', j'))’ >- fs[lostc_def] >>
  ‘(sys_chan (ss n') (k', j')).peer_sent = (sys_chan (ss n') e).sent’ suffices_by simp[] >>
  Cases_on ‘frozen (sys_chan (ss n') (k', j'))’ >- (
    ‘(sys_chan (ss n') (k', j')).peer_eof’ by (qpat_x_assum ‘¬lostc _’ mp_tac >> qpat_x_assum ‘frozen _’ mp_tac >>
        PURE_REWRITE_TAC [l0sysMonoTheory.frozen_def, lostc_def] >> metis_tac[]) >>
    irule fin_inv_eof >> simp[]) >>
  fs[TAKE_LENGTH_ID]
QED

Theorem sys_delivers_claim_holds:
  sys_delivers_claim
Proof
  rw[sys_delivers_claim_def] >> metis_tac[sys_delivers]
QED
