(*
  R2, action by action: in the simple world each L1 action does what the
  handle layer's hdo does, with the events renamed (l0_v2_event), up to
  "would block" events: where the round discipline lets L1 skip a syscall
  (an accept or read on a handle that the last poll did not report
  ready), the handle layer makes the call and records a would-block event.
  So L1's renamed events are the handle layer's with some would-block
  events deleted (drops).  Such events read no bytes and open no
  connection.
*)
Theory honestL1Steps
Ancestors
  honestL1Refine honestL1Model honestL1Simple honestL1Inv honestL0World
  honestL0WorldProps honestL0Rely honestL0 loopHandlesModel lifetimeWorld lifetimeProof
  socketWorld loopPollWorld Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   Events
   ------------------------------------------------------------------------ *)

(* What recv returned, as «sock_read»'s response *)
Definition recv_view_def:
  recv_view out =
    case l0_res_of out of
    | Ok k => if k = 0 then SOME [] else SOME (TAKE k (DROP 13 out))
    | Fail e _ => NONE
End

Definition poll_flag_def:
  poll_flag (b : word8) : word8 =
    if (byte_revents b).rin ∨ (byte_revents b).rhup ∨ (byte_revents b).rerr
    then 1w else 0w
End

(* The same from a revents field (D20) *)
Definition abi_flag_def:
  abi_flag (bs : word8 list) : word8 =
    if (abi_revents bs).rin ∨ (abi_revents bs).rhup ∨ (abi_revents bs).rerr
    then 1w else 0w
End

Theorem abi_flag_abi_rev[simp]:
  abi_flag (abi_rev b) = poll_flag b
Proof
  simp[abi_flag_def, poll_flag_def]
QED

(* An L0 event as the version-2 event it stands for *)
Definition l0_v2_event_def:
  l0_v2_event (IO_event (ExtCall n) conf bs) =
    (let out = MAP SND bs in
     if n = «sys_recv» then
       act_event (Read (bytes_fd conf) (LENGTH bs − 13)) (Got (recv_view out))
     else if n = «sys_send» then
       act_event (Write (bytes_fd (TAKE 8 conf)) (DROP 8 conf)) Wrote
     else if n = «sys_accept» then
       act_event (Accept (bytes_fd conf))
         (Accepted (case l0_res_of out of Ok f => SOME (n2w f) | Fail _ _ => NONE))
     else if n = «sys_close» then close_event (bytes_fd conf)
     else if n = «sys_poll» then
       (let ents = pollfd_entries (DROP 16 (MAP FST bs)) in
          IO_event (ExtCall «sock_poll») (fds_bytes (MAP pe_fd ents))
            (ZIP (REPLICATE (LENGTH ents) 0w,
                  MAP (λe. abi_flag (DROP 6 e)) (pollfd_entries (DROP 16 out)))))
     else IO_event (ExtCall n) conf bs) ∧
  l0_v2_event ev = ev
End

(* A version-2 event that reports "would block" *)
Definition wb_event_def:
  wb_event ev ⇔
    (∃l. ev = act_event (Accept l) (Accepted NONE)) ∨
    (∃f n. ev = act_event (Read f n) (Got NONE))
End

(* l is h with some would-block events deleted *)
Inductive drops:
  drops [] [] ∧
  (∀l h e. drops l h ∧ wb_event e ⇒ drops l (e :: h)) ∧
  (∀l h x. drops l h ⇒ drops (x :: l) (x :: h))
End

Theorem drops_refl[simp]:
  ∀l. drops l l
Proof
  Induct >> metis_tac[drops_rules]
QED

Theorem drops_APPEND:
  ∀a b. drops a b ⇒ ∀c d. drops c d ⇒ drops (a ++ c) (b ++ d)
Proof
  Induct_on ‘drops’ >> rw[] >> metis_tac[drops_rules]
QED

Theorem drops_wb:
  wb_event e ⇒ drops [] [e]
Proof
  metis_tac[drops_rules]
QED

(* ------------------------------------------------------------------------
   The lowest free fd
   ------------------------------------------------------------------------ *)

(* Among 0 .. LENGTH l some number is not in l *)
Theorem free_exists:
  LENGTH (l : word64 list) < dimword (:64) ⇒ ∃n. n ≤ LENGTH l ∧ ¬MEM (n2w n : word64) l
Proof
  strip_tac >> CCONTR_TAC >> gvs[] >>
  ‘set (GENLIST (λi. n2w i : word64) (SUC (LENGTH l))) ⊆ set l’
    by (simp[SUBSET_DEF, MEM_GENLIST, PULL_EXISTS] >> rw[] >>
        first_x_assum (qspec_then ‘i’ mp_tac) >> simp[]) >>
  ‘ALL_DISTINCT (GENLIST (λi. n2w i : word64) (SUC (LENGTH l)))’
    by (simp[ALL_DISTINCT_GENLIST] >> rw[] >> gvs[]) >>
  ‘CARD (set (GENLIST (λi. n2w i : word64) (SUC (LENGTH l)))) = SUC (LENGTH l)’
    by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  ‘CARD (set (GENLIST (λi. n2w i : word64) (SUC (LENGTH l)))) ≤ CARD (set l)’
    by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (set l) ≤ LENGTH l’ by simp[CARD_LIST_TO_SET] >>
  decide_tac
QED

Theorem lowest_n_bound:
  LENGTH (l : word64 list) < dimword (:64) ⇒
  (LEAST n. ¬MEM (n2w n : word64) l) ≤ LENGTH l ∧ ¬MEM (n2w (LEAST n. ¬MEM (n2w n : word64) l) : word64) l
Proof
  strip_tac >> drule free_exists >> strip_tac >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rw[] >> CCONTR_TAC >> gvs[NOT_LESS_EQUAL] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED

Theorem lowest_fd_free:
  LENGTH (l0_used w) < dimword (:64) ⇒
  ¬MEM (lowest_fd w) (l0_used w) ∧ w2n (lowest_fd w) ≤ LENGTH (l0_used w)
Proof
  strip_tac >> drule lowest_n_bound >> strip_tac >> simp[lowest_fd_def] >>
  ‘(LEAST n. ¬MEM (n2w n : word64) (l0_used w)) < 18446744073709551616’
    by (fs[dimword_def] >> decide_tac) >>
  simp[LESS_MOD]
QED

(* ------------------------------------------------------------------------
   Handles
   ------------------------------------------------------------------------ *)

Theorem l1hdl_hdl[simp]:
  l1hdl lfd j = hdl lfd j ∧ l1hdln n j = hdln n j
Proof
  simp[l1hdl_def, hdl_def, l1hdln_def, hdln_def]
QED

Theorem l1hdl_11:
  l1hdln (w2n lfd) i < dimword (:64) ∧ l1hdln (w2n lfd) j < dimword (:64) ∧
  l1hdl lfd i = l1hdl lfd j ⇒ i = j
Proof
  simp[hdl_def, hdln_def] >> rw[] >> gvs[dimword_def, n2w_11] >>
  CCONTR_TAC >> gvs[LESS_MOD]
QED

(* The fds in use are the same lists in both worlds *)
Theorem used_fds_rel:
  core_rel p lfd w s ⇒ used_fds s = l0_used w
Proof
  rw[core_rel_def, used_fds_def, l0_used_def] >> simp[]
QED

Theorem lowest_free_fd:
  lowest_free (l0_used w) = lowest_fd w
Proof
  simp[lowest_free_def, lowest_fd_def]
QED

(* ------------------------------------------------------------------------
   The class and the rely survive calls
   ------------------------------------------------------------------------ *)

Theorem simple_v2_same:
  w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit ∧ w'.env = w.env ⇒
  (simple_v2 p lfd sched w' ⇔ simple_v2 p lfd sched w)
Proof
  rw[simple_v2_def, simple0_def]
QED

Theorem upd_lchan_env[simp]:
  (upd_lchan j g w).env = w.env
Proof
  simp[upd_lchan_def]
QED

Theorem FOLDL_upd_env[simp]:
  ∀q w. (FOLDL (λw j. upd_lchan j (g j) w) w q).env = w.env
Proof
  Induct >> simp[]
QED

Theorem close_fd_env[simp]:
  (close_fd f w).env = w.env
Proof
  rw[close_fd_def] >> every_case_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘FOLDL _ w0 q’ >>
  ‘∀q w0. (FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) w0 q).env = w0.env’
    by (Induct >> simp[]) >>
  simp[Abbr ‘w0’]
QED

Theorem deliver_env[simp]:
  (l0_deliver w a).env = w.env
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_env[simp]:
  ∀as w. (FOLDL l0_deliver w as).env = w.env
Proof
  Induct >> simp[]
QED

Theorem tick_env[simp]:
  (l0_tick nm w).env = w.env
Proof
  simp[l0_tick_def]
QED

Theorem ticks_env[simp]:
  ∀k w. (l0_ticks nm k w).env = w.env
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem ops_env:
  (l0_listen p w = (x, w') ⇒ w'.env = w.env) ∧
  (l0_accept l w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_recv f n w = (r, d, w') ⇒ w'.env = w.env) ∧
  (l0_send f bs w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_shutdown f w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_close f w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_connect p w = (r, v, w') ⇒ w'.env = w.env) ∧
  (l0_connerr f w = (y, w') ⇒ w'.env = w.env)
Proof
  rpt conj_tac >> rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def,
                     l0_shutdown_def, l0_close_def, l0_connect_def, l0_connerr_def,
                     AllCaseEqs()] >> gvs[]
QED

Theorem l0_call_env:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ w'.env = w.env
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac ops_env >> simp[]
QED

Theorem l0_do_env:
  l0_do n conf alen w = SOME (out, w', ev) ⇒ w'.env = w.env ∧ w'.ch = w.ch ∧
  w'.fd_limit = w.fd_limit
Proof
  rw[l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  imp_res_tac l0_call_ch >> imp_res_tac l0_call_env >> gvs[]
QED

Theorem l0_do_buf_env:
  l0_do_buf n conf bs w = SOME (out, w', ev) ⇒ w'.env = w.env ∧ w'.ch = w.ch ∧
  w'.fd_limit = w.fd_limit
Proof
  rw[l0_do_buf_def, l0_ffi_fn_def, AllCaseEqs()] >>
  imp_res_tac l0_call_ch >> imp_res_tac l0_call_env >> gvs[]
QED

(* ------------------------------------------------------------------------
   Accept
   ------------------------------------------------------------------------ *)

Theorem wb_accept_none[simp]:
  wb_event (act_event (Accept l) (Accepted NONE))
Proof
  simp[wb_event_def] >> metis_tac[]
QED

(* The listener was polled and found empty: L1 makes no call; the handle
   layer's accept says "would block" *)
Theorem accept_skip:
  l1v2_rel p lfd sched (w, st) (s, hs) ∧ rdy_ok lfd polp w st ∧
  MEM (lfd, lfd) polp ∧ ¬MEM lfd st.rdy ⇒
  l1do lfd (w, st) (Accept lfd) = SOME (Accepted NONE, (w, st), []) ∧
  hdo lfd (s, hs) (Accept lfd) =
    SOME (Accepted NONE, (s, hs), [act_event (Accept lfd) (Accepted NONE)]) ∧
  drops (MAP l0_v2_event []) [act_event (Accept lfd) (Accepted NONE)]
Proof
  rw[l1do_def] >> gvs[l1v2_rel_def, core_rel_def, rdy_ok_def] >>
  simp[hdo_def, sock_accept2_def] >> metis_tac[drops_wb, wb_accept_none]
QED

Theorem fd_bytes_lfd[simp]:
  bytes_fd (fd_bytes (l : word64)) = l
Proof
  simp[]
QED

Theorem l0_res_of_enc:
  l0_res_ok r ⇒ l0_res_of (enc_res r) = r
Proof
  rw[l0_res_of_def] >> drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >>
  simp[]
QED

Theorem MAP_SND_ZIP_REPLICATE:
  LENGTH out = n ⇒ MAP SND (ZIP (REPLICATE n x, out)) = out
Proof
  rw[] >> simp[MAP_ZIP]
QED

Theorem fail_ok:
  l0_rely w ⇒ l0_res_ok (fail w e)
Proof
  rw[fail_def, l0_res_ok_def, l0_rely_def]
QED

(* The listener is in L1's readable set: one sys_accept, as version 2's
   accept *)
Theorem accept_call:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  MEM lfd st.rdy ∧ small lfd ∧ LENGTH (l0_used w) < 2147483647 ∧
  hdln (w2n lfd) st.nxt < dimword (:64) ⇒
  ∃r w' st' s' hs' evs evs'.
    l1do lfd (w, st) (Accept lfd) = SOME (r, (w', st'), evs) ∧
    hdo lfd (s, hs) (Accept lfd) = SOME (r, (s', hs'), evs') ∧
    MAP l0_v2_event evs = evs'
Proof
  strip_tac >>
  ‘l0_tick «sys_accept» w = w with clock := w.clock + 1’
    by (drule tick_simple_v2 >> disch_then irule >> EVAL_TAC) >>
  gvs[l1v2_rel_def, core_rel_def, small_def] >>
  ‘w2n lfd < 2147483648’ by simp[] >>
  simp[l1do_def, sys_accept_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def,
       fd_ok_def, l0_accept_def] >>
  ‘w.ch.transient (w.hist) = NONE’ by gvs[simple_v2_def, simple0_def] >>
  ‘l0_rely (w with clock := w.clock + 1)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘used_fds s = l0_used w’ by gvs[used_fds_def, l0_used_def] >>
  drule_then strip_assume_tac fail_ok >>
  Cases_on ‘q’ >> gvs[]
  >- (‘∀e. l0_res_ok (fail (w with clock := w.clock + 1) e)’ by metis_tac[fail_ok] >>
      simp[l0_res_of_enc, LENGTH_enc_res, MAP_SND_ZIP_REPLICATE] >>
      simp[hdo_def, sock_accept2_def, l0_v2_event_def, fail_def] >>
      gvs[fail_def] >>
      ‘l0_res_ok (Fail E_AGAIN (w.ch.errno_of w.hist))’ by metis_tac[] >>
      imp_res_tac LENGTH_enc_res >> simp[MAP_SND_ZIP_REPLICATE, l0_res_of_enc])
  >> ‘h < LENGTH (w:l0world).chans ∧ ¬(EL h w.chans).broken’
    by (gvs[LIST_REL_EL_EQN, chan_rel_def] >> metis_tac[]) >>
  ‘LENGTH (l0_used w) < dimword (:64)’ by gvs[dimword_def] >>
  drule lowest_fd_free >> strip_tac >>
  ‘w2n (lowest_fd w) < 2147483648’ by decide_tac >>
  ‘(w with clock := w.clock + 1).fd_limit = 2147483648’ by gvs[simple_v2_def, simple0_def] >>
  simp[l0_alloc_def] >>
  ‘lowest_fd (w with clock := w.clock + 1) = lowest_fd w’ by simp[lowest_fd_def, l0_used_def] >>
  simp[] >>
  ‘l0_res_ok (Ok (w2n (lowest_fd w)))’ by simp[l0_res_ok_def] >>
  simp[l0_res_of_enc, LENGTH_enc_res, MAP_SND_ZIP_REPLICATE] >>
  simp[hdo_def, sock_accept2_def, l0_v2_event_def, lowest_free_fd] >>
  simp[l0_res_of_enc, LENGTH_enc_res, MAP_SND_ZIP_REPLICATE]
QED

Theorem hdl_not_lfd:
  hdln (w2n lfd) j < dimword (:64) ⇒ hdl lfd j ≠ lfd
Proof
  Cases_on ‘lfd’ >> simp[hdl_def, hdln_def] >> rw[] >> gvs[dimword_def, n2w_11]
QED

Theorem hdl_fresh:
  i < k ∧ hdln (w2n lfd) k < dimword (:64) ⇒ hdl lfd i ≠ hdl lfd k
Proof
  rw[hdl_def, hdln_def] >> gvs[dimword_def, n2w_11]
QED

Theorem open_used:
  ALOOKUP w.open_fds f ≠ NONE ⇒ MEM f (l0_used w)
Proof
  rw[l0_used_def] >> Cases_on ‘ALOOKUP w.open_fds f’ >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem accept_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  rdy_ok lfd polp w st ∧ MEM lfd st.rdy ∧ small lfd ∧ LENGTH (l0_used w) < 2147483647 ∧
  hdln (w2n lfd) st.nxt < dimword (:64) ⇒
  ∃r w' st' s' hs' evs evs'.
    l1do lfd (w, st) (Accept lfd) = SOME (r, (w', st'), evs) ∧
    hdo lfd (s, hs) (Accept lfd) = SOME (r, (s', hs'), evs') ∧
    MAP l0_v2_event evs = evs' ∧
    l1v2_rel p lfd sched (w', st') (s', hs') ∧ rdy_ok lfd polp w' st' ∧
    LENGTH (l0_used w') ≤ LENGTH (l0_used w) + 1 ∧
    w'.env = w.env ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >>
  ‘l0_tick «sys_accept» w = w with clock := w.clock + 1’
    by (drule tick_simple_v2 >> disch_then irule >> EVAL_TAC) >>
  qpat_x_assum ‘rdy_ok _ _ _ _’ mp_tac >>
  gvs[l1v2_rel_def, core_rel_def, small_def] >> strip_tac >>
  ‘w2n lfd < 2147483648’ by simp[] >>
  simp[l1do_def, sys_accept_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def,
       fd_ok_def, l0_accept_def] >>
  ‘w.ch.transient (w.hist) = NONE’ by gvs[simple_v2_def, simple0_def] >>
  ‘l0_rely (w with clock := w.clock + 1)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘used_fds s = l0_used w’ by gvs[used_fds_def, l0_used_def] >>
  drule_then strip_assume_tac fail_ok >>
  Cases_on ‘q’ >> gvs[]
  >- (‘∀e. l0_res_ok (fail (w with clock := w.clock + 1) e)’ by metis_tac[fail_ok] >>
      simp[l0_res_of_enc, LENGTH_enc_res, MAP_SND_ZIP_REPLICATE] >>
      simp[hdo_def, sock_accept2_def, l0_v2_event_def, fail_def] >>
      gvs[fail_def] >>
      ‘l0_res_ok (Fail E_AGAIN (w.ch.errno_of w.hist))’ by metis_tac[] >>
      imp_res_tac LENGTH_enc_res >> simp[MAP_SND_ZIP_REPLICATE, l0_res_of_enc] >>
      simp[npolls_snoc, l0_used_def] >> rpt conj_tac >- metis_tac[]
      >- metis_tac[]
      >> fs[rdy_ok_def, MEM_FILTER] >> rw[] >> metis_tac[])
  >> ‘h < LENGTH (w:l0world).chans ∧ ¬(EL h w.chans).broken’
    by (gvs[LIST_REL_EL_EQN, chan_rel_def] >> metis_tac[]) >>
  ‘LENGTH (l0_used w) < dimword (:64)’ by gvs[dimword_def] >>
  drule lowest_fd_free >> strip_tac >>
  ‘w2n (lowest_fd w) < 2147483648’ by decide_tac >>
  ‘(w with clock := w.clock + 1).fd_limit = 2147483648’ by gvs[simple_v2_def, simple0_def] >>
  simp[l0_alloc_def] >>
  ‘lowest_fd (w with clock := w.clock + 1) = lowest_fd w’ by simp[lowest_fd_def, l0_used_def] >>
  simp[] >>
  ‘l0_res_ok (Ok (w2n (lowest_fd w)))’ by simp[l0_res_ok_def] >>
  simp[l0_res_of_enc, LENGTH_enc_res, MAP_SND_ZIP_REPLICATE] >>
  simp[hdo_def, sock_accept2_def, l0_v2_event_def, lowest_free_fd] >>
  simp[l0_res_of_enc, LENGTH_enc_res, MAP_SND_ZIP_REPLICATE] >>
  ‘MEM lfd (l0_used w)’ by simp[l0_used_def] >>
  ‘∀f. ALOOKUP s.open_fds f ≠ NONE ⇒ MEM f (l0_used w)’ by metis_tac[open_used] >>
  ‘hdl lfd hs.nxt ≠ lfd’ by (irule hdl_not_lfd >> simp[]) >>
  ‘∀i. i < hs.nxt ⇒ hdl lfd i ≠ hdl lfd hs.nxt’ by (rw[] >> irule hdl_fresh >> simp[]) >>
  simp[AFUPDKEY_def, npolls_snoc, l0_used_def] >>
  rpt conj_tac >>
  TRY (rw[] >> gvs[] >> metis_tac[DECIDE “(i:num) < n ⇒ i < n + 1”] >> NO_TAC) >>
  gvs[rdy_ok_def] >> rw[] >> gvs[] >>
  TRY (metis_tac[] >> NO_TAC) >>
  TRY (qexists_tac ‘hs.nxt’ >> simp[] >> NO_TAC) >>
  res_tac >> gvs[] >> qexists_tac ‘i’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Write
   ------------------------------------------------------------------------ *)

Definition fds_small_def:
  fds_small (w : l0world) ⇔ ∀f. MEM f (l0_used w) ⇒ w2n f < 2147483648
End

Theorem fds_small_tbl:
  l1v2_rel p lfd sched (w, st) (s, hs) ∧ fds_small w ∧ ALOOKUP st.tbl h = SOME f ⇒
  w2n f < 2147483648
Proof
  rw[l1v2_rel_def, fds_small_def] >> first_x_assum irule >> irule open_used >>
  gvs[core_rel_def] >> metis_tac[]
QED

(* The round discipline only looks at open fds, the listener and each
   channel's input and EOF *)
Theorem rdy_ok_same:
  rdy_ok lfd polp w st ∧ w'.open_fds = w.open_fds ∧ w'.listeners = w.listeners ∧
  (∀k. ((EL k w.chans).inbox = [] ⇒ (EL k w'.chans).inbox = []) ∧
       (EL k w'.chans).peer_eof = (EL k w.chans).peer_eof) ⇒
  rdy_ok lfd polp w' st
Proof
  rw[rdy_ok_def] >> metis_tac[]
QED

(* In the simple world a Write is the handle layer's write *)
Theorem write_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  rdy_ok lfd polp w st ∧ fds_small w ∧ LENGTH bs < 256 ** 8 ⇒
  ∃w' st' s' hs' evs evs'.
    l1do lfd (w, st) (Write h bs) = SOME (Wrote, (w', st'), evs) ∧
    hdo lfd (s, hs) (Write h bs) = SOME (Wrote, (s', hs'), evs') ∧
    MAP l0_v2_event evs = evs' ∧
    l1v2_rel p lfd sched (w', st') (s', hs') ∧ rdy_ok lfd polp w' st' ∧
    l0_used w' = l0_used w ∧
    w'.env = w.env ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >> simp[l1do_def, hdo_def] >>
  ‘st.tbl = hs.tbl ∧ st.gone = [] ∧ st.outbox = []’ by gvs[l1v2_rel_def] >>
  Cases_on ‘ALOOKUP st.tbl h’ >> gvs[] >>
  rename1 ‘ALOOKUP _ h = SOME f’ >>
  ‘w2n f < 2147483648’ by metis_tac[fds_small_tbl] >>
  ‘∃j. ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧ ¬(EL j w.chans).closed’
    by (gvs[l1v2_rel_def, core_rel_def] >> Cases_on ‘ALOOKUP s.open_fds f’ >>
        gvs[] >> metis_tac[]) >>
  ‘chan_rel (EL j w.chans) (EL j s.clients)’ by gvs[l1v2_rel_def, core_rel_def, LIST_REL_EL_EQN] >>
  ‘¬(EL j w.chans).broken ∧ ¬(EL j w.chans).shut ∧ ¬(EL j w.chans).connecting’
    by gvs[chan_rel_def] >>
  ‘l0_tick «sys_send» w = w with clock := w.clock + 1’
    by (drule tick_simple_v2 >> disch_then irule >> EVAL_TAC) >>
  ‘outbox_of st f = []’ by simp[outbox_of_def] >>
  simp[sys_send_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def, fd_ok_def,
       l0_send_def, l0_chan_of_def] >>
  ‘w.ch.transient w.hist = NONE ∧ ∀j h b n. w.ch.takes j h b n = n’
    by gvs[simple_v2_def, simple0_def] >>
  simp[] >>
  ‘l0_res_ok (Ok (LENGTH bs))’ by simp[l0_res_ok_def] >>
  simp[l0_res_of_enc, LENGTH_enc_res, MAP_SND_ZIP_REPLICATE] >>
  ‘LENGTH s.clients = LENGTH w.chans ∧ w.open_fds = s.open_fds’
    by gvs[l1v2_rel_def, core_rel_def, LIST_REL_EL_EQN] >>
  simp[sock_write2_def, client_of_def] >>
  IF_CASES_TAC >- gvs[] >>
  ‘l0_res_of (enc_res (Ok (LENGTH bs))) = Ok (LENGTH bs)’ by simp[l0_res_of_enc] >>
  ‘after_send f (Ok (LENGTH bs)) (set_outbox f bs st) = st’
    by (simp[after_send_def, set_outbox_def, outbox_of_def] >>
        Cases_on ‘bs’ >> simp[ADELKEY_def, honestL1ModelTheory.l1st_component_equality]) >>
  ‘«sys_send» ≠ «sys_recv» ∧ «sys_send» ≠ «sys_poll»’ by EVAL_TAC >>
  simp[l0_v2_event_def, TAKE_DROP_fd_bytes] >>
  gvs[l1v2_rel_def, npolls_snoc, l0_used_def] >>
  rpt conj_tac
  >- (irule core_rel_upd >> simp[] >> gvs[chan_rel_def])
  >- simp[update_client_def]
  >- (simp[upd_lchan_def] >> metis_tac[])
  >- (irule rdy_ok_same >> qexists_tac ‘w’ >>
      simp[upd_lchan_def, EL_LUPDATE] >> rw[])
  >> simp[upd_lchan_def]
QED

(* ------------------------------------------------------------------------
   Read
   ------------------------------------------------------------------------ *)

Theorem wb_read_none[simp]:
  wb_event (act_event (Read f n) (Got NONE))
Proof
  simp[wb_event_def] >> metis_tac[]
QED

Theorem tbl_open_chan:
  l1v2_rel p lfd sched (w, st) (s, hs) ∧ ALOOKUP st.tbl h = SOME f ⇒
  ∃j. ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧ ¬(EL j w.chans).closed ∧
      chan_rel (EL j w.chans) (EL j s.clients) ∧ client_of s f = SOME j ∧
      ¬(EL j w.chans).connecting
Proof
  rw[l1v2_rel_def, core_rel_def] >>
  ‘ALOOKUP s.open_fds f ≠ NONE’ by metis_tac[] >>
  Cases_on ‘ALOOKUP s.open_fds f’ >> gvs[] >>
  imp_res_tac LIST_REL_LENGTH >> gvs[LIST_REL_EL_EQN, client_of_def] >>
  metis_tac[chan_rel_def]
QED

(* A polled handle whose fd was not readable: L1 makes no call; the handle
   layer's read would block *)
Theorem read_skip:
  l1v2_rel p lfd sched (w, st) (s, hs) ∧ rdy_ok lfd polp w st ∧
  0 < n ∧ n < 256 ** 8 ∧ ALOOKUP st.tbl h = SOME f ∧ MEM (h, f) polp ∧
  ¬MEM f st.rdy ⇒
  l1do lfd (w, st) (Read h n) = SOME (Got NONE, (w, st), []) ∧
  hdo lfd (s, hs) (Read h n) = SOME (Got NONE, (s, hs), [act_event (Read f n) (Got NONE)]) ∧
  drops (MAP l0_v2_event []) [act_event (Read f n) (Got NONE)]
Proof
  strip_tac >> drule_all tbl_open_chan >> strip_tac >>
  ‘st.gone = [] ∧ st.tbl = hs.tbl’ by gvs[l1v2_rel_def] >>
  ‘(EL j w.chans).inbox = [] ∧ ¬(EL j w.chans).peer_eof’ by (gvs[rdy_ok_def] >> metis_tac[]) >>
  gvs[chan_rel_def] >>
  simp[l1do_def, hdo_def, sock_read2_def] >> metis_tac[drops_wb, wb_read_none]
QED

Theorem LENGTH_enc_res_ok13[local]:
  LENGTH (enc_res (Ok n)) = 13
Proof
  simp[enc_res_def, LENGTH_n2w8]
QED

(* A readable fd with input: one recv, the data version 2's read returns *)
Theorem read_data_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  rdy_ok lfd polp w st ∧ fds_small w ∧ 0 < n ∧ n < 256 ** 8 ∧
  ALOOKUP st.tbl h = SOME f ∧ MEM f st.rdy ∧ ALOOKUP w.open_fds f = SOME j ∧
  (EL j w.chans).inbox ≠ [] ⇒
  ∃w' s' evs.
    l1do lfd (w, st) (Read h n) =
      SOME (Got (SOME (TAKE n (EL j w.chans).inbox)), (w', st), evs) ∧
    hdo lfd (s, hs) (Read h n) =
      SOME (Got (SOME (TAKE n (EL j w.chans).inbox)), (s', hs), MAP l0_v2_event evs) ∧
    l1v2_rel p lfd sched (w', st) (s', hs) ∧ rdy_ok lfd polp w' st ∧
    l0_used w' = l0_used w ∧ w'.env = w.env ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >> drule_all tbl_open_chan >> strip_tac >> gvs[] >>
  ‘st.gone = [] ∧ st.tbl = hs.tbl’ by gvs[l1v2_rel_def] >>
  ‘w2n f < 2147483648’ by metis_tac[fds_small_tbl] >>
  ‘l0_tick «sys_recv» w = w with clock := w.clock + 1’
    by (drule tick_simple_v2 >> disch_then irule >> EVAL_TAC) >>
  ‘l0_recv f n (w with clock := w.clock + 1) =
     (Ok (MIN n (LENGTH (EL j w.chans).inbox)), TAKE n (EL j w.chans).inbox,
      upd_lchan j (λc. c with inbox := DROP n c.inbox) (w with clock := w.clock + 1))’
    by (mp_tac (Q.INST [‘w’ |-> ‘w with clock := w.clock + 1’] l0_recv_data) >>
        gvs[simple_v2_def, simple0_def, l0_chan_of_def]) >>
  qabbrev_tac ‘inb = (EL j w.chans).inbox’ >>
  qabbrev_tac ‘k = MIN n (LENGTH inb)’ >>
  ‘0 < k ∧ k < 256 ** 8’ by (unabbrev_all_tac >> Cases_on ‘(EL j w.chans).inbox’ >>
                             gvs[MIN_DEF]) >>
  ‘∀rest. l0_res_of (enc_res (Ok k) ++ rest) = Ok k’ by simp[l0_res_of_ok_app] >>
  ‘LENGTH (TAKE n inb) = k’ by simp[Abbr ‘k’, LENGTH_TAKE_MIN] >>
  ‘TAKE k (TAKE n inb) = TAKE n inb’ by metis_tac[TAKE_LENGTH_ID] >>
  simp[l1do_def, sys_recv_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def,
       fd_ok_def] >>
  qmatch_goalsub_abbrev_tac ‘l0_res_of out’ >>
  ‘l0_res_of out = Ok k’ by (simp[Abbr ‘out’] >> metis_tac[APPEND_ASSOC]) >>
  ‘LENGTH out = n + 13’ by (simp[Abbr ‘out’, LENGTH_enc_res_ok13] >> simp[Abbr ‘k’, MIN_DEF]) >>
  ‘TAKE k (DROP 13 out) = TAKE n inb’
    by (simp[Abbr ‘out’] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
        simp[DROP_APPEND, LENGTH_enc_res_ok13, TAKE_APPEND] >>
        simp[DROP_LENGTH_TOO_LONG, LENGTH_enc_res_ok13]) >>
  simp[hdo_def, sock_read2_def] >>
  gvs[chan_rel_def] >>
  ‘«sys_recv» ≠ «sys_poll»’ by EVAL_TAC >>
  simp[l0_v2_event_def, MAP_SND_ZIP_REPLICATE, recv_view_def] >>
  Cases_on ‘TAKE n s.clients❲j❳.incoming’ >> gvs[] >>
  gvs[l1v2_rel_def, npolls_snoc, l0_used_def] >>
  rpt conj_tac
  >- (irule core_rel_upd >> simp[] >> gvs[chan_rel_def])
  >- simp[update_client_def]
  >- (simp[upd_lchan_def] >> metis_tac[])
  >- (irule rdy_ok_same >> qexists_tac ‘w’ >>
      simp[upd_lchan_def, EL_LUPDATE] >> rw[])
  >> simp[upd_lchan_def]
QED

Theorem l0_res_of_enc_app:
  l0_res_ok r ⇒ l0_res_of (enc_res r ++ rest) = r
Proof
  rw[l0_res_of_def] >> drule dec_enc_res >> disch_then (qspec_then ‘rest’ mp_tac) >>
  simp[]
QED

(* The discipline survives: the table, the readable set and the open fds
   may only lose entries (an fd leaving the readable set leaves the table
   too), and no channel's input or EOF changes *)
Theorem rdy_ok_shrink:
  rdy_ok lfd polp w st ∧ w'.listeners = w.listeners ∧ st'.nxt = st.nxt ∧
  (∀h f. ALOOKUP st'.tbl h = SOME f ⇒ ALOOKUP st.tbl h = SOME f ∧
                                       (¬MEM f st'.rdy ⇒ ¬MEM f st.rdy)) ∧
  (MEM lfd st.rdy ⇒ MEM lfd st'.rdy) ∧
  (∀f j. ALOOKUP w'.open_fds f = SOME j ⇒ ALOOKUP w.open_fds f = SOME j) ∧
  (∀k. (EL k w'.chans).inbox = (EL k w.chans).inbox ∧
       (EL k w'.chans).peer_eof = (EL k w.chans).peer_eof) ⇒
  rdy_ok lfd polp w' st'
Proof
  rw[rdy_ok_def] >> metis_tac[]
QED

(* A readable fd found empty: EAGAIN, as version 2's read; the fd leaves
   L1's readable set *)
Theorem read_empty_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  rdy_ok lfd polp w st ∧ fds_small w ∧ 0 < n ∧ n < 256 ** 8 ∧
  ALOOKUP st.tbl h = SOME f ∧ MEM f st.rdy ∧ ALOOKUP w.open_fds f = SOME j ∧
  (EL j w.chans).inbox = [] ∧ ¬(EL j w.chans).peer_eof ⇒
  ∃w' st' evs.
    l1do lfd (w, st) (Read h n) = SOME (Got NONE, (w', st'), evs) ∧
    hdo lfd (s, hs) (Read h n) = SOME (Got NONE, (s, hs), MAP l0_v2_event evs) ∧
    l1v2_rel p lfd sched (w', st') (s, hs) ∧ rdy_ok lfd polp w' st' ∧
    l0_used w' = l0_used w ∧ w'.env = w.env ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >> drule_all tbl_open_chan >> strip_tac >> gvs[] >>
  ‘st.gone = [] ∧ st.tbl = hs.tbl’ by gvs[l1v2_rel_def] >>
  ‘w2n f < 2147483648’ by metis_tac[fds_small_tbl] >>
  ‘l0_tick «sys_recv» w = w with clock := w.clock + 1’
    by (drule tick_simple_v2 >> disch_then irule >> EVAL_TAC) >>
  ‘w.ch.transient w.hist = NONE’ by gvs[simple_v2_def, simple0_def] >>
  gvs[chan_rel_def] >>
  ‘l0_res_ok (fail (w with clock := w.clock + 1) E_AGAIN)’
    by (irule fail_ok >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  simp[l1do_def, sys_recv_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def,
       fd_ok_def, l0_recv_def, l0_chan_of_def] >>
  qabbrev_tac ‘raw = w.ch.errno_of w.hist’ >>
  ‘l0_res_ok (Fail E_AGAIN raw)’ by gvs[fail_def, Abbr ‘raw’] >>
  ‘∀rest. l0_res_of (enc_res (Fail E_AGAIN raw) ++ rest) = Fail E_AGAIN raw’
    by simp[l0_res_of_enc_app] >>
  ‘LENGTH (enc_res (Fail E_AGAIN raw)) = 13’ by simp[LENGTH_enc_res] >>
  simp[fail_def, l1_transient_def] >>
  simp[hdo_def, sock_read2_def] >>
  ‘«sys_recv» ≠ «sys_poll»’ by EVAL_TAC >>
  simp[l0_v2_event_def, MAP_SND_ZIP_REPLICATE, recv_view_def] >>
  gvs[l1v2_rel_def, npolls_snoc, l0_used_def] >>
  gvs[rdy_ok_def, MEM_FILTER] >> rw[] >> gvs[] >>
  TRY (Cases_on ‘f' = f’ >> gvs[]) >> metis_tac[]
QED

Theorem l0_used_clock_hist[simp]:
  l0_used (w with clock := c) = l0_used w ∧ l0_used (w with hist := hh) = l0_used w
Proof
  simp[l0_used_def]
QED

(* A readable fd at EOF: one recv (0) and one close, as version 2's read
   at EOF and the handle layer's auto-close *)
Theorem read_eof_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  rdy_ok lfd polp w st ∧ fds_small w ∧ 0 < n ∧ n < 256 ** 8 ∧
  ALOOKUP st.tbl h = SOME f ∧ MEM f st.rdy ∧ ALOOKUP w.open_fds f = SOME j ∧
  (EL j w.chans).inbox = [] ∧ (EL j w.chans).peer_eof ⇒
  ∃w' st' s' hs' evs.
    l1do lfd (w, st) (Read h n) = SOME (Got (SOME []), (w', st'), evs) ∧
    hdo lfd (s, hs) (Read h n) = SOME (Got (SOME []), (s', hs'), MAP l0_v2_event evs) ∧
    l1v2_rel p lfd sched (w', st') (s', hs') ∧ rdy_ok lfd polp w' st' ∧
    (∀x. MEM x (l0_used w') ⇒ MEM x (l0_used w)) ∧
    LENGTH (l0_used w') ≤ LENGTH (l0_used w) ∧
    w'.env = w.env ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >> drule_all tbl_open_chan >> strip_tac >> gvs[] >>
  ‘st.gone = [] ∧ st.tbl = hs.tbl ∧ st.outbox = []’ by gvs[l1v2_rel_def] >>
  ‘w2n f < 2147483648’ by metis_tac[fds_small_tbl] >>
  ‘l0_tick «sys_recv» w = w with clock := w.clock + 1’
    by (drule tick_simple_v2 >> disch_then irule >> EVAL_TAC) >>
  ‘∀w1. w1.env = w.env ⇒ l0_tick «sys_close» w1 = w1 with clock := w1.clock + 1’
    by (rw[l0_tick_def] >> gvs[simple_v2_def] >> EVAL_TAC) >>
  ‘w.ch.transient w.hist = NONE ∧ ∀h. w.ch.close_intr h = NONE’
    by gvs[simple_v2_def, simple0_def] >>
  gvs[chan_rel_def] >>
  ‘l0_res_ok (Ok 0)’ by simp[l0_res_ok_def] >>
  ‘∀rest. l0_res_of (enc_res (Ok 0) ++ rest) = Ok 0’ by simp[l0_res_of_enc_app] >>
  ‘LENGTH (enc_res (Ok 0)) = 13’ by simp[LENGTH_enc_res] >>
  ‘MEM f (l0_used w)’ by (irule open_used >> simp[]) >>
  simp[l1do_def, sys_recv_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def,
       fd_ok_def, l0_recv_def, l0_chan_of_def, outbox_of_def] >>
  simp[l1_close_def, sys_close_def, l0_do_def, l0_ffi_fn_def, l0_call_def,
       l0_hdr_def, fd_ok_def, l0_close_def, close_fd_def, l0_chan_of_def] >>
  simp[hdo_def, sock_read2_def, sock_close2_def] >>
  ‘«sys_recv» ≠ «sys_poll» ∧ «sys_close» ≠ «sys_poll» ∧ «sys_close» ≠ «sys_recv» ∧
   «sys_close» ≠ «sys_send» ∧ «sys_close» ≠ «sys_accept»’ by EVAL_TAC >>
  simp[l0_v2_event_def, MAP_SND_ZIP_REPLICATE, recv_view_def] >>
  ‘∀h'. ALOOKUP hs.tbl h' = SOME f ⇒ h' = h’ by (gvs[l1v2_rel_def] >> metis_tac[]) >>
  ‘f ≠ lfd’ by (gvs[l1v2_rel_def] >> metis_tac[]) >>
  rpt conj_tac
  >- (qpat_x_assum ‘l1v2_rel _ _ _ _ _’ mp_tac >>
      simp[l1v2_rel_def, forget_def, set_outbox_def, npolls_snoc, ALOOKUP_ADELKEY] >>
      strip_tac >> rpt conj_tac >>
      TRY (simp[ADELKEY_def] >> NO_TAC) >>
      TRY (rw[] >> gvs[upd_lchan_def, ALOOKUP_ADELKEY] >> metis_tac[] >> NO_TAC) >>
      qpat_x_assum ‘core_rel _ _ _ _’ mp_tac >>
      simp[core_rel_def, upd_lchan_def, EL_LUPDATE, LIST_REL_EL_EQN, ALOOKUP_ADELKEY] >>
      strip_tac >> rpt conj_tac >> rw[] >> gvs[EVERY_MEM, chan_rel_def] >>
      rw[] >> gvs[EL_LUPDATE] >> metis_tac[])
  >- (irule rdy_ok_shrink >> qexists_tac ‘st’ >> qexists_tac ‘w’ >>
      simp[forget_def, set_outbox_def, upd_lchan_def, EL_LUPDATE, ALOOKUP_ADELKEY,
           MEM_FILTER] >>
      rw[] >> gvs[] >> metis_tac[])
  >> simp[l0_used_def, upd_lchan_def, MEM_MAP, EXISTS_PROD, ADELKEY_def, MEM_FILTER] >>
  TRY (metis_tac[] >> NO_TAC) >>
  simp[LENGTH_FILTER_LEQ]
QED

(* ------------------------------------------------------------------------
   Every fd in use stays below the limit
   ------------------------------------------------------------------------ *)

Theorem fds_lt_small:
  fds_lt w ∧ l0_rely w ⇒ fds_small w
Proof
  rw[fds_lt_def, fds_small_def, l0_rely_def] >> res_tac >> decide_tac
QED

Theorem AFUPDKEY_MAP_FST:
  ∀l. MAP FST (AFUPDKEY k g l) = MAP FST l
Proof
  Induct >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[]
QED

Theorem l0_accept_fds_lt:
  fds_lt w ∧ l0_accept l w = (r, w') ⇒ fds_lt w'
Proof
  rw[l0_accept_def, l0_alloc_def, AllCaseEqs()] >> gvs[] >>
  gvs[fds_lt_def, l0_used_def, upd_lchan_def, AFUPDKEY_MAP_FST] >> rw[] >> gvs[]
QED

Theorem sys_accept_fds_lt:
  fds_lt w ∧ sys_accept l w = SOME (out, w', ev) ⇒ fds_lt w'
Proof
  rw[sys_accept_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  ‘fds_lt (l0_tick «sys_accept» w)’ by simp[] >>
  drule_all l0_accept_fds_lt >> simp[fds_lt_def]
QED

(* ------------------------------------------------------------------------
   Any action
   ------------------------------------------------------------------------ *)

Theorem l1do_nxt:
  l1do lfd (w, st) a = SOME (r, (w', st'), evs) ⇒ st'.nxt ≤ st.nxt + 1
Proof
  Cases_on ‘a’ >>
  rw[l1do_def, l1_close_def, forget_def, set_outbox_def, after_send_def, AllCaseEqs()] >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), forget_def, set_outbox_def] >>
  Cases_on ‘l0_res_of out’ >> gvs[after_send_def, set_outbox_def] >> rw[]
QED

(* The server's side of the round discipline: it accepts only on the
   listener, polled at the last poll; it reads only handles polled at the
   last poll (with the fd they had then); and its reads and writes are of
   sizes the FFI encodes *)
Definition act_disc_def:
  act_disc lfd polp (st : l1st) (Accept l) = (l = lfd ∧ MEM (lfd, lfd) polp) ∧
  act_disc lfd polp st (Read h n) =
    (0 < n ∧ n < 256 ** 8 ∧ ∀f. ALOOKUP st.tbl h = SOME f ⇒ MEM (h, f) polp) ∧
  act_disc lfd polp st (Write h bs) = (LENGTH bs < 256 ** 8)
End

Theorem act_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  rdy_ok lfd polp w st ∧ fds_lt w ∧ act_disc lfd polp st a ∧
  LENGTH (l0_used w) < 2147483647 ∧ hdln (w2n lfd) st.nxt < dimword (:64) ∧
  w2n lfd < 2147483648 ⇒
  ∃r w' st' s' hs' evs evs'.
    l1do lfd (w, st) a = SOME (r, (w', st'), evs) ∧
    hdo lfd (s, hs) a = SOME (r, (s', hs'), evs') ∧
    drops (MAP l0_v2_event evs) evs' ∧
    l1v2_rel p lfd sched (w', st') (s', hs') ∧ rdy_ok lfd polp w' st' ∧ fds_lt w' ∧
    st'.nxt ≤ st.nxt + 1 ∧ LENGTH (l0_used w') ≤ LENGTH (l0_used w) + 1 ∧
    w'.env = w.env ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >> drule_all fds_lt_small >> strip_tac >>
  ‘∀w' st' r evs. l1do lfd (w, st) a = SOME (r, (w', st'), evs) ⇒ st'.nxt ≤ st.nxt + 1’
    by metis_tac[l1do_nxt] >>
  Cases_on ‘a’
  (* Accept *)
  >- (rename1 ‘Accept l’ >> ‘l = lfd’ by fs[act_disc_def] >>
      pop_assum SUBST_ALL_TAC >> fs[act_disc_def] >>
      Cases_on ‘MEM lfd st.rdy’
      >- (‘small lfd’ by gvs[small_def] >>
          ‘hdln (w2n lfd) st.nxt < dimword (:64)’ by simp[] >>
          drule_all accept_step >> strip_tac >> gvs[] >>
          qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
          ‘¬st.exhausted’ by gvs[l1v2_rel_def] >> simp[] >>
          Cases_on ‘sys_accept lfd w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
          strip_tac >> imp_res_tac sys_accept_fds_lt >>
          gvs[AllCaseEqs()] >> metis_tac[drops_refl])
      >> drule_all accept_skip >> strip_tac >> simp[])
  (* Read *)
  >- (rename1 ‘Read h n’ >> fs[act_disc_def] >>
      Cases_on ‘ALOOKUP st.tbl h’
      >- (‘st.tbl = hs.tbl’ by gvs[l1v2_rel_def] >>
          simp[l1do_def, hdo_def] >> gvs[])
      >> rename1 ‘ALOOKUP _ h = SOME f’ >>
      ‘n < 256 ** 8’ by simp[] >>
      drule_all tbl_open_chan >> strip_tac >>
      Cases_on ‘MEM f st.rdy’
      >- (Cases_on ‘(EL j w.chans).inbox = []’
          >- (Cases_on ‘(EL j w.chans).peer_eof’
              >- (drule_all read_eof_step >> strip_tac >> simp[] >>
                  gvs[fds_lt_def] >> metis_tac[])
              >> drule_all read_empty_step >> strip_tac >> simp[] >>
              gvs[fds_lt_def] >> metis_tac[])
          >> drule_all read_data_step >> strip_tac >> simp[] >>
          gvs[fds_lt_def] >> metis_tac[])
      >> ‘MEM (h, f) polp’ by metis_tac[] >>
      drule_all read_skip >> strip_tac >> simp[])
  (* Write *)
  >> fs[act_disc_def] >> rename1 ‘Write h bs’ >>
  ‘LENGTH bs < 256 ** 8’ by simp[] >>
  drule_all write_step >> disch_then (qspec_then ‘h’ strip_assume_tac) >>
  qexistsl_tac [‘Wrote’, ‘w'’, ‘st'’, ‘s'’, ‘hs'’, ‘evs’, ‘MAP l0_v2_event evs’] >>
  gvs[fds_lt_def] >> metis_tac[]
QED

(* The poll buffer read back (D20) *)
Theorem pollfd_entries_FLAT:
  ∀l. EVERY (λx. LENGTH x = 8) l ⇒ pollfd_entries (FLAT l) = l
Proof
  Induct >- simp[Once pollfd_entries_def] >>
  rw[] >> simp[Once pollfd_entries_def] >>
  simp[TAKE_APPEND1, DROP_APPEND1, TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL_rwt]
QED

Theorem DROP_16_poll_buf[simp]:
  DROP 16 (poll_buf fes) = FLAT (MAP pfd_bytes fes)
Proof
  simp[poll_buf_def, DROP_APPEND]
QED

Theorem poll_out_entries:
  EVERY (λ(f, e). small f ∧ e < 4) fes ⇒
  pollfd_entries (DROP 16 (poll_out w (poll_buf fes))) =
  MAP (λfe. TAKE 6 (pfd_bytes fe) ++ abi_rev (fd_revents w fe)) fes
Proof
  strip_tac >> simp[poll_out_def, pollfd_entries_buf] >>
  ‘LENGTH (TAKE 3 (DROP 13 (poll_buf fes))) = 3’ by simp[poll_buf_def] >>
  simp[DROP_APPEND, MAP_MAP_o, o_DEF] >>
  ‘DROP 16 (enc_res (Ok (LENGTH (FILTER (λe. pfd_revents w (pe_fe e) ≠ 0w)
             (MAP pfd_bytes fes)))) ++ TAKE 3 (DROP 13 (poll_buf fes))) = []’
    by simp[DROP_LENGTH_TOO_LONG] >>
  ‘DROP 3 (TAKE 3 (DROP 13 (poll_buf fes))) = []’ by fs[DROP_LENGTH_TOO_LONG] >>
  simp[DROP_LENGTH_TOO_LONG] >>
  ‘EVERY (λx. LENGTH x = 8)
     (MAP (λx. TAKE 6 (pfd_bytes x) ++ abi_rev (pfd_revents w (pe_fe (pfd_bytes x)))) fes)’
    by simp[EVERY_MAP, abi_rev_def] >>
  drule pollfd_entries_FLAT >> simp[] >> strip_tac >>
  irule MAP_CONG >> simp[FORALL_PROD] >> rw[] >>
  gvs[EVERY_MEM] >> first_x_assum drule >> simp[] >> strip_tac >>
  drule_all pe_pfd_bytes >> simp[pfd_revents_def] >> fs[small_def]
QED

Theorem poll_revents_ok:
  EVERY (λ(f, e). small f ∧ e < 4) fes ∧ l0_res_of (poll_out w (poll_buf fes)) = Ok k ⇒
  poll_revents fes (poll_out w (poll_buf fes)) =
  ZIP (MAP FST fes, MAP (λfe. byte_revents (fd_revents w fe)) fes)
Proof
  strip_tac >> simp[poll_revents_def] >> drule poll_out_entries >>
  disch_then (qspec_then ‘w’ SUBST1_TAC) >> simp[MAP_MAP_o, o_DEF] >>
  ‘∀fe. DROP 6 (TAKE 6 (pfd_bytes fe) ++ abi_rev (fd_revents w fe)) = abi_rev (fd_revents w fe)’
    by simp[DROP_APPEND] >> simp[]
QED

