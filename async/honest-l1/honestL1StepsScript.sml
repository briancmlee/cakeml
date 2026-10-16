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
  honestL0WorldProps honestL0Rely honestL0 asyncHLModel socketV2FFI socketV2Events
  ffiSpikeSocketFFI asyncM3World Marshalling
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
       (let fes = poll_entries (DROP 1 conf) in
          IO_event (ExtCall «sock_poll») (fds_bytes (MAP FST fes))
            (ZIP (REPLICATE (LENGTH fes) 0w,
                  MAP poll_flag (TAKE (LENGTH fes) (DROP 13 out)))))
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
  (l0_close f w = (r, w') ⇒ w'.env = w.env)
Proof
  rpt conj_tac >> rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def,
                     l0_shutdown_def, l0_close_def, AllCaseEqs()] >> gvs[]
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
