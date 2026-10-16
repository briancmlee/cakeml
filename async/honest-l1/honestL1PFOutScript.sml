(*
  R1-safe, the output side: what the kernel took on a connection is what
  the server wrote to it in the version-2 world (psk), up to L1's outbox;
  a prefix of it once L1 dropped the outbox (a send error, or D19).

  Per held fd f with channel c and client j = cl cm f:
    ¬gone f ⇒ (EL c w.chans).sent ++ outbox_of ps.b f = (EL j s.clients).outgoing
    gone f  ⇒ (EL c w.chans).sent ≼ (EL j s.clients).outgoing
  and, on the raw trace, round by round, `sent` grows by exactly the bytes
  the kernel took in that round's sys_send calls on f.

  L0 level first: a channel's `sent` changes only by a send on its fd.
*)
Theory honestL1PFOut
Ancestors
  honestL0WorldProps honestL1PFConnRun honestL1PFConn honestL1PFClient honestL1PFLive
  honestL1PFRound honestL1PFRefine honestL1PFInv honestL1PFModel honestL1Steps
  honestL1Props honestL1Model honestL0WorldInv honestL0Rely honestL0World honestL0
  socketV2FFI asyncHLModel asyncCore
Libs
  preamble

(* What the kernel has taken on channel c *)
Definition csent_def:
  csent w c = (EL c w.chans).sent
End

(* Ticks keep every channel's sent; new channels start with none *)
Theorem csent_deliver:
  c < LENGTH w.chans ⇒
  c < LENGTH (l0_deliver w a).chans ∧ csent (l0_deliver w a) c = csent w c
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, csent_def] >> every_case_tac >>
  gvs[upd_lchan_def, EL_LUPDATE, EL_APPEND1] >> rw[] >> rw[break_lchan_def]
QED

Theorem csent_tick:
  c < LENGTH w.chans ⇒
  c < LENGTH (l0_tick nm w).chans ∧ csent (l0_tick nm w) c = csent w c
Proof
  simp[l0_tick_def] >>
  ‘∀as w. c < LENGTH w.chans ⇒
          c < LENGTH (FOLDL l0_deliver w as).chans ∧
          csent (FOLDL l0_deliver w as) c = csent w c’
    by (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
        drule csent_deliver >> disch_then (qspec_then ‘h’ strip_assume_tac) >>
        first_x_assum drule >> simp[]) >>
  strip_tac >> first_x_assum (qspecl_then [‘w.env w.clock w.hist nm’,
                                            ‘w with clock := w.clock + 1’] mp_tac) >>
  simp[csent_def]
QED

Theorem csent_upd[simp]:
  l0_chan_of (upd_lchan j g w) f = l0_chan_of w f ∧
  csent (upd_lchan j g w) c =
    (if c = j ∧ j < LENGTH w.chans then (g (EL j w.chans)).sent else csent w c)
Proof
  rw[upd_lchan_def, l0_chan_of_def, csent_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem chan_of_simple[simp]:
  l0_chan_of (w with hist := h) f = l0_chan_of w f ∧
  l0_chan_of (w with listeners := ls) f = l0_chan_of w f ∧
  l0_chan_of (w with reserved := rs) f = l0_chan_of w f ∧
  csent (w with hist := h) c = csent w c ∧ csent (w with listeners := ls) c = csent w c ∧
  csent (w with reserved := rs) c = csent w c
Proof
  simp[l0_chan_of_def, csent_def]
QED

Theorem csent_FOLDL_break:
  ∀q w. (l0_chan_of (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q) f = l0_chan_of w f) ∧
        ∀c. csent (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q) c = csent w c
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘upd_lchan h (break_lchan e F) w’ strip_assume_tac) >>
  simp[] >> rw[break_lchan_def, csent_def]
QED

Theorem csent_ops:
  (l0_listen p w = (x, w') ⇒ (∀f. l0_chan_of w' f = l0_chan_of w f) ∧ ∀c. csent w' c = csent w c) ∧
  (l0_recv g n w = (r, d, w') ⇒ (∀f. l0_chan_of w' f = l0_chan_of w f) ∧ ∀c. csent w' c = csent w c) ∧
  (l0_shutdown g w = (r, w') ⇒ (∀f. l0_chan_of w' f = l0_chan_of w f) ∧ ∀c. csent w' c = csent w c) ∧
  (l0_connerr g w = (y, w') ⇒ (∀f. l0_chan_of w' f = l0_chan_of w f) ∧ ∀c. csent w' c = csent w c) ∧
  (l0_close g w = (r, w') ∧ g ≠ f ⇒ l0_chan_of w' f = l0_chan_of w f ∧ ∀c. csent w' c = csent w c)
Proof
  rpt conj_tac >> strip_tac
  >- (gvs[l0_listen_def, AllCaseEqs()])
  >- (gvs[l0_recv_def, AllCaseEqs()] >> rw[] >> rw[csent_def] >> metis_tac[])
  >- (gvs[l0_shutdown_def, AllCaseEqs()] >> rw[] >> rw[csent_def] >> metis_tac[])
  >- (gvs[l0_connerr_def, AllCaseEqs()] >> rw[] >> rw[csent_def] >> metis_tac[])
  >> gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >>
  gvs[csent_FOLDL_break] >> rw[] >> rw[csent_def] >>
  gvs[l0_chan_of_def, ALOOKUP_ADELKEY, csent_def] >> rw[] >> metis_tac[]
QED

Theorem csent_accept:
  l0_accept l w = (r, w') ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧ l0_chan_of w f = SOME c ⇒
  l0_chan_of w' f = SOME c ∧ ∀c'. csent w' c' = csent w c'
Proof
  rw[l0_accept_def] >> gvs[AllCaseEqs(), fail_def] >> rw[] >> rw[break_lchan_def] >>
  gvs[l0_alloc_def] >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free_lim >> gvs[fds_lt_def]) >>
  gvs[l0_chan_of_def, csent_def, AllCaseEqs(), l0_used_def] >> rw[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem csent_send:
  l0_send g bs w = (r, w') ∧ l0_chan_of w f = SOME c ∧ l0wf w ⇒
  l0_chan_of w' f = SOME c ∧
  csent w' c = csent w c ++ (if g = f then (case r of Ok k => TAKE k bs | Fail _ _ => []) else [])
Proof
  rw[l0_send_def] >> gvs[AllCaseEqs(), fail_def] >> rw[] >> rw[] >>
  gvs[l0_chan_of_def, AllCaseEqs(), csent_def] >>
  metis_tac[open_chan_ne]
QED

(* The bytes a send on f took, as its event records them *)
Definition taken_def:
  taken f conf r =
    if bytes_fd (TAKE 8 conf) = f then
      (case r of Ok k => TAKE k (DROP 8 conf) | Fail _ _ => [])
    else []
End

Theorem tick_open_fds[simp]:
  (l0_tick nm w).open_fds = w.open_fds
Proof
  simp[l0_tick_def] >>
  ‘∀as w0. (FOLDL l0_deliver w0 as).open_fds = w0.open_fds’
    by (Induct >> simp[] >> Cases_on ‘h’ >> rw[l0_deliver_def] >> every_case_tac >>
        simp[upd_lchan_def]) >>
  simp[]
QED

Theorem csent_ticks:
  ∀k w. l0_chan_of w f = SOME c ⇒
        l0_chan_of (l0_ticks nm k w) f = SOME c ∧ csent (l0_ticks nm k w) c = csent w c
Proof
  ‘∀w. l0_chan_of w f = SOME c ⇒ l0_chan_of (l0_tick nm w) f = SOME c ∧
                                  csent (l0_tick nm w) c = csent w c’
    by (gen_tac >> strip_tac >>
        ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
        drule csent_tick >> disch_then (qspec_then ‘nm’ strip_assume_tac) >>
        gvs[l0_chan_of_def, AllCaseEqs()]) >>
  Induct >> simp[l0_ticks_def] >> metis_tac[]
QED

(* A call (not a connect, not a close of f, a send of fewer than 2^64
   bytes): f keeps its channel, whose sent grows by what a send on f took *)
Theorem csent_call:
  l0_chan_of w f = SOME c ∧ l0wf w ∧ fds_lt w ∧ l0_rely w ∧
  n ≠ «sys_connect» ∧ ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧
  (n = «sys_send» ⇒ LENGTH conf < 8 + 256 ** 8) ∧
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  l0_chan_of w' f = SOME c ∧
  csent w' c = csent w c ++
               (if n = «sys_send» then taken f conf (l0_res_of bytes') else [])
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac csent_ops >> gvs[] >>
  TRY (rename1 ‘l0_ticks _ k w’ >>
       qspecl_then [‘k’, ‘w’] mp_tac
         (Q.GENL [‘k’, ‘w’] (Q.INST [‘nm’ |-> ‘«sys_poll»’] (SPEC_ALL csent_ticks))) >>
       simp[] >> NO_TAC) >>
  TRY (rename1 ‘l0_accept l w = (r, w')’ >>
       qspecl_then [‘l’, ‘w’, ‘r’, ‘w'’, ‘f’, ‘c’] mp_tac
         (Q.GENL [‘l’, ‘w’, ‘r’, ‘w'’, ‘f’, ‘c’] csent_accept) >>
       impl_tac >- fs[l0_rely_def] >> simp[] >> NO_TAC) >>
  (* send *)
  drule_all csent_send >> strip_tac >> simp[] >>
  ‘l0_res_ok r’
    by (qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
        simp[l0_send_def, not_chan_def] >> rw[AllCaseEqs()] >>
        TRY (irule fail_ok >> simp[] >> NO_TAC) >>
        simp[l0_res_ok_def, MIN_DEF] >> rw[] >> fs[]) >>
  simp[l0_res_of_enc, taken_def] >> rw[] >> every_case_tac >> gvs[]
QED

(* The bytes the kernel took on f in event ev, as the event records them *)
Definition ev_sent_def:
  ev_sent f (IO_event n conf bs) =
    if n = ExtCall «sys_send» then taken f conf (l0_res_of (MAP SND bs)) else []
End

(* The same on a list of events (a round's) *)
Definition evs_sent_def:
  evs_sent f evs = FLAT (MAP (ev_sent f) evs)
End

Theorem evs_sent_simps[simp]:
  evs_sent f [] = [] ∧ evs_sent f (ev :: evs) = ev_sent f ev ++ evs_sent f evs ∧
  evs_sent f (evs1 ++ evs2) = evs_sent f evs1 ++ evs_sent f evs2
Proof
  simp[evs_sent_def]
QED

Theorem csent_do:
  winv w ∧ l0_chan_of w f = SOME c ∧ n ≠ «sys_connect» ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧ (n = «sys_send» ⇒ LENGTH conf < 8 + 256 ** 8) ∧
  l0_do n conf alen w = SOME (out, w', ev) ⇒
  l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ++ ev_sent f ev
Proof
  strip_tac >>
  ‘LENGTH out = alen’
    by (gvs[l0_do_def, AllCaseEqs(), winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick n w’ >>
  ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘l0_chan_of wt f = SOME c ∧ csent wt c = csent w c’
    by (qspecl_then [‘w’, ‘n’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
        simp[Abbr ‘wt’] >> gvs[l0_chan_of_def, AllCaseEqs()]) >>
  ‘l0wf wt ∧ fds_lt wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, l0wf_tick] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_at (Pos last) csent_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >>
  strip_tac >> simp[ev_sent_def, MAP_SND_ZIP_REPLICATE] >> rw[]
QED
