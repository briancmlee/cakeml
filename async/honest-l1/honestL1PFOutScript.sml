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
  (l0_close g w = (r, w') ⇒ (g ≠ f ⇒ l0_chan_of w' f = l0_chan_of w f) ∧ ∀c. csent w' c = csent w c)
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

(* ------------------------------------------------------------------------
   L1's calls and one fd's account
   ------------------------------------------------------------------------ *)

(* A send event (if any) of fewer than 2^64 bytes: its recorded count is
   the kernel's (an explicit, observed hypothesis on the trace) *)
Definition small_send_def:
  small_send (IO_event n conf bs) ⇔ (n = ExtCall «sys_send» ⇒ LENGTH conf < 8 + 256 ** 8)
End

(* f's account: the kernel took what the server wrote, up to f's outbox;
   a prefix of it once the outbox was dropped *)
Definition acct_def:
  acct w b f c out ⇔
    l0_chan_of w f = SOME c ∧
    (¬MEM f b.gone ⇒ csent w c ++ outbox_of b f = out) ∧
    (MEM f b.gone ⇒ csent w c ≼ out)
End

Theorem sys_send_csent:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ∧ small_send ev ∧ l0_chan_of w f = SOME c ⇒
  l0_chan_of w' f = SOME c ∧
  csent w' c = csent w c ++ ev_sent f ev ∧
  ev_sent f ev = (if g = f then (case l0_res_of out of Ok k => TAKE k bs | Fail _ _ => [])
                  else [])
Proof
  rw[sys_send_def] >>
  ‘LENGTH out = 13’
    by (gvs[l0_do_def, AllCaseEqs(), winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >>
  ‘LENGTH bs < 256 ** 8’ by gvs[small_send_def] >>
  qpat_x_assum ‘l0_do _ _ _ _ = _’ assume_tac >>
  drule_at (Pos last) csent_do >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >> simp[] >>
  gvs[ev_sent_def, taken_def, MAP_SND_ZIP_REPLICATE] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  simp[TAKE_APPEND1, DROP_APPEND1, TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL_rwt] >> rw[]
QED

(* The calls other than sends (and a close of f) keep f's channel and sent *)
Theorem sys_csent:
  winv w ∧ l0_chan_of w f = SOME c ⇒
  (sys_recv g k w = SOME (out, w', ev) ∨ sys_accept g w = SOME (out, w', ev) ∨
   sys_poll fes w = SOME (out, w', ev) ∨ (g ≠ f ∧ sys_close g w = SOME (out, w', ev))) ⇒
  l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ ev_sent f ev = []
Proof
  rpt strip_tac >> gvs[sys_recv_def, sys_accept_def, sys_poll_def, sys_close_def] >>
  drule_at (Pos last) csent_do >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  simp[] >> strip_tac >> drule l0_do_cases >> strip_tac >> gvs[ev_sent_def]
QED

Theorem acct_keep:
  acct w b f c out ∧ l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ⇒ acct w' b f c out
Proof
  simp[acct_def]
QED

Theorem acct_after_send:
  acct w b f c out ∧ ¬MEM f b.gone ∧ l0_chan_of w' f = SOME c ∧
  csent w' c = csent w c ++ (case r of Ok k => TAKE k (outbox_of b f) | Fail _ _ => []) ⇒
  acct w' (after_send f r b) f c out
Proof
  rw[acct_def, after_send_def] >> every_case_tac >> gvs[outbox_of_set_outbox, set_outbox_def] >>
  rw[] >> gvs[MEM_FILTER, IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem acct_after_send_other:
  acct w b f c out ∧ g ≠ f ⇒ acct w (after_send g r b) f c out
Proof
  rw[acct_def, after_send_def] >> every_case_tac >> gvs[outbox_of_set_outbox, set_outbox_def] >>
  gvs[MEM_FILTER] >> fs[outbox_of_def]
QED

(* The flush: f's account is kept, and f's sent grows by the flush's sends
   on f *)
Theorem l1_flush_acct:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ EVERY small_send evs ∧
    acct w b f c out ⇒
    acct w' b' f c out ∧ csent w' c = csent w c ++ evs_sent f evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  rename1 ‘sys_send g _ w = SOME (out1, w1, ev)’ >>
  ‘l0_chan_of w f = SOME c’ by gvs[acct_def] >>
  drule_all sys_send_csent >> strip_tac >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  ‘acct w1 (after_send g (l0_res_of out1) b) f c out’
    by (Cases_on ‘g = f’ >> gvs[]
        >- (irule acct_after_send >> simp[] >> qexists_tac ‘w’ >> simp[] >>
            every_case_tac >> simp[])
        >> irule acct_after_send_other >> simp[] >> irule acct_keep >> simp[] >>
        qexists_tac ‘w’ >> simp[]) >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem close_chans_len:
  l0_close g w = (r, w') ⇒ LENGTH w'.chans = LENGTH w.chans
Proof
  ‘∀q w. LENGTH (FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) w q).chans =
         LENGTH w.chans’ by (Induct >> simp[upd_lchan_def]) >>
  rw[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >>
  simp[upd_lchan_def]
QED

(* A close (of any fd) keeps every channel's sent *)
Theorem sys_close_csent:
  winv w ∧ c < LENGTH w.chans ∧ sys_close g w = SOME (out, w', ev) ⇒
  c < LENGTH w'.chans ∧ csent w' c = csent w c ∧ ev_sent f ev = []
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_sent_def] >>
  drule csent_tick >> disch_then (qspec_then ‘«sys_close»’ strip_assume_tac) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule close_chans_len >> strip_tac >>
  imp_res_tac csent_ops >> gvs[csent_def]
QED

Theorem l1_close_csent:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ c < LENGTH w.chans ⇒
  c < LENGTH w'.chans ∧ csent w' c = csent w c ∧ evs_sent f evs = [] ∧
  st' = forget g st
Proof
  rw[l1_close_def, AllCaseEqs()] >> drule_all sys_close_csent >> simp[]
QED
