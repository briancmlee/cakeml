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

Theorem csent_do_buf:
  winv w ∧ l0_chan_of w f = SOME c ∧ n ≠ «sys_connect» ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧ (n = «sys_send» ⇒ LENGTH conf < 8 + 256 ** 8) ∧
  l0_do_buf n conf bs w = SOME (out, w', ev) ⇒
  l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ++ ev_sent f ev
Proof
  strip_tac >>
  ‘LENGTH out = LENGTH bs’
    by (gvs[l0_do_buf_def, AllCaseEqs(), winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick n w’ >>
  ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘l0_chan_of wt f = SOME c ∧ csent wt c = csent w c’
    by (qspecl_then [‘w’, ‘n’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
        simp[Abbr ‘wt’] >> gvs[l0_chan_of_def, AllCaseEqs()]) >>
  ‘l0wf wt ∧ fds_lt wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, l0wf_tick] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_at (Pos last) csent_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >>
  strip_tac >> simp[ev_sent_def, MAP_ZIP] >> rw[]
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
  TRY (drule_at (Pos last) csent_do_buf >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
       simp[] >> strip_tac >> drule l0_do_buf_cases >> strip_tac >> gvs[ev_sent_def] >>
       NO_TAC) >>
  drule_at (Pos last) csent_do >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  simp[] >> strip_tac >> drule l0_do_cases >> strip_tac >> gvs[ev_sent_def]
QED

Theorem sys_close_chan:
  winv w ∧ l0_chan_of w f = SOME c ∧ g ≠ f ∧ sys_close g w = SOME (out, w', ev) ⇒
  l0_chan_of w' f = SOME c
Proof
  metis_tac[sys_csent]
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

(* ------------------------------------------------------------------------
   The server's actions
   ------------------------------------------------------------------------ *)

(* What an action writes to f *)
Definition wbytes_def:
  wbytes f (b : l1st) (Write h bs : sact) = (if ALOOKUP b.tbl h = SOME f then bs else []) ∧
  wbytes f b (Read h n : sact) = [] ∧
  wbytes f b (Accept l : sact) = []
End

Theorem pdo_acct:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ EVERY small_send evs ∧
  l0_chan_of w f = SOME c ∧ pown lfd ps ⇒
  c < LENGTH w'.chans ∧ csent w' c = csent w c ++ evs_sent f evs ∧
  (acct w ps.b f c out ∧ (MEM f (MAP SND ps'.b.tbl) ∨ MEM f ps'.b.closing) ⇒
   acct w' ps'.b f c (out ++ wbytes f ps.b a))
Proof
  strip_tac >>
  ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs(), wbytes_def] >>
  TRY (rw[] >> gvs[acct_def] >> NO_TAC) >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY ((* a read that closes f' *)
       drule_all l1_close_csent >> disch_then (qspec_then ‘f’ strip_assume_tac) >> gvs[] >>
       strip_tac >>
       ‘f ≠ f'’
         by (strip_tac >> gvs[forget_def, set_outbox_def, MEM_FILTER] >>
             gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[MEM_SND_ADELKEY]) >>
       qpat_x_assum ‘l1_close _ _ = _’ mp_tac >> simp[l1_close_def, AllCaseEqs()] >>
       strip_tac >>
       ‘l0_chan_of w' f = SOME c’ by (irule sys_close_chan >> metis_tac[]) >>
       qpat_x_assum ‘acct w _ _ _ _’ mp_tac >>
       simp[acct_def, forget_def, outbox_of_set_outbox, MEM_FILTER] >>
       simp[outbox_of_def, set_outbox_def, MEM_FILTER] >> NO_TAC) >>
  (* a write *)
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  Cases_on ‘ALOOKUP ps.b.tbl c'’ >> simp[] >- (rw[] >> gvs[]) >>
  rename1 ‘ALOOKUP _ _ = SOME g’ >>
  IF_CASES_TAC
  >- (rw[] >> gvs[acct_def] >> rw[] >> gvs[] >>
      metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND3, APPEND_ASSOC]) >>
  IF_CASES_TAC
  >- (rw[] >> gvs[acct_def, outbox_of_set_outbox, set_outbox_def] >> rw[] >>
      fs[outbox_of_def]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 ‘sys_send g _ w = SOME (out1, w1, ev)’ >>
  drule_all sys_send_csent >> strip_tac >>
  ‘c < LENGTH w1.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  ‘g = f ⇒ ¬MEM f ps.b.closing’
    by (strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
        gvs[pown_def, ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[SND]) >>
  Cases_on ‘g = f’ >> gvs[] >>
  TRY (gvs[set_outbox_def] >> NO_TAC) >>
  TRY (irule acct_after_send >> simp[outbox_of_set_outbox, set_outbox_def] >>
       qexists_tac ‘w’ >> gvs[acct_def, outbox_of_set_outbox] >>
       every_case_tac >> simp[outbox_of_def, ALOOKUP_ADELKEY] >> NO_TAC) >>
  irule acct_after_send_other >> simp[] >>
  gvs[acct_def, outbox_of_set_outbox, set_outbox_def] >> fs[outbox_of_def]
QED

(* ------------------------------------------------------------------------
   The handle layer's writes
   ------------------------------------------------------------------------ *)

(* What an action of the handle layer writes to client j *)
Definition hwrote_def:
  hwrote s hs (Write h bs : sact) j =
    (case ALOOKUP hs.tbl h of
     | SOME f => if client_of s f = SOME j then bs else []
     | NONE => []) ∧
  hwrote s hs (Read h n : sact) j = [] ∧
  hwrote s hs (Accept l : sact) j = []
End

Theorem sock_ops_clients:
  (sock_read2 f n s = SOME (x, s') ⇒
     LENGTH s'.clients = LENGTH s.clients ∧
     ∀j. (EL j s'.clients).outgoing = (EL j s.clients).outgoing) ∧
  (sock_close2 f s = SOME s' ⇒ s'.clients = s.clients) ∧
  (sock_accept2 l s = SOME (y, s') ⇒ s'.clients = s.clients) ∧
  (sock_write2 f bs s = SOME s' ⇒
     LENGTH s'.clients = LENGTH s.clients ∧
     ∀j. (EL j s'.clients).outgoing =
         (EL j s.clients).outgoing ++ (if client_of s f = SOME j then bs else []))
Proof
  rpt conj_tac >> strip_tac
  >- (qpat_x_assum ‘sock_read2 _ _ _ = _’ mp_tac >> simp[sock_read2_def] >>
      Cases_on ‘client_of s f’ >> simp[] >> rw[] >>
      simp[update_client_def, EL_LUPDATE] >> rw[] >> simp[])
  >- (qpat_x_assum ‘sock_close2 _ _ = _’ mp_tac >> simp[sock_close2_def] >>
      Cases_on ‘client_of s f’ >> simp[] >> rw[] >> simp[])
  >- (qpat_x_assum ‘sock_accept2 _ _ = _’ mp_tac >>
      PURE_REWRITE_TAC[sock_accept2_def] >>
      every_case_tac >> fs[LET_THM] >> rpt strip_tac >> rveq >> simp[])
  >> qpat_x_assum ‘sock_write2 _ _ _ = _’ mp_tac >> simp[sock_write2_def] >>
  Cases_on ‘client_of s f’ >> simp[] >> strip_tac >> rveq >>
  simp[update_client_def, EL_LUPDATE] >> gen_tac >> Cases_on ‘j = x’ >> simp[] >>
  gvs[client_of_def, AllCaseEqs()]
QED

Theorem hdo_out:
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ⇒
  LENGTH s'.clients = LENGTH s.clients ∧
  ∀j. (EL j s'.clients).outgoing = (EL j s.clients).outgoing ++ hwrote s hs a j
Proof
  Cases_on ‘a’ >> PURE_REWRITE_TAC[hdo_def, hwrote_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> imp_res_tac sock_ops_clients >> gvs[]
QED

(* ------------------------------------------------------------------------
   A queued connection has nothing sent: the kernel takes bytes on a
   channel only through a send on its fd, and a queued channel has none
   ------------------------------------------------------------------------ *)

Definition qfresh_def:
  qfresh w ⇔
    ∀l p q j. MEM (l, p, q) w.listeners ∧ MEM j q ⇒ j < LENGTH w.chans ∧ csent w j = []
End

Theorem MEM_AFUPDKEY_imp:
  ∀ls. MEM (k', v') (AFUPDKEY k g ls) ⇒ MEM (k', v') ls ∨ ∃v. MEM (k, v) ls ∧ k' = k ∧ v' = g v
Proof
  Induct >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[] >> metis_tac[]
QED

Theorem qfresh_simple[simp]:
  (qfresh (w with hist := h) ⇔ qfresh w) ∧ (qfresh (w with clock := c) ⇔ qfresh w) ∧
  (qfresh (w with open_fds := fs) ⇔ qfresh w) ∧ (qfresh (w with reserved := rs) ⇔ qfresh w)
Proof
  simp[qfresh_def, csent_def]
QED

Theorem qfresh_upd:
  qfresh w ∧ (j < LENGTH w.chans ⇒ (g (EL j w.chans)).sent = (EL j w.chans).sent) ⇒
  qfresh (upd_lchan j g w)
Proof
  rw[qfresh_def, upd_lchan_def, csent_def, EL_LUPDATE] >> res_tac >> rw[] >> gvs[csent_def]
QED

Theorem qfresh_deliver:
  qfresh w ⇒ qfresh (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  TRY (irule qfresh_upd >> rw[break_lchan_def] >> NO_TAC) >>
  gvs[qfresh_def] >> rpt gen_tac >> strip_tac >>
  drule MEM_AFUPDKEY_imp >> strip_tac >> gvs[]
  >- (res_tac >> gvs[csent_def, EL_APPEND1])
  >> pairarg_tac >> gvs[]
  >- (res_tac >> gvs[csent_def, EL_APPEND1])
  >> simp[csent_def, EL_APPEND2, fresh_lchan_def]
QED

Theorem qfresh_tick:
  qfresh w ⇒ qfresh (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. qfresh w ⇒ qfresh (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[qfresh_deliver]) >>
  rw[] >> first_x_assum irule >> simp[]
QED

Theorem qfresh_ticks:
  ∀k w. qfresh w ⇒ qfresh (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[qfresh_tick]
QED

Theorem qfresh_FOLDL_break:
  ∀q w. qfresh w ⇒ qfresh (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule qfresh_upd >> rw[break_lchan_def]
QED

Theorem qfresh_listen:
  qfresh w ∧ l0_listen p w = (x, w') ⇒ qfresh w'
Proof
  strip_tac >> gvs[l0_listen_def, AllCaseEqs()] >> gvs[qfresh_def] >> rw[] >> gvs[] >>
  metis_tac[]
QED

Theorem qfresh_send:
  qfresh w ∧ l0wf w ∧ l0_send g bs w = (r, w') ⇒ qfresh w'
Proof
  strip_tac >>
  gvs[l0_send_def, AllCaseEqs()] >> TRY (irule qfresh_upd >> simp[] >> NO_TAC) >>
  gvs[l0_chan_of_def, AllCaseEqs()] >> imp_res_tac ALOOKUP_MEM >>
  gvs[qfresh_def, upd_lchan_def, csent_def, EL_LUPDATE] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >> simp[] >>
  rename1 ‘MEM j' q’ >> Cases_on ‘j' = j’ >> simp[] >> gvs[] >>
  gvs[l0wf_def, used_chans_def, ALL_DISTINCT_APPEND] >>
  ‘MEM j (FLAT (MAP (SND ∘ SND) w.listeners))’
    by (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘(l, p, q)’ >> simp[]) >>
  ‘MEM j (MAP SND w.open_fds)’ by (simp[MEM_MAP] >> qexists_tac ‘(g, j)’ >> simp[]) >>
  qpat_x_assum ‘∀e. MEM e (MAP SND w.open_fds) ⇒ _’ drule >> simp[]
QED

Theorem qfresh_recv:
  qfresh w ∧ l0_recv g n w = (r, d, w') ⇒ qfresh w'
Proof
  strip_tac >> gvs[l0_recv_def, AllCaseEqs()] >> rpt (irule qfresh_upd >> simp[])
QED

Theorem qfresh_shutdown:
  qfresh w ∧ l0_shutdown g w = (r, w') ⇒ qfresh w'
Proof
  strip_tac >> gvs[l0_shutdown_def, AllCaseEqs()] >> rpt (irule qfresh_upd >> simp[])
QED

Theorem qfresh_connerr:
  qfresh w ∧ l0_connerr g w = (y, w') ⇒ qfresh w'
Proof
  strip_tac >> gvs[l0_connerr_def, AllCaseEqs()] >> rpt (irule qfresh_upd >> simp[])
QED

Theorem qfresh_close:
  qfresh w ∧ l0_close g w = (r, w') ⇒ qfresh w'
Proof
  strip_tac >> gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule qfresh_upd >> simp[] >> NO_TAC) >>
  irule qfresh_FOLDL_break >> gvs[qfresh_def, MEM_FILTER] >> metis_tac[]
QED

Theorem qfresh_pop:
  qfresh w ∧ FILTER (λ(l', p, q). l' = l) w.listeners = (x, p, j :: q') :: t ⇒
  qfresh (w with listeners := AFUPDKEY l (K (p, q')) w.listeners)
Proof
  simp[qfresh_def] >> strip_tac >>
  ‘MEM (x, p, j :: q') w.listeners ∧ x = l’
    by (qpat_x_assum ‘FILTER _ _ = _’ (mp_tac o Q.AP_TERM ‘MEM (x, p, j :: q')’) >>
        simp[MEM_FILTER]) >>
  rpt gen_tac >> strip_tac >>
  drule MEM_AFUPDKEY_imp >> strip_tac >- (res_tac >> simp[]) >>
  gvs[] >> metis_tac[MEM]
QED

Theorem qfresh_accept:
  qfresh w ∧ l0_accept g w = (r, w') ⇒ qfresh w'
Proof
  strip_tac >> gvs[l0_accept_def, AllCaseEqs(), fail_def] >>
  drule_all qfresh_pop >> strip_tac >>
  TRY (irule qfresh_upd >> simp[] >> rw[break_lchan_def] >> NO_TAC) >>
  fs[qfresh_def, csent_def] >> first_assum ACCEPT_TAC
QED

Theorem qfresh_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_connect» ∧
  qfresh w ∧ l0wf w ⇒ qfresh w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac qfresh_listen >> imp_res_tac qfresh_send >> imp_res_tac qfresh_recv >>
  imp_res_tac qfresh_shutdown >> imp_res_tac qfresh_connerr >> imp_res_tac qfresh_close >>
  imp_res_tac qfresh_accept >> gvs[qfresh_ticks]
QED

Theorem qfresh_do:
  l0_do n conf alen w = SOME (out, w', ev) ∧ n ≠ «sys_connect» ∧ qfresh w ∧ winv w ⇒
  qfresh w'
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  drule qfresh_call >> simp[] >> disch_then irule >>
  gvs[winv_def, qfresh_tick, l0wf_tick]
QED

Theorem qfresh_do_buf:
  l0_do_buf n conf bs w = SOME (out, w', ev) ∧ n ≠ «sys_connect» ∧ qfresh w ∧ winv w ⇒
  qfresh w'
Proof
  strip_tac >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  drule qfresh_call >> simp[] >> disch_then irule >>
  gvs[winv_def, qfresh_tick, l0wf_tick]
QED

Theorem sys_qfresh:
  (qfresh w ∧ winv w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ qfresh w') ∧
  (qfresh w ∧ winv w ∧ sys_close g w = SOME (out, w', ev) ⇒ qfresh w') ∧
  (qfresh w ∧ winv w ∧ sys_recv g k w = SOME (out, w', ev) ⇒ qfresh w') ∧
  (qfresh w ∧ winv w ∧ sys_accept g w = SOME (out, w', ev) ⇒ qfresh w') ∧
  (qfresh w ∧ winv w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ qfresh w')
Proof
  rw[sys_close_def, sys_send_def, sys_recv_def, sys_accept_def, sys_poll_def] >>
  TRY (drule_at (Pos (el 1)) qfresh_do_buf >> simp[] >> NO_TAC) >>
  drule_at (Pos (el 1)) qfresh_do >> simp[]
QED

Theorem l1_close_qfresh:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ qfresh w ∧ winv w ⇒ qfresh w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_qfresh]
QED

Theorem pdo_qfresh:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ qfresh w ∧ winv w ⇒ qfresh w'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY (drule_all l1_close_qfresh >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >> metis_tac[sys_qfresh]
QED

Theorem pacts_qfresh:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ qfresh w ∧ winv w ⇒ qfresh w'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all pdo_qfresh >> strip_tac >> drule_all pdo_winv >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_polls_qfresh:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ qfresh w ⇒ qfresh w'
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  ‘winv w1 ∧ qfresh w1’ by metis_tac[sys_winv, sys_qfresh] >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_qfresh:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ qfresh w ⇒
                       qfresh w'
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘winv w'' ∧ qfresh w''’ by metis_tac[sys_winv, sys_qfresh] >>
  first_x_assum drule_all >> simp[]
QED

Theorem pf_fetch_qfresh:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ qfresh w ⇒ qfresh w'
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum irule >> metis_tac[sys_winv, sys_qfresh]
QED

Theorem l1_reap_qfresh:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ qfresh w ⇒
                       qfresh w'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >>
      drule_all l1_close_qfresh >> strip_tac >>
      drule_all l1_close_winv >> strip_tac >>
      first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem pround_qfresh:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧ qfresh w ⇒
  qfresh w'
Proof
  rw[pround_def, AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> drule_all pacts_qfresh >> drule_all pacts_winv >> rpt strip_tac >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all l1_polls_qfresh >> drule_all l1_polls_winv >> rpt strip_tac >>
  drule_all l1_flush_qfresh >> drule_all l1_flush_winv >> rpt strip_tac >>
  drule_all pf_fetch_qfresh >> drule_all pf_fetch_winv >> rpt strip_tac >>
  drule_all l1_reap_qfresh >> simp[]
QED

(* ------------------------------------------------------------------------
   The relation
   ------------------------------------------------------------------------ *)

(* Only held fds (open or closing) have an outbox or are gone *)
Definition okeys_def:
  okeys (b : l1st) ⇔
    ∀f. outbox_of b f ≠ [] ∨ MEM f b.gone ⇒ MEM f (MAP SND b.tbl) ∨ MEM f b.closing
End

(* Per held fd: what the kernel took on its channel, then L1's outbox, is
   what the server wrote to its client in the version-2 world s (a prefix,
   once gone); a pre-accepted fd's channel and client have nothing yet;
   queued channels have nothing sent *)
Definition out_rel_def:
  out_rel cm w ps s ⇔
    (∀f. MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ⇒
         MEM f (MAP FST cm) ∧ ∃c. acct w ps.b f c (EL (cl cm f) s.clients).outgoing) ∧
    okeys ps.b ∧
    (∀f. MEM f ps.acq ⇒
         ∃c. l0_chan_of w f = SOME c ∧ csent w c = [] ∧
             (EL (cl cm f) s.clients).outgoing = []) ∧
    qfresh w
End

Theorem cl_mem:
  MEM f (MAP FST cm) ⇒ MEM (cl cm f) (MAP SND cm)
Proof
  rw[cl_def] >> Cases_on ‘ALOOKUP cm f’ >> gvs[ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem hwrote_wbytes:
  pv_rel lfd cm ps s ∧ MEM f (MAP FST cm) ⇒
  hwrote s (hs_of ps) a (cl cm f) = wbytes f ps.b a
Proof
  strip_tac >> Cases_on ‘a’ >> simp[hwrote_def, wbytes_def, hs_of_def] >>
  CASE_TAC >> simp[] >> rename1 ‘ALOOKUP ps.b.tbl h = SOME g’ >>
  ‘MEM g (MAP FST cm) ∧ ALOOKUP s.open_fds g = SOME (cl cm g)’
    by (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> simp[pv_rel_def] >> metis_tac[]) >>
  ‘ALL_DISTINCT (MAP SND cm) ∧ EVERY (λj. j < LENGTH s.clients) (MAP SND cm)’
    by fs[pv_rel_def] >>
  ‘cl cm g < LENGTH s.clients’ by (drule cl_mem >> gvs[EVERY_MEM]) >>
  simp[client_of_def] >> metis_tac[cl_inj]
QED

Theorem pdo_held:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ∧
  (MEM f (MAP SND ps'.b.tbl) ∨ MEM f ps'.b.closing) ⇒
  MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >>
  gvs[forget_def, set_outbox_def, MEM_FILTER] >>
  TRY (drule MEM_SND_ADELKEY_sub >> simp[] >> NO_TAC) >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem forget_keys:
  outbox_of (forget f st) g = (if g = f then [] else outbox_of st g) ∧
  (forget f st).gone = FILTER ($≠ f) st.gone ∧ (forget f st).tbl = st.tbl ∧
  (forget f st).closing = FILTER ($≠ f) st.closing
Proof
  rw[forget_def, set_outbox_def, outbox_of_def, ALOOKUP_ADELKEY]
QED

Theorem okeys_close:
  okeys b ∧ ALOOKUP b.tbl h = SOME f ∧ ALL_DISTINCT (MAP FST b.tbl) ∧
  ALL_DISTINCT (MAP SND b.tbl) ⇒
  okeys (forget f (b with tbl := ADELKEY h b.tbl))
Proof
  rw[okeys_def, forget_keys, MEM_FILTER] >> gvs[] >>
  drule_all MEM_SND_ADELKEY >> simp[] >> disch_then kall_tac >>
  Cases_on ‘f' = f’ >> gvs[] >>
  first_x_assum (qspec_then ‘f'’ mp_tac) >> simp[] >> metis_tac[]
QED

Theorem okeys_flushing:
  okeys b ∧ ALOOKUP b.tbl h = SOME f ∧ ALL_DISTINCT (MAP FST b.tbl) ∧
  ALL_DISTINCT (MAP SND b.tbl) ⇒
  okeys (b with <| tbl := ADELKEY h b.tbl; closing := f :: b.closing |>)
Proof
  rw[okeys_def] >> drule_all MEM_SND_ADELKEY >> simp[] >> disch_then kall_tac >>
  Cases_on ‘f' = f’ >> simp[] >> first_x_assum irule >> fs[outbox_of_def]
QED

Theorem okeys_acc:
  okeys b ⇒ okeys (b with <| tbl := (h, f) :: b.tbl; nxt := n |>)
Proof
  rw[okeys_def] >> gvs[outbox_of_def] >> metis_tac[]
QED

Theorem okeys_set_outbox:
  okeys b ∧ (MEM f (MAP SND b.tbl) ∨ MEM f b.closing) ⇒ okeys (set_outbox f x b)
Proof
  rw[okeys_def, outbox_of_set_outbox] >> rw[set_outbox_def] >>
  Cases_on ‘f' = f’ >> gvs[] >> first_x_assum irule >> gvs[set_outbox_def]
QED

Theorem okeys_after_send:
  okeys b ∧ (MEM f (MAP SND b.tbl) ∨ MEM f b.closing) ⇒ okeys (after_send f r b)
Proof
  rw[after_send_def] >> every_case_tac >> simp[] >>
  TRY (irule okeys_set_outbox >> simp[] >> NO_TAC) >>
  irule okeys_set_outbox >> gvs[okeys_def, MEM_FILTER] >> rw[] >> gvs[outbox_of_def] >>
  metis_tac[]
QED

Theorem pdo_keys:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ∧ okeys ps.b ⇒ okeys ps'.b
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >>
  ‘ALL_DISTINCT (MAP FST ps.b.tbl) ∧ ALL_DISTINCT (MAP SND ps.b.tbl)’
    by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  TRY (irule okeys_acc >> simp[] >> NO_TAC) >>
  TRY (irule okeys_close >> simp[] >> NO_TAC) >>
  TRY (irule okeys_flushing >> simp[] >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC) >>
  imp_res_tac ALOOKUP_MEM >>
  ‘MEM f (MAP SND ps.b.tbl)’ by (simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘c’ >> simp[]) >>
  TRY (irule okeys_set_outbox >> simp[] >> NO_TAC) >>
  irule okeys_after_send >> rpt conj_tac >>
  TRY (irule okeys_set_outbox >> simp[] >> NO_TAC) >> simp[set_outbox_def]
QED

(* An action touches only fds with a handle *)
Theorem pdo_chan:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ EVERY small_send evs ∧
  l0_chan_of w f = SOME c ∧ ¬MEM f (MAP SND ps.b.tbl) ⇒
  l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ evs_sent f evs = []
Proof
  strip_tac >>
  ‘∀h g. ALOOKUP ps.b.tbl h = SOME g ⇒ g ≠ f’
    by (rpt strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >>
        metis_tac[SND]) >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> res_tac >>
  TRY (gvs[] >> NO_TAC) >>
  ‘f' ≠ f’ by metis_tac[] >> fs[] >>
  TRY (drule_all sys_send_csent >> simp[] >> NO_TAC) >>
  mp_tac (Q.INST [‘g’ |-> ‘f'’, ‘out’ |-> ‘v1’, ‘fes’ |-> ‘[]’] sys_csent) >> fs[]
QED

Theorem wbytes_nil:
  ¬MEM f (MAP SND b.tbl) ⇒ wbytes f b a = []
Proof
  Cases_on ‘a’ >> rw[wbytes_def] >> imp_res_tac ALOOKUP_MEM >>
  gvs[MEM_MAP] >> metis_tac[SND]
QED

(* A pre-accepted fd: its account is empty *)
Theorem acq_acct:
  out_rel cm w ps s ∧ pown lfd ps ∧ MEM f ps.acq ⇒
  ∃c. acct w ps.b f c (EL (cl cm f) s.clients).outgoing ∧ csent w c = [] ∧
      ¬MEM f (MAP SND ps.b.tbl)
Proof
  rw[out_rel_def] >> first_x_assum drule >> strip_tac >>
  ‘¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing’
    by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘outbox_of ps.b f = [] ∧ ¬MEM f ps.b.gone’ by (gvs[okeys_def] >> metis_tac[]) >>
  qexists_tac ‘c’ >> simp[acct_def]
QED

Theorem held_acct:
  out_rel cm w ps s ∧ pown lfd ps ∧ pv_rel lfd cm ps s ∧
  (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq) ⇒
  MEM f (MAP FST cm) ∧ ∃c. acct w ps.b f c (EL (cl cm f) s.clients).outgoing
Proof
  rpt strip_tac
  >~ [‘MEM f ps.acq’]
  >- (gvs[pv_rel_def])
  >~ [‘MEM f ps.acq’]
  >- (drule_all acq_acct >> metis_tac[])
  >> gvs[out_rel_def]
QED

Theorem pdo_out:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧
  hdo lfd (s, hs_of ps) a = SOME (r', (s', hs'), hevs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧ EVERY small_send evs ∧ out_rel cm w ps s ⇒
  out_rel cm w' ps' s'
Proof
  strip_tac >> drule hdo_out >> strip_tac >>
  ‘qfresh w ∧ okeys ps.b’ by gvs[out_rel_def] >>
  ‘qfresh w'’ by (drule_all pdo_qfresh >> simp[]) >>
  ‘okeys ps'.b’ by (drule_all pdo_keys >> simp[]) >>
  ‘∀f. MEM f ps.acq ⇒ MEM f (MAP FST cm)’ by gvs[pv_rel_def] >>
  simp[out_rel_def] >> rpt conj_tac
  >- (gen_tac >> disch_then assume_tac >>
      ‘MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq’
        by (drule pdo_held >> fs[]) >>
      ‘MEM f (MAP FST cm) ∧ ∃c. acct w ps.b f c (EL (cl cm f) s.clients).outgoing’
        by metis_tac[held_acct] >>
      simp[] >> qexists_tac ‘c’ >>
      ‘l0_chan_of w f = SOME c’ by gvs[acct_def] >>
      drule_all pdo_acct >> strip_tac >>
      drule_all hwrote_wbytes >> disch_then (fn th => REWRITE_TAC [th]) >>
      first_x_assum (qspec_then ‘(EL (cl cm f) s.clients).outgoing’ strip_assume_tac) >>
      first_x_assum irule >> simp[])
  >> rpt strip_tac >>
  drule pdo_lfd >> strip_tac >>
  ‘MEM f ps.acq’ by (gvs[] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  drule_all acq_acct >> strip_tac >>
  ‘l0_chan_of w f = SOME c’ by gvs[acct_def] >>
  drule_all pdo_chan >> strip_tac >>
  qexists_tac ‘c’ >> simp[] >>
  ‘(EL (cl cm f) s.clients).outgoing = []’ by (qpat_x_assum ‘out_rel _ _ _ _’ mp_tac >> simp[out_rel_def] >> metis_tac[]) >>
  ‘MEM f (MAP FST cm)’ by simp[] >>
  drule_all hwrote_wbytes >> simp[wbytes_nil]
QED

Theorem pacts_out:
  ∀acts w ps s rs evs w' ps' s' hs' hrs hevs.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
    hacts lfd (s, hs_of ps) acts = SOME (hrs, hevs, (s', hs')) ∧
    pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧ EVERY small_send evs ∧
    out_rel cm w ps s ⇒
    out_rel cm w' ps' s'
Proof
  Induct >> simp[pacts_def, hacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘hdo _ _ _ = SOME (r2, st1, hevs1)’ >> PairCases_on ‘st1’ >>
  drule_all pdo_hdo >> strip_tac >> gvs[] >>
  drule_all pdo_out >> strip_tac >>
  drule_all pdo_winv >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* ------------------------------------------------------------------------
   The round's tail, stage by stage
   ------------------------------------------------------------------------ *)

Theorem acct_len:
  acct w b f c out ⇒ LENGTH (csent w c) ≤ LENGTH out
Proof
  rw[acct_def] >> Cases_on ‘MEM f b.gone’ >> gvs[] >>
  imp_res_tac IS_PREFIX_LENGTH >> rw[] >> simp[]
QED

Theorem l0_accept_chan:
  l0_accept l w = (Ok k, w') ∧ qfresh w ⇒
  ∃c. l0_chan_of w' (n2w k) = SOME c ∧ csent w' c = []
Proof
  rw[l0_accept_def] >> gvs[AllCaseEqs(), fail_def] >>
  gvs[qfresh_def] >>
  ‘MEM (v2, p, j :: q') (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
  ‘MEM (v2, p, j :: q') w.listeners’ by fs[MEM_FILTER] >>
  ‘j < LENGTH w.chans ∧ csent w j = []’
    by (qpat_x_assum ‘∀l p q j. _’ (qspecl_then [‘v2’, ‘p’, ‘j :: q'’, ‘j’] mp_tac) >>
        simp[]) >>
  qexists_tac ‘j’ >> gvs[l0_chan_of_def, csent_def]
QED

Theorem sys_accept_chan:
  sys_accept l w = SOME (out, w', ev) ∧ l0_res_of out = Ok k ∧ winv w ∧ qfresh w ⇒
  ∃c. l0_chan_of w' (n2w k) = SOME c ∧ csent w' c = []
Proof
  rw[sys_accept_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  ‘l0_rely (l0_tick «sys_accept» w)’
    by (irule l0_rely_ch >> qexists_tac ‘w’ >> gvs[winv_def]) >>
  drule_all honestL1InvTheory.l0_accept_res >> strip_tac >>
  gvs[l0_res_of_enc] >>
  ‘qfresh (l0_tick «sys_accept» w)’ by simp[qfresh_tick] >>
  drule_all l0_accept_chan >> simp[]
QED

Theorem chan_used:
  l0_chan_of w f = SOME c ⇒ MEM f (l0_used w)
Proof
  rw[l0_chan_of_def, l0_used_def, AllCaseEqs()] >> imp_res_tac ALOOKUP_MEM >>
  simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem sys_csents:
  (winv w ∧ l0_chan_of w f = SOME c ∧ sys_poll fes w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ ev_sent f ev = []) ∧
  (winv w ∧ l0_chan_of w f = SOME c ∧ sys_recv g k w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ ev_sent f ev = []) ∧
  (winv w ∧ l0_chan_of w f = SOME c ∧ sys_accept g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ ev_sent f ev = []) ∧
  (winv w ∧ l0_chan_of w f = SOME c ∧ g ≠ f ∧ sys_close g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ ev_sent f ev = [])
Proof
  rpt conj_tac >> strip_tac >> irule sys_csent >> simp[] >> metis_tac[]
QED

Theorem l1_polls_csent:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ l0_chan_of w f = SOME c ⇒
    l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ evs_sent f evs = []
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all (cj 1 sys_csents) >> strip_tac >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_keys:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ okeys b ⇒
    okeys b' ∧ b'.tbl = b.tbl ∧ b'.closing = b.closing
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘okeys (after_send h (l0_res_of out) b)’
    by (irule okeys_after_send >> gvs[okeys_def]) >>
  first_x_assum drule_all >> simp[]
QED

(* A flush leaves an fd with nothing to send alone *)
Theorem l1_flush_quiet:
  l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ EVERY small_send evs ∧
  l0_chan_of w f = SOME c ∧ outbox_of b f = [] ∧ ¬MEM f b.gone ⇒
  l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ evs_sent f evs = []
Proof
  strip_tac >>
  ‘acct w b f c (csent w c)’ by simp[acct_def] >>
  drule_all l1_flush_acct >> strip_tac >>
  drule acct_len >> gvs[acct_def] >> strip_tac >>
  ‘LENGTH (evs_sent f evs) = 0’ by decide_tac >> gvs[]
QED

Theorem sys_ev_sent:
  (sys_poll fes w = SOME (out, w', ev) ⇒ ∀f. ev_sent f ev = []) ∧
  (sys_recv g k w = SOME (out, w', ev) ⇒ ∀f. ev_sent f ev = []) ∧
  (sys_close g w = SOME (out, w', ev) ⇒ ∀f. ev_sent f ev = []) ∧
  (sys_accept g w = SOME (out, w', ev) ⇒ ∀f. ev_sent f ev = [])
Proof
  rw[sys_poll_def, sys_recv_def, sys_close_def, sys_accept_def] >>
  TRY (drule l0_do_buf_cases >> rw[] >> simp[ev_sent_def] >> NO_TAC) >>
  drule l0_do_cases >> rw[] >> simp[ev_sent_def]
QED

val chan_tac =
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘∀f c. l0_chan_of w f = SOME c ⇒ _’ drule >> strip_tac >>
  qpat_x_assum ‘∀f c. l0_chan_of w1 f = SOME c ⇒ _’ drule >> simp[];

val fconn_tac =
  qpat_x_assum ‘∀f. MEM (FConn f) log' ⇒ _’ drule >> strip_tac >>
  ‘∀c. l0_chan_of w f ≠ SOME c’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀f c. l0_chan_of w f = SOME c ⇒ _’ drule >> strip_tac >> gvs[]) >>
  simp[] >> qexists_tac ‘c'’ >> simp[];

(* The fetch sends nothing, keeps every channel, leaves L1's buffers of
   output alone, and pre-accepts fresh fds whose channels have nothing sent *)
Theorem pf_fetch_out:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ qfresh w ⇒
    ps'.b = ps.b ∧
    (∀f c. l0_chan_of w f = SOME c ⇒ l0_chan_of w' f = SOME c ∧ csent w' c = csent w c) ∧
    (∀f. evs_sent f evs = []) ∧
    (∀f. MEM f ps'.acq ⇔ MEM f ps.acq ∨ MEM (FConn f) log) ∧
    (∀f. MEM (FConn f) log ⇒
         (∃c. l0_chan_of w' f = SOME c ∧ csent w' c = []) ∧ ∀c. l0_chan_of w f ≠ SOME c)
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (g :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘g = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >>
      simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      ‘winv w1 ∧ qfresh w1’ by metis_tac[sys_winv, sys_qfresh] >>
      first_x_assum drule_all >> strip_tac >>
      ‘∀f c. l0_chan_of w f = SOME c ⇒ l0_chan_of w1 f = SOME c ∧ csent w1 c = csent w c’
        by (rpt gen_tac >> strip_tac >> drule_all (cj 3 sys_csents) >> simp[]) >>
      ‘∀f. ev_sent f ev = []’ by (drule (cj 4 sys_ev_sent) >> simp[]) >>
      Cases_on ‘l0_res_of out’ >> gvs[]
      >- (rename1 ‘l0_res_of out = Ok k’ >>
          ‘∃c. l0_chan_of w1 (n2w k) = SOME c ∧ csent w1 c = []’
            by (drule_all sys_accept_chan >> simp[]) >>
          ‘¬MEM (n2w k) (l0_used w)’
            by (qspecl_then [‘w’, ‘lfd’, ‘out’, ‘w1’, ‘ev’, ‘k’] mp_tac
                  (Q.GENL [‘w’, ‘l’, ‘out’, ‘w'’, ‘ev’, ‘k’] sys_accept_fresh) >>
                gvs[winv_def]) >>
          rpt conj_tac >> TRY (chan_tac >> NO_TAC) >>
          TRY (simp[DISJ_ASSOC] >> NO_TAC) >>
          gen_tac >> strip_tac
          >- (gvs[] >> qexists_tac ‘c’ >>
              qpat_x_assum ‘∀f c. l0_chan_of w1 f = SOME c ⇒ _’ drule >> strip_tac >>
              simp[] >> rpt strip_tac >> drule chan_used >> simp[])
          >> fconn_tac)
      >> rpt conj_tac >> TRY (chan_tac >> NO_TAC) >> TRY (rw[] >> gvs[] >> NO_TAC) >>
      gen_tac >> strip_tac >> fconn_tac)
  >> Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  ‘winv w1 ∧ qfresh w1’ by metis_tac[sys_winv, sys_qfresh] >>
  first_x_assum drule_all >> strip_tac >>
  ‘∀f c. l0_chan_of w f = SOME c ⇒ l0_chan_of w1 f = SOME c ∧ csent w1 c = csent w c’
    by (rpt gen_tac >> strip_tac >> drule_all (cj 2 sys_csents) >> simp[]) >>
  ‘∀f. ev_sent f ev = []’ by (drule (cj 2 sys_ev_sent) >> simp[]) >>
  ‘ps1.b = ps.b ∧ ps1.acq = ps.acq ∧ ∀f. ¬MEM (FConn f) fl'’
    by (qpat_x_assum ‘_ = (ps1, fl')’ mp_tac >> rw[AllCaseEqs()] >> gvs[]) >>
  gvs[] >> rpt conj_tac >> TRY (chan_tac >> NO_TAC) >> TRY (rw[] >> gvs[] >> NO_TAC) >>
  gen_tac >> strip_tac >> fconn_tac
QED

Theorem set_outbox_fields[simp]:
  (set_outbox f x b).tbl = b.tbl ∧ (set_outbox f x b).closing = b.closing ∧
  (set_outbox f x b).gone = b.gone ∧ (set_outbox f x b).nxt = b.nxt
Proof
  simp[set_outbox_def]
QED

Theorem outbox_of_gone[simp]:
  outbox_of (b with gone := x) f = outbox_of b f
Proof
  simp[outbox_of_def]
QED

(* Dropping an outbox (D19) keeps every account: a prefix is a prefix *)
Theorem acct_drop:
  acct w b f c out ⇒ acct w (drop_out b g) f c out
Proof
  rw[acct_def, drop_out_def, outbox_of_set_outbox, MEM_FILTER] >>
  Cases_on ‘g = f’ >> gvs[] >>
  Cases_on ‘MEM f b.gone’ >> gvs[] >>
  qpat_x_assum ‘_ = out’ (SUBST1_TAC o SYM) >> simp[IS_PREFIX_APPEND3]
QED

Theorem okeys_drop:
  okeys b ∧ (MEM g (MAP SND b.tbl) ∨ MEM g b.closing) ⇒ okeys (drop_out b g)
Proof
  rw[okeys_def, drop_out_def, outbox_of_set_outbox, MEM_FILTER] >>
  Cases_on ‘f = g’ >> gvs[] >> first_x_assum irule >> gvs[]
QED

Theorem FOLDL_drop_out:
  ∀l b. (FOLDL drop_out b l).tbl = b.tbl ∧ (FOLDL drop_out b l).closing = b.closing ∧
        (∀w f c out. acct w b f c out ⇒ acct w (FOLDL drop_out b l) f c out) ∧
        (okeys b ∧ EVERY (λg. MEM g (MAP SND b.tbl) ∨ MEM g b.closing) l ⇒
         okeys (FOLDL drop_out b l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘drop_out b h’ strip_assume_tac) >>
  ‘(drop_out b h).tbl = b.tbl ∧ (drop_out b h).closing = b.closing’
    by simp[drop_out_def] >>
  gvs[] >> rw[] >- metis_tac[acct_drop] >>
  first_x_assum irule >> simp[] >> irule okeys_drop >> simp[]
QED

Theorem stall_out:
  (stall_step hfs ob log ps).acq = ps.acq ∧
  (stall_step hfs ob log ps).b.tbl = ps.b.tbl ∧
  (stall_step hfs ob log ps).b.closing = ps.b.closing ∧
  (∀w f c out. acct w ps.b f c out ⇒ acct w (stall_step hfs ob log ps).b f c out) ∧
  (okeys ps.b ⇒ okeys (stall_step hfs ob log ps).b)
Proof
  simp[stall_step_def] >>
  qmatch_goalsub_abbrev_tac ‘FOLDL drop_out ps.b dl’ >>
  qspecl_then [‘dl’, ‘ps.b’] strip_assume_tac FOLDL_drop_out >> simp[] >>
  strip_tac >> first_x_assum irule >> simp[] >>
  simp[Abbr ‘dl’, EVERY_MAP, EVERY_FILTER, EVERY_MEM, FORALL_PROD] >>
  rw[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[MEM_FILTER, MEM_MAP, MEM_nub] >>
  every_case_tac >> gvs[]
QED

Theorem okeys_forget:
  okeys b ⇒ okeys (forget g b)
Proof
  rw[okeys_def, forget_keys, MEM_FILTER] >> Cases_on ‘f = g’ >> gvs[] >>
  first_x_assum irule >> gvs[]
QED

(* The reap closes only closing fds with nothing to send (or gone); any
   other fd keeps its channel, its account and its outbox *)
Theorem l1_reap_keep:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
    (MEM f fs ⇒ outbox_of b f ≠ [] ∧ ¬MEM f b.gone) ⇒
    l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧ evs_sent f evs = [] ∧
    outbox_of b' f = outbox_of b f ∧ (MEM f b'.gone ⇔ MEM f b.gone) ∧
    (okeys b ⇒ okeys b')
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> rename1 ‘l1_close h (w, b) = SOME ((w1, b1), evs1)’ >>
      ‘h ≠ f’ by (strip_tac >> gvs[]) >>
      ‘c < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
      drule_all l1_close_csent >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
      ‘l0_chan_of w1 f = SOME c’
        by (qpat_x_assum ‘l1_close _ _ = _’ mp_tac >> simp[l1_close_def, AllCaseEqs()] >>
            strip_tac >> irule sys_close_chan >> metis_tac[]) >>
      ‘winv w1’ by metis_tac[l1_close_winv] >>
      gvs[] >>
      first_x_assum (drule_at (Pos (el 1))) >> simp[forget_keys] >>
      ‘MEM f fs ⇒ ¬MEM f (FILTER (λy. h ≠ y) b.gone)’ by rw[MEM_FILTER] >>
      simp[] >> strip_tac >> gvs[forget_keys, MEM_FILTER] >> metis_tac[okeys_forget])
  >> ‘MEM f fs ⇒ outbox_of b f ≠ [] ∧ ¬MEM f b.gone’ by metis_tac[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_reap_closing:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ MEM f b'.closing ⇒
    MEM f b.closing ∧ (MEM f fs ⇒ outbox_of b f ≠ [] ∧ ¬MEM f b.gone)
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >>
      gvs[l1_close_def, AllCaseEqs()] >>
      first_x_assum drule_all >> simp[forget_keys, MEM_FILTER] >> rw[] >> gvs[])
  >> first_x_assum drule_all >> simp[] >> rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The version-2 world's side of the tail: a tick only adds clients, and
   they have nothing written
   ------------------------------------------------------------------------ *)

Definition cext_def:
  cext s s' ⇔
    LENGTH s.clients ≤ LENGTH s'.clients ∧
    (∀j. j < LENGTH s.clients ⇒ (EL j s'.clients).outgoing = (EL j s.clients).outgoing) ∧
    (∀j. LENGTH s.clients ≤ j ∧ j < LENGTH s'.clients ⇒ (EL j s'.clients).outgoing = [])
End

Theorem cext_deliver2:
  cext s s0 ⇒ cext s (deliver2 s0 a)
Proof
  Cases_on ‘a’ >> rw[deliver2_def, update_client_def] >>
  gvs[cext_def, EL_LUPDATE] >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  TRY (rw[] >> gvs[] >> NO_TAC) >>
  Cases_on ‘j < LENGTH s0.clients’ >> gvs[EL_APPEND1, EL_APPEND2] >>
  ‘j = LENGTH s0.clients’ by simp[] >> gvs[EL_APPEND2, ffiSpikeSocketFFITheory.empty_conn_def]
QED

Theorem cext_tick2:
  cext s (tick2 s)
Proof
  simp[tick2_def] >> CASE_TAC >- simp[cext_def] >>
  ‘∀as s0. cext s s0 ⇒ cext s (FOLDL deliver2 s0 as)’
    by (Induct >> simp[] >> metis_tac[cext_deliver2]) >>
  first_x_assum irule >> simp[cext_def]
QED

Theorem cext_hpoll:
  cext s (SND (hpoll lfd hs hfds s))
Proof
  simp[hpoll_def, sock_poll2_def, cext_tick2]
QED

(* ------------------------------------------------------------------------
   The tail
   ------------------------------------------------------------------------ *)

Theorem arrs_fconn:
  ∀l cm k as cm' k'.
    arrs lfd (cm, k) l = (as, (cm', k')) ⇒
    ∃new. cm' = new ++ cm ∧ ∀f. MEM f (MAP FST new) ⇔ MEM (FConn f) l
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
  gvs[] >> TRY (qexists_tac ‘new’ >> simp[] >> NO_TAC) >> metis_tac[]
QED

Theorem cl_append:
  (¬MEM f (MAP FST new) ⇒ cl (new ++ cm) f = cl cm f) ∧
  (MEM f (MAP FST new) ⇒ MEM (f, cl (new ++ cm) f) new)
Proof
  rw[cl_def, ALOOKUP_APPEND] >> every_case_tac >> gvs[ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem acct_same:
  acct w b f c out ∧ l0_chan_of w' f = SOME c ∧ csent w' c = csent w c ∧
  outbox_of b' f = outbox_of b f ∧ (MEM f b'.gone ⇔ MEM f b.gone) ⇒
  acct w' b' f c out
Proof
  simp[acct_def]
QED

Theorem l1_reap_okeys:
  ∀fs w b w' b' evs. l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ okeys b ⇒ okeys b'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> gvs[l1_close_def, AllCaseEqs()] >>
      first_x_assum irule >> metis_tac[okeys_forget])
  >> metis_tac[]
QED

Theorem pown_disjoint:
  pown lfd ps ⇒
  (MEM f ps.acq ⇒ ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing) ∧
  (MEM f (MAP SND ps.b.tbl) ⇒ ¬MEM f ps.b.closing)
Proof
  rw[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem arrs_new:
  arrs lfd (cm, k) l = (as, (cm', k')) ∧
  ALL_DISTINCT (MAP SND cm) ∧ EVERY (λj. j < k) (MAP SND cm) ⇒
  ∃new. cm' = new ++ cm ∧ (∀f. MEM f (MAP FST new) ⇔ MEM (FConn f) l) ∧
        EVERY (λj. k ≤ j ∧ j < k') (MAP SND new)
Proof
  strip_tac >> drule_all arrs_inv >> strip_tac >> drule arrs_fconn >> strip_tac >>
  rename1 ‘cm' = new1 ++ cm’ >>
  ‘new1 ++ cm = new ++ cm’ by metis_tac[] >>
  ‘LENGTH new1 = LENGTH new’
    by (‘LENGTH (new1 ++ cm) = LENGTH (new ++ cm)’ by metis_tac[] >> fs[]) >>
  ‘new1 = new’ by metis_tac[APPEND_LENGTH_EQ] >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

val not_new_tac =
  strip_tac >>
  ‘MEM (FConn f) log’
    by (qpat_x_assum ‘∀f. MEM f (MAP FST new) ⇔ _’
          (fn th => qpat_x_assum ‘MEM f (MAP FST new)’ (mp_tac o REWRITE_RULE [th])) >>
        simp[]) >>
  qpat_x_assum ‘∀f. MEM (FConn f) log ⇒ _’ drule >> strip_tac >>
  qpat_x_assum ‘∀c. l0_chan_of w2 f ≠ SOME c’ (qspec_then ‘c’ mp_tac) >> fs[];

Theorem tail_out:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧ EVERY small_send evs ∧ out_rel cm w ps s ∧
  arrs lfd (cm, LENGTH s.clients) log = (as, (cm', k')) ∧ cext s s' ∧
  k' = LENGTH s'.clients ⇒
  out_rel cm' w' ps' s'
Proof
  simp[pf_tail_def] >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol ps hs’ >>
  Cases_on ‘l1_polls [fes] w’ >> gvs[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘l1_polls _ _ = SOME (rv, w1, pevs)’ >> gvs[] >>
  Cases_on ‘l1_flush (writable_fds rv) (w1, ps.b)’ >> gvs[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >> gvs[] >>
  qmatch_asmsub_abbrev_tac ‘pf_fetch _ _ fs (w2, ps2)’ >>
  Cases_on ‘pf_fetch lfd pol fs (w2, ps2)’ >> gvs[] >> rename1 ‘_ = SOME z’ >>
  PairCases_on ‘z’ >> rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3f), log3, gevs)’ >> gvs[] >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3f) (outbox_of ps.b) log3 ps3f’ >>
  ‘ps3f.b.closing = ps3.b.closing ∧ ps3f.pause = ps3.pause’ by simp[Abbr ‘ps3’] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  Cases_on ‘l1_reap ps3.b.closing (w3, ps3.b)’ >> gvs[] >> rename1 ‘_ = SOME u’ >>
  PairCases_on ‘u’ >> rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >> gvs[] >>
  ‘qfresh w ∧ okeys ps.b’ by gvs[out_rel_def] >>
  ‘winv w1’ by (drule_all l1_polls_winv >> simp[]) >>
  ‘qfresh w1’ by (drule_all l1_polls_qfresh >> simp[]) >>
  ‘winv w2’ by (drule_all l1_flush_winv >> simp[]) >>
  ‘qfresh w2’ by (drule_all l1_flush_qfresh >> simp[]) >>
  ‘winv w3’ by (drule_all pf_fetch_winv >> simp[]) >>
  ‘qfresh w3’ by (drule_all pf_fetch_qfresh >> simp[]) >>
  ‘qfresh w'’ by (drule_all l1_reap_qfresh >> simp[]) >>
  drule_all pf_fetch_out >> strip_tac >>
  drule_all l1_flush_keys >> strip_tac >>
  ‘ps2.b = b2 ∧ ps2.acq = ps.acq’ by simp[Abbr ‘ps2’] >>
  qspecl_then [‘pf_held ps3f’, ‘outbox_of ps.b’, ‘log’, ‘ps3f’] mp_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_out) >>
  qpat_x_assum ‘Abbrev (ps3 = _)’
    (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] >>
              assume_tac th) >>
  strip_tac >>
  ‘okeys b4’ by (drule l1_reap_okeys >> gvs[]) >>
  ‘b4.tbl = ps3.b.tbl’ by (drule l1_reap_l0 >> gvs[winv_def]) >>
  ‘ALL_DISTINCT (MAP SND cm) ∧ EVERY (λj. j < LENGTH s.clients) (MAP SND cm)’
    by fs[pv_rel_def] >>
  drule_all arrs_new >> strip_tac >> gvs[] >>
  simp[out_rel_def] >> rpt conj_tac
  >- ((* held fds *)
      gen_tac >> disch_then assume_tac >>
      ‘¬(¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing) ∧
       (MEM f ps.b.closing ⇒ outbox_of ps3.b f ≠ [] ∧ ¬MEM f ps3.b.gone)’
        by (qpat_x_assum ‘_ ∨ _’ strip_assume_tac
            >- (‘MEM f (MAP SND ps.b.tbl)’ by fs[] >> drule pown_disjoint >> fs[])
            >> drule_all l1_reap_closing >> fs[]) >>
      ‘MEM f (MAP FST cm) ∧ ∃c. acct w ps.b f c (EL (cl cm f) s.clients).outgoing’
        by (qpat_x_assum ‘out_rel _ _ _ _’ mp_tac >> simp[out_rel_def] >> strip_tac >>
            qpat_x_assum ‘∀f. MEM f (MAP SND ps.b.tbl) ∨ _ ⇒ _’ (qspec_then ‘f’ mp_tac) >>
            impl_tac >- (qpat_x_assum ‘¬(_ ∧ _)’ mp_tac >> simp[]) >>
            simp[]) >>
      ‘l0_chan_of w f = SOME c’ by fs[acct_def] >>
      drule_all l1_polls_csent >> strip_tac >>
      ‘acct w1 ps.b f c (EL (cl cm f) s.clients).outgoing’
        by (qpat_x_assum ‘acct w _ _ _ _’ mp_tac >> simp[acct_def]) >>
      drule_all l1_flush_acct >> strip_tac >>
      ‘l0_chan_of w2 f = SOME c’ by (qpat_x_assum ‘acct w2 _ _ _ _’ mp_tac >> simp[acct_def]) >>
      ‘l0_chan_of w3 f = SOME c ∧ csent w3 c = csent w2 c’
        by (qpat_x_assum ‘∀f c. l0_chan_of w2 f = SOME c ⇒ _’ drule >> simp[]) >>
      ‘acct w3 ps3f.b f c (EL (cl cm f) s.clients).outgoing’
        by (qpat_x_assum ‘acct w2 _ _ _ _’ mp_tac >> simp[acct_def]) >>
      ‘acct w3 ps3.b f c (EL (cl cm f) s.clients).outgoing’
        by (qpat_x_assum ‘∀w f c out. acct w ps3f.b f c out ⇒ _’ drule >> simp[]) >>
      ‘l0_chan_of w' f = SOME c ∧ csent w' c = csent w3 c ∧
       outbox_of b4 f = outbox_of ps3.b f ∧ (MEM f b4.gone ⇔ MEM f ps3.b.gone)’
        by (qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule l1_reap_keep >>
            disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> fs[]) >>
      ‘¬MEM f (MAP FST new)’ by not_new_tac >>
      ‘cl (new ++ cm) f = cl cm f’ by (irule (cj 1 cl_append) >> first_assum ACCEPT_TAC) >>
      ‘cl cm f < LENGTH s.clients’ by (drule cl_mem >> fs[EVERY_MEM]) >>
      ‘(EL (cl cm f) s'.clients).outgoing = (EL (cl cm f) s.clients).outgoing’
        by fs[cext_def] >>
      conj_tac >- fs[] >>
      qexists_tac ‘c’ >>
      qpat_x_assum ‘cl (new ++ cm) f = _’ SUBST1_TAC >>
      qpat_x_assum ‘(EL (cl cm f) s'.clients).outgoing = _’ SUBST1_TAC >>
      mp_tac (Q.INST [‘w’ |-> ‘w3’, ‘b’ |-> ‘ps3.b’, ‘b'’ |-> ‘b4’,
                      ‘out’ |-> ‘(EL (cl cm f) s.clients).outgoing’] acct_same) >>
      disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >> (* pre-accepted fds *)
  gen_tac >> strip_tac
  >~ [‘MEM f ps.acq’]
  >- (‘∃c. l0_chan_of w f = SOME c ∧ csent w c = [] ∧
          (EL (cl cm f) s.clients).outgoing = []’
        by (qpat_x_assum ‘out_rel _ _ _ _’ mp_tac >> simp[out_rel_def] >> strip_tac >>
            first_x_assum (qspec_then ‘f’ mp_tac) >> fs[]) >>
      ‘MEM f (MAP FST cm)’ by fs[pv_rel_def] >>
      ‘¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing’ by (drule pown_disjoint >> fs[]) >>
      ‘outbox_of ps.b f = [] ∧ ¬MEM f ps.b.gone’
        by (qpat_x_assum ‘okeys ps.b’ (mp_tac o REWRITE_RULE [okeys_def]) >>
            disch_then (qspec_then ‘f’ mp_tac) >> fs[]) >>
      drule_all l1_polls_csent >> strip_tac >>
      ‘l0_chan_of w2 f = SOME c ∧ csent w2 c = csent w1 c’
        by (qpat_x_assum ‘l1_flush _ _ = _’ assume_tac >> drule l1_flush_quiet >>
            disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> fs[]) >>
      ‘l0_chan_of w3 f = SOME c ∧ csent w3 c = csent w2 c’
        by (qpat_x_assum ‘∀f c. l0_chan_of w2 f = SOME c ⇒ _’ drule >> simp[]) >>
      ‘l0_chan_of w' f = SOME c ∧ csent w' c = csent w3 c’
        by (qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule l1_reap_keep >>
            disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> fs[]) >>
      ‘¬MEM f (MAP FST new)’ by not_new_tac >>
      ‘cl (new ++ cm) f = cl cm f’ by (irule (cj 1 cl_append) >> first_assum ACCEPT_TAC) >>
      ‘cl cm f < LENGTH s.clients’ by (drule cl_mem >> fs[EVERY_MEM]) >>
      qexists_tac ‘c’ >> fs[cext_def])
  >> (* fetched in this round *)
  qpat_x_assum ‘∀f. MEM (FConn f) log ⇒ _’ drule >> strip_tac >>
  ‘¬MEM f ps.b.closing’
    by (strip_tac >>
        ‘∃c'. acct w ps.b f c' (EL (cl cm f) s.clients).outgoing’
          by (qpat_x_assum ‘out_rel _ _ _ _’ mp_tac >> simp[out_rel_def] >> strip_tac >>
              qpat_x_assum ‘∀f. MEM f (MAP SND ps.b.tbl) ∨ _ ⇒ _’ (qspec_then ‘f’ mp_tac) >>
              simp[] >> strip_tac >> qexists_tac ‘c’ >> simp[]) >>
        ‘l0_chan_of w f = SOME c'’ by fs[acct_def] >>
        drule_all l1_polls_csent >> strip_tac >>
        ‘acct w1 ps.b f c' (EL (cl cm f) s.clients).outgoing’
          by fs[acct_def] >>
        drule_all l1_flush_acct >> strip_tac >>
        ‘l0_chan_of w2 f = SOME c'’ by fs[acct_def] >>
        qpat_x_assum ‘∀c. l0_chan_of w2 f ≠ SOME c’ (qspec_then ‘c'’ mp_tac) >> simp[]) >>
  ‘l0_chan_of w' f = SOME c ∧ csent w' c = csent w3 c’
    by (qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule l1_reap_keep >>
        disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> fs[]) >>
  ‘MEM f (MAP FST new)’
    by (qpat_x_assum ‘∀f. MEM f (MAP FST new) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
        first_assum ACCEPT_TAC) >>
  drule (cj 2 cl_append) >> disch_then (qspec_then ‘cm’ assume_tac) >>
  ‘LENGTH s.clients ≤ cl (new ++ cm) f ∧ cl (new ++ cm) f < LENGTH s'.clients’
    by (qpat_x_assum ‘EVERY _ (MAP SND new)’ mp_tac >>
        simp[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> disch_then drule >> simp[]) >>
  qexists_tac ‘c’ >> fs[cext_def]
QED

(* ------------------------------------------------------------------------
   One round, and the run
   ------------------------------------------------------------------------ *)

Theorem round_out:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ winv w ∧
  EVERY small_send evs ∧ out_rel cm w ps s ∧
  arrs lfd (cm, LENGTH s.clients) log = (as, (cm', k')) ∧
  (∀f j. MEM (f, j) cm' ∧ LENGTH s.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s.alloc j used = f) ∧
  LHD s.future = SOME as ∧ k' + 1 < dimword (:64) ⇒
  ∃rs hevs s1.
    hacts lfd (s, hs_of ps) acts = SOME (rs, hevs, (s1, hs_of ps')) ∧
    out_rel cm' w' ps' (SND (hpoll lfd (hs_of ps') hs s1)) ∧ winv w'
Proof
  strip_tac >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[winv_def] >>
  drule_all round_rel >> strip_tac >>
  ‘winv w'’ by (drule_all pround_winv >> simp[]) >>
  qexistsl_tac [‘rs’, ‘hevs’, ‘s1’] >> ASM_REWRITE_TAC [] >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[pround_def, AllCaseEqs()] >>
  strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  rename1 ‘pacts _ _ _ = SOME (rs1, aevs, (w1, ps1))’ >>
  drule_all pacts_hacts >> strip_tac >> gvs[] >>
  drule_all pacts_out >> strip_tac >>
  drule_all pacts_winv >> strip_tac >>
  drule hacts_world >> strip_tac >>
  mp_tac (Q.INST [‘w’ |-> ‘w1’, ‘ps’ |-> ‘ps1’, ‘evs’ |-> ‘tevs’, ‘s’ |-> ‘s'’,
                  ‘s'’ |-> ‘SND (hpoll lfd (hs_of ps') hs s')’,
                  ‘k'’ |-> ‘LENGTH (SND (hpoll lfd (hs_of ps') hs s')).clients’] tail_out) >>
  impl_tac >- fs[cext_hpoll] >> simp[]
QED

(* MAIN (R1-safe, output side), for the rounds up to N: on a run whose
   sends each record their count (small_send, an explicit hypothesis on the
   trace), in a world whose queued connections have nothing sent (qfresh),
   every fd L1 holds has its account: what the kernel took on its channel,
   then L1's outbox, is what the server wrote to its client in psk (a
   prefix once the fd is gone) *)
Theorem l1pf_refines_hl_out_upto:
  winv w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ N ⇒ SND (pcm lfd pol ifds m w0 n') + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    n ≤ N ∧ prounds lfd pol ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ∧
    EVERY small_send evs ⇒
    out_rel (FST (pcm lfd pol ifds m w0 n)) (FST ws) (SND ws)
      (FST (hst lfd ifds m (psk lfd pol ifds m w0) n)) ∧ winv (FST ws)
Proof
  strip_tac >>
  ‘l0_rely w0 ∧ fds_lt w0’ by gvs[winv_def] >>
  Induct
  >- (simp[prounds_def, hst_def, hrounds_def, pcm_def, psk_def] >>
      rw[] >> simp[out_rel_def, okeys_def, pinit_def, l1init_def, outbox_of_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘prounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [prounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘prounds _ _ _ _ _ n = SOME (h0, ws0, evs0, logs0)’ >>
  ‘n ≤ N’ by simp[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [EVERY_APPEND]) >>
  qpat_x_assum ‘EVERY _ evs0 ∧ _’ strip_assume_tac >>
  qpat_x_assum ‘∀h ws evs logs. _’ drule_all >> strip_tac >>
  mp_tac (Q.INST [‘N’ |-> ‘N’] l1pf_refines_hl_upto) >> impl_tac >- simp[] >>
  disch_then drule_all >> strip_tac >>
  ‘hacts_of lfd ifds m (psk lfd pol ifds m w0) n = new_actions (log_of m) h0’
    by simp[hacts_of_def] >>
  PairCases_on ‘ws0’ >> rename1 ‘prounds _ _ _ _ _ n = SOME (h0, (w, ps), evs0, logs0)’ >>
  PairCases_on ‘ws’ >> rename1 ‘pround _ _ _ _ _ = SOME (snap, (w', ps'), log, _)’ >>
  gvs[] >>
  Cases_on ‘hst lfd ifds m (psk lfd pol ifds m w0) n’ >> rename1 ‘_ = (s, hs)’ >> gvs[] >>
  ‘plog lfd pol ifds m w0 n = log’
    by (drule prounds_logs >> strip_tac >>
        qpat_x_assum ‘prounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule plog_EL >> disch_then (qspec_then ‘n’ mp_tac) >>
        simp[EL_APPEND2]) >>
  Cases_on ‘pcm lfd pol ifds m w0 n’ >> rename1 ‘pcm _ _ _ _ _ n = (cm, k)’ >> gvs[] >>
  Cases_on ‘arrs lfd (cm, LENGTH s.clients) (plog lfd pol ifds m w0 n)’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >>
  ‘pcm lfd pol ifds m w0 (SUC n) = (ck0, ck1) ∧ parr lfd pol ifds m w0 n = as’
    by simp[pcm_def, parr_def] >>
  ‘∀f j. MEM (f, j) ck0 ∧ LENGTH s.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s.alloc j used = f’
    by (rw[] >> irule run_alloc_eq >> simp[] >> qexists_tac ‘SUC n’ >> simp[]) >>
  ‘LHD s.future = SOME as’ by simp[] >>
  ‘ck1 + 1 < dimword (:64)’
    by (qpat_assum ‘∀n'. _ ≤ N ⇒ SND (pcm _ _ _ _ _ n') + 1 < _’ (mp_tac o Q.SPEC ‘SUC n’) >>
        qpat_assum ‘pcm _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        simp[]) >>
  drule_all round_out >> strip_tac >>
  ‘hacts_tot lfd (hst lfd ifds m (psk lfd pol ifds m w0) n)
     (hacts_of lfd ifds m (psk lfd pol ifds m w0) n) = (rs, hevs, (s1, hs_of ps'))’
    by simp[hacts_tot_def] >>
  drule hround_step >> strip_tac >> simp[]
QED

Theorem l1pf_refines_hl_out:
  winv w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    prounds lfd pol ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ∧
    EVERY small_send evs ⇒
    out_rel (FST (pcm lfd pol ifds m w0 n)) (FST ws) (SND ws)
      (FST (hst lfd ifds m (psk lfd pol ifds m w0) n))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPEC ‘n’ (Q.GEN ‘N’ l1pf_refines_hl_out_upto)) >>
  impl_tac >- fs[] >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Step 2: round by round on the raw trace.  Through a round, an fd that L1
   holds (or has pre-accepted) at the start is followed until it is closed:
   while live, its channel's sent is the start's plus what the round's
   sys_send events took on it; once closed (dead), that sum is a prefix of
   what the server wrote, and no later event of the round sends on it
   ------------------------------------------------------------------------ *)

Definition tk_def:
  tk live w ps f c tsum out ⇔
    (live ⇒ (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq) ∧
            csent w c = tsum ∧ acct w ps.b f c out) ∧
    (¬live ⇒ tsum ≼ out ∧ ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing ∧
             outbox_of ps.b f = [] ∧ ¬MEM f ps.b.gone)
End

Theorem sys_send_other:
  sys_send g bs w = SOME (out, w', ev) ∧ g ≠ f ⇒ ev_sent f ev = []
Proof
  rw[sys_send_def] >> drule l0_do_cases >> rw[] >>
  simp[ev_sent_def, taken_def, MAP_SND_ZIP_REPLICATE] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  simp[TAKE_APPEND1, TAKE_LENGTH_ID_rwt]
QED

Theorem outbox_of_after_send_other:
  g ≠ f ⇒ outbox_of (after_send g r b) f = outbox_of b f ∧
          (MEM f (after_send g r b).gone ⇔ MEM f b.gone)
Proof
  rw[after_send_def] >> every_case_tac >> simp[outbox_of_set_outbox, MEM_FILTER]
QED

(* An action on others: f (without a handle) is untouched *)
Theorem pdo_quiet:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ∧
  ¬MEM f (MAP SND ps.b.tbl) ⇒
  evs_sent f evs = [] ∧ outbox_of ps'.b f = outbox_of ps.b f ∧
  (MEM f ps'.b.gone ⇔ MEM f ps.b.gone) ∧ (MEM f ps'.b.closing ⇔ MEM f ps.b.closing) ∧
  (MEM f (MAP SND ps'.b.tbl) ⇒ MEM f ps.acq) ∧ (MEM f ps'.acq ⇒ MEM f ps.acq)
Proof
  strip_tac >>
  ‘∀h g. ALOOKUP ps.b.tbl h = SOME g ⇒ g ≠ f’
    by (rpt strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >>
        metis_tac[SND]) >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> res_tac >>
  gvs[forget_keys, MEM_FILTER, outbox_of_set_outbox, outbox_of_after_send_other] >>
  TRY (drule (cj 3 sys_ev_sent) >> simp[] >> NO_TAC) >>
  TRY (drule_all sys_send_other >> simp[] >> NO_TAC) >>
  TRY (‘f' ≠ f’ by (strip_tac >> gvs[])) >> gvs[] >>
  imp_res_tac MEM_SND_ADELKEY_sub >> gvs[] >>
  simp[outbox_of_after_send_other, outbox_of_set_outbox] >>
  TRY (drule_all sys_send_other >> simp[])
QED

(* An action that loses f closed it: f had nothing to send (or was gone) *)
Theorem pdo_closed:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ∧
  ¬(¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing ∧ ¬MEM f ps.acq) ∧
  ¬MEM f (MAP SND ps'.b.tbl) ∧ ¬MEM f ps'.b.closing ∧ ¬MEM f ps'.acq ⇒
  evs_sent f evs = [] ∧ wbytes f ps.b a = [] ∧
  (outbox_of ps.b f = [] ∨ MEM f ps.b.gone) ∧ MEM f (MAP SND ps.b.tbl) ∧
  outbox_of ps'.b f = [] ∧ ¬MEM f ps'.b.gone
Proof
  strip_tac >>
  ‘ALL_DISTINCT (MAP FST ps.b.tbl) ∧ ALL_DISTINCT (MAP SND ps.b.tbl)’
    by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >>
  gvs[forget_keys, MEM_FILTER, wbytes_def] >>
  TRY (drule (cj 3 sys_ev_sent) >> simp[] >> NO_TAC) >>
  TRY (‘f = f'’ by (qspecl_then [‘ps.b.tbl’, ‘c’, ‘f'’, ‘f’] mp_tac
                      (Q.GENL [‘l’, ‘h’, ‘f’, ‘g’] MEM_SND_ADELKEY) >> fs[]) >>
       gvs[] >> NO_TAC) >>
  imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem pdo_tk:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ pown lfd ps ∧
  EVERY small_send evs ∧ tk live w ps f c ts out ∧ (¬live ⇒ ¬MEM f ps.acq) ⇒
  ∃live'. tk live' w' ps' f c (ts ++ evs_sent f evs) (out ++ wbytes f ps.b a) ∧
          (¬live' ⇒ ¬MEM f ps'.acq)
Proof
  strip_tac >> qpat_x_assum ‘tk _ _ _ _ _ _ _’ mp_tac >> Cases_on ‘live’ >>
  simp_tac bool_ss [tk_def] >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  simp_tac bool_ss [tk_def]
  >- (Cases_on ‘MEM f (MAP SND ps'.b.tbl) ∨ MEM f ps'.b.closing ∨ MEM f ps'.acq’
      >- (qexists_tac ‘T’ >> simp[] >>
          ‘l0_chan_of w f = SOME c’ by fs[acct_def] >>
          drule_all pdo_acct >> disch_then (qspec_then ‘out’ strip_assume_tac) >>
          rpt conj_tac >> TRY (fs[] >> NO_TAC) >>
          Cases_on ‘MEM f (MAP SND ps'.b.tbl) ∨ MEM f ps'.b.closing’
          >- (first_x_assum irule >> fs[]) >>
          ‘MEM f ps'.acq’ by fs[] >>
          ‘MEM f ps.acq’ by (drule pdo_lfd >> strip_tac >> gvs[] >>
                             metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
          ‘¬MEM f (MAP SND ps.b.tbl)’ by metis_tac[pown_disjoint] >>
          drule_all pdo_chan >> strip_tac >>
          drule_all pdo_quiet >> strip_tac >>
          simp[wbytes_nil] >>
          mp_tac (Q.INST [‘b’ |-> ‘ps.b’, ‘b'’ |-> ‘ps'.b’] acct_same) >>
          disch_then irule >> fs[])
      >> qexists_tac ‘F’ >> simp[] >>
      ‘¬(¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing ∧ ¬MEM f ps.acq)’ by fs[] >>
      ‘¬MEM f (MAP SND ps'.b.tbl) ∧ ¬MEM f ps'.b.closing ∧ ¬MEM f ps'.acq’ by fs[] >>
      drule_all pdo_closed >> strip_tac >> fs[acct_def] >>
      Cases_on ‘MEM f ps.b.gone’ >> gvs[])
  >> qexists_tac ‘F’ >> simp[] >>
  drule_all pdo_quiet >> strip_tac >> simp[wbytes_nil] >>
  fs[] >> metis_tac[]
QED

Theorem pacts_tk:
  ∀acts w ps s rs evs w' ps' s' hs' hrs hevs live ts.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
    hacts lfd (s, hs_of ps) acts = SOME (hrs, hevs, (s', hs')) ∧
    pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧ EVERY small_send evs ∧
    MEM f (MAP FST cm) ∧
    tk live w ps f c ts (EL (cl cm f) s.clients).outgoing ∧ (¬live ⇒ ¬MEM f ps.acq) ⇒
    ∃live'. tk live' w' ps' f c (ts ++ evs_sent f evs) (EL (cl cm f) s'.clients).outgoing ∧
            (¬live' ⇒ ¬MEM f ps'.acq)
Proof
  Induct >> simp[pacts_def, hacts_def]
  >- (rpt strip_tac >> gvs[] >> qexists_tac ‘live’ >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘hdo _ _ _ = SOME (r2, st1, hevs1)’ >> PairCases_on ‘st1’ >>
  drule_all pdo_hdo >> strip_tac >> gvs[] >>
  ‘EVERY small_send evs1 ∧ EVERY small_send evs'’ by fs[] >>
  drule_all pdo_tk >> strip_tac >>
  drule_all pdo_winv >> strip_tac >>
  drule hdo_out >> strip_tac >>
  first_x_assum (qspec_then ‘cl cm f’ assume_tac) >>
  ‘hwrote s (hs_of ps) h (cl cm f) = wbytes f ps.b h’ by metis_tac[hwrote_wbytes] >>
  qpat_x_assum ‘hwrote _ _ _ _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum ‘tk live' _ _ _ _ _ _’ mp_tac >>
  qpat_x_assum ‘(EL (cl cm f) _.clients).outgoing = _’ (SUBST1_TAC o SYM) >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac ‘live''’ >> fs[]
QED

Theorem l1_polls_quiet:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒ ∀f. evs_sent f evs = []
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule (cj 1 sys_ev_sent) >> first_x_assum drule >> simp[]
QED

Theorem l1_flush_other:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ outbox_of b f = [] ⇒
    evs_sent f evs = [] ∧ outbox_of b' f = [] ∧ (MEM f b'.gone ⇔ MEM f b.gone)
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘h ≠ f’ by (strip_tac >> gvs[]) >>
  drule_all sys_send_other >> strip_tac >>
  first_x_assum (qspecl_then [‘w''’, ‘after_send h (l0_res_of out) b’] mp_tac) >>
  simp[outbox_of_after_send_other]
QED

Theorem FOLDL_drop_other:
  ∀dl b. ¬MEM f dl ⇒
         outbox_of (FOLDL drop_out b dl) f = outbox_of b f ∧
         (MEM f (FOLDL drop_out b dl).gone ⇔ MEM f b.gone)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then ‘drop_out b h’ mp_tac) >> simp[] >>
  simp[drop_out_def, outbox_of_set_outbox, MEM_FILTER]
QED

Theorem stall_other:
  ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing ⇒
  outbox_of (stall_step hfs ob log ps).b f = outbox_of ps.b f ∧
  (MEM f (stall_step hfs ob log ps).b.gone ⇔ MEM f ps.b.gone)
Proof
  strip_tac >> simp[stall_step_def] >>
  qmatch_goalsub_abbrev_tac ‘FOLDL drop_out ps.b dl’ >>
  ‘EVERY (λg. MEM g (MAP SND ps.b.tbl) ∨ MEM g ps.b.closing) dl’
    by (simp[Abbr ‘dl’, EVERY_MAP, EVERY_FILTER, EVERY_MEM, FORALL_PROD] >>
        rw[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[MEM_FILTER, MEM_MAP, MEM_nub] >>
        every_case_tac >> gvs[]) >>
  ‘¬MEM f dl’ by (strip_tac >> gvs[EVERY_MEM] >> res_tac) >>
  drule FOLDL_drop_other >> simp[]
QED

Theorem l1_reap_other:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ ¬MEM f fs ⇒
    evs_sent f evs = [] ∧ outbox_of b' f = outbox_of b f ∧ (MEM f b'.gone ⇔ MEM f b.gone)
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> gvs[l1_close_def, AllCaseEqs()] >>
      drule (cj 3 sys_ev_sent) >> strip_tac >>
      first_x_assum drule_all >> simp[forget_keys, MEM_FILTER])
  >> first_x_assum drule_all >> simp[]
QED

Theorem l1_reap_csent:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ c < LENGTH w.chans ⇒
    csent w' c = csent w c ∧ evs_sent f evs = []
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >>
      drule_all l1_close_csent >> disch_then (qspec_then ‘f’ strip_assume_tac) >> gvs[] >>
      ‘winv q’ by metis_tac[l1_close_winv] >>
      first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem l1_reap_clean:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ outbox_of b f = [] ∧ ¬MEM f b.gone ⇒
    outbox_of b' f = [] ∧ ¬MEM f b'.gone
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> gvs[l1_close_def, AllCaseEqs()] >>
      first_x_assum drule >> fs[forget_keys, MEM_FILTER] >> rw[] >> fs[])
  >> first_x_assum drule_all >> simp[]
QED

(* A closing fd the reap lets go: it had nothing to send (or was gone) *)
Theorem l1_reap_dead:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ c < LENGTH w.chans ∧
    ¬MEM f b'.closing ∧ MEM f b.closing ⇒
    evs_sent f evs = [] ∧ csent w' c = csent w c ∧
    (outbox_of b f = [] ∨ MEM f b.gone) ∧ outbox_of b' f = [] ∧ ¬MEM f b'.gone
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  drule_all l1_reap_csent >> strip_tac >> simp[] >>
  qpat_x_assum ‘l1_reap _ _ = _’ mp_tac >> simp[l1_reap_def]
  >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> rename1 ‘l1_close h _ = SOME ((w1, b1), evs1)’ >>
      drule_all l1_close_csent >> disch_then (qspec_then ‘f’ strip_assume_tac) >> gvs[] >>
      ‘winv w1’ by metis_tac[l1_close_winv] >>
      Cases_on ‘h = f’ >> gvs[] >>
      TRY (‘outbox_of (forget f b) f = [] ∧ ¬MEM f (forget f b).gone’
             by simp[forget_keys, MEM_FILTER] >>
           drule_all l1_reap_clean >> simp[] >> NO_TAC) >>
      first_x_assum drule >> simp[forget_keys, MEM_FILTER])
  >> first_x_assum drule_all >> simp[]
QED

Theorem chan_lt:
  l0_chan_of w f = SOME c ⇒ c < LENGTH w.chans
Proof
  rw[l0_chan_of_def, AllCaseEqs()] >> simp[]
QED

Theorem l1_flush_fields:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒ b'.tbl = b.tbl ∧ b'.closing = b.closing
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem tail_tk:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  winv w ∧ qfresh w ∧ pown lfd ps ∧ EVERY small_send evs ∧ tk live w ps f c ts out ⇒
  ∃live'. tk live' w' ps' f c (ts ++ evs_sent f evs) out
Proof
  simp[pf_tail_def] >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol ps hs’ >>
  Cases_on ‘l1_polls [fes] w’ >> gvs[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘l1_polls _ _ = SOME (rv, w1, pevs)’ >> gvs[] >>
  Cases_on ‘l1_flush (writable_fds rv) (w1, ps.b)’ >> gvs[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >> gvs[] >>
  qmatch_asmsub_abbrev_tac ‘pf_fetch _ _ fs (w2, ps2)’ >>
  Cases_on ‘pf_fetch lfd pol fs (w2, ps2)’ >> gvs[] >> rename1 ‘_ = SOME z’ >>
  PairCases_on ‘z’ >> rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3f), log3, gevs)’ >> gvs[] >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3f) (outbox_of ps.b) log3 ps3f’ >>
  ‘ps3f.b.closing = ps3.b.closing ∧ ps3f.pause = ps3.pause’ by simp[Abbr ‘ps3’] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  Cases_on ‘l1_reap ps3.b.closing (w3, ps3.b)’ >> gvs[] >> rename1 ‘_ = SOME u’ >>
  PairCases_on ‘u’ >> rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >> gvs[] >>
  ‘winv w1’ by (drule_all l1_polls_winv >> simp[]) >>
  ‘qfresh w1’ by (drule_all l1_polls_qfresh >> simp[]) >>
  ‘winv w2’ by (drule_all l1_flush_winv >> simp[]) >>
  ‘qfresh w2’ by (drule_all l1_flush_qfresh >> simp[]) >>
  ‘winv w3’ by (drule_all pf_fetch_winv >> simp[]) >>
  drule_all pf_fetch_out >> strip_tac >>
  ‘ps2.b = b2 ∧ ps2.acq = ps.acq’ by simp[Abbr ‘ps2’] >>
  qspecl_then [‘pf_held ps3f’, ‘outbox_of ps.b’, ‘log’, ‘ps3f’] mp_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_out) >>
  qpat_x_assum ‘Abbrev (ps3 = _)’
    (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] >>
              assume_tac th) >>
  strip_tac >>
  ‘b4.tbl = ps3.b.tbl’ by (drule l1_reap_l0 >> gvs[winv_def]) >>
  drule l1_flush_fields >> strip_tac >>
  ‘evs_sent f pevs = []’ by (drule l1_polls_quiet >> simp[]) >>
  ‘evs_sent f gevs = []’ by simp[] >>
  ‘ps3.b.closing = ps.b.closing ∧ ps3.b.tbl = ps.b.tbl’ by fs[] >>
  ‘∀g. MEM g b4.closing ⇒ MEM g ps.b.closing ∧
                          (MEM g ps.b.closing ⇒ outbox_of ps3.b g ≠ [] ∧ ¬MEM g ps3.b.gone)’
    by (rpt strip_tac >> drule_all l1_reap_closing >> gvs[]) >>
  qpat_x_assum ‘tk _ _ _ _ _ _ _’ mp_tac >> Cases_on ‘live’ >>
  simp_tac bool_ss [tk_def] >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >- ((* live *)
      ‘l0_chan_of w f = SOME c’
        by (qpat_x_assum ‘acct w _ _ _ _’ mp_tac >> simp[acct_def]) >>
      drule_all l1_polls_csent >> strip_tac >>
      ‘acct w1 ps.b f c out’
        by (mp_tac (Q.INST [‘w'’ |-> ‘w1’, ‘b’ |-> ‘ps.b’] acct_keep) >>
            disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      drule_all l1_flush_acct >> strip_tac >>
      ‘l0_chan_of w2 f = SOME c’
        by (qpat_x_assum ‘acct w2 _ _ _ _’ mp_tac >> simp[acct_def]) >>
      ‘l0_chan_of w3 f = SOME c ∧ csent w3 c = csent w2 c’
        by (qpat_x_assum ‘∀f c. l0_chan_of w2 f = SOME c ⇒ _’ drule >> simp[]) >>
      ‘ps3f.b = b2’
        by (qpat_x_assum ‘ps3f.b = ps2.b’ SUBST1_TAC >> qpat_x_assum ‘ps2.b = b2’ ACCEPT_TAC) >>
      ‘acct w3 ps3f.b f c out’
        by (mp_tac (Q.INST [‘w’ |-> ‘w2’, ‘w'’ |-> ‘w3’, ‘b’ |-> ‘ps3f.b’] acct_keep) >>
            disch_then irule >> qpat_x_assum ‘ps3f.b = b2’ SUBST1_TAC >>
            rpt conj_tac >> first_assum ACCEPT_TAC) >>
      ‘acct w3 ps3.b f c out’
        by (qpat_x_assum ‘∀w f c out. acct w ps3f.b f c out ⇒ _’ drule >> simp[]) >>
      ‘c < LENGTH w3.chans’
        by (irule chan_lt >> qexists_tac ‘f’ >> first_assum ACCEPT_TAC) >>
      Cases_on ‘MEM f ps.b.closing ∧ ¬MEM f b4.closing’
      >- (qpat_x_assum ‘MEM f ps.b.closing ∧ ¬MEM f b4.closing’ strip_assume_tac >>
          ‘MEM f ps3.b.closing’ by fs[] >>
          drule_all l1_reap_dead >> strip_tac >>
          qexists_tac ‘F’ >> simp[tk_def] >>
          ‘¬MEM f (MAP SND ps.b.tbl)’ by metis_tac[pown_disjoint] >>
          fs[acct_def] >> Cases_on ‘MEM f ps3.b.gone’ >> gvs[]) >>
      ‘MEM f ps.b.closing ⇒ outbox_of ps3.b f ≠ [] ∧ ¬MEM f ps3.b.gone’
        by (strip_tac >>
            ‘MEM f b4.closing’ by (qpat_x_assum ‘¬(_ ∧ _)’ mp_tac >> simp[]) >>
            qpat_x_assum ‘∀g. MEM g b4.closing ⇒ _’ drule >> simp[]) >>
      ‘MEM f ps3.b.closing ⇒ outbox_of ps3.b f ≠ [] ∧ ¬MEM f ps3.b.gone’ by fs[] >>
      qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >>
      drule l1_reap_keep >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
      impl_tac >- fs[] >> strip_tac >>
      qexists_tac ‘T’ >> simp[tk_def] >>
      conj_tac
      >- (qpat_x_assum ‘MEM f (MAP SND ps.b.tbl) ∨ _’ strip_assume_tac >> simp[] >>
          qpat_x_assum ‘¬(_ ∧ _)’ mp_tac >> qpat_x_assum ‘MEM f ps.b.closing’ mp_tac >>
          simp[]) >>
      mp_tac (Q.INST [‘w’ |-> ‘w3’, ‘b’ |-> ‘ps3.b’, ‘b'’ |-> ‘b4’] acct_same) >>
      disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >> (* dead *)
  qpat_x_assum ‘ps3f.b.closing = ps3.b.closing’ kall_tac >>
  qpat_x_assum ‘ps3.b.closing = ps3f.b.closing’ kall_tac >>
  qpat_x_assum ‘ps3.b.tbl = ps3f.b.tbl’ kall_tac >>
  ‘outbox_of b2 f = [] ∧ (MEM f b2.gone ⇔ MEM f ps.b.gone) ∧ evs_sent f fevs = []’
    by (drule_all l1_flush_other >> simp[]) >>
  ‘ps3f.b = b2’
    by (qpat_x_assum ‘ps3f.b = ps2.b’ SUBST1_TAC >> qpat_x_assum ‘ps2.b = b2’ ACCEPT_TAC) >>
  ‘¬MEM f (MAP SND ps3f.b.tbl) ∧ ¬MEM f ps3f.b.closing’
    by (qpat_x_assum ‘ps3f.b = b2’ SUBST1_TAC >> qpat_x_assum ‘b2.tbl = _’ SUBST1_TAC >>
        qpat_x_assum ‘b2.closing = _’ SUBST1_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [‘f’, ‘ps3f’, ‘pf_held ps3f’, ‘outbox_of ps.b’, ‘log’] mp_tac
    (Q.GENL [‘f’, ‘ps’, ‘hfs’, ‘ob’, ‘log’] stall_other) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘Abbrev (ps3 = _)’
    (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)] >>
              assume_tac th) >>
  strip_tac >>
  ‘¬MEM f ps3.b.closing’
    by (qpat_x_assum ‘ps3.b.closing = ps.b.closing’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >>
  drule_all l1_reap_other >> strip_tac >>
  ‘¬MEM f b4.closing’
    by (strip_tac >> qpat_x_assum ‘∀g. MEM g b4.closing ⇒ _’ drule >>
        qpat_x_assum ‘¬MEM f ps.b.closing’ mp_tac >> simp[]) >>
  qexists_tac ‘F’ >> simp[] >>
  ASM_REWRITE_TAC [APPEND_NIL]
QED

(* One round, followed from an fd L1 holds or has pre-accepted at its start *)
Theorem round_tk:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ winv w ∧ EVERY small_send evs ∧ out_rel cm w ps s ∧
  (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq) ∧ l0_chan_of w f = SOME c ⇒
  MEM f (MAP FST cm) ∧
  ∃rs hevs s1 hs1.
    hacts lfd (s, hs_of ps) acts = SOME (rs, hevs, (s1, hs1)) ∧
    ∃live. tk live w' ps' f c (csent w c ++ evs_sent f evs) (EL (cl cm f) s1.clients).outgoing
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule_all held_acct >> strip_tac >> simp[] >>
  ‘c' = c’ by gvs[acct_def] >> gvs[] >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[pround_def, AllCaseEqs()] >>
  strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  rename1 ‘pacts _ _ _ = SOME (rs1, aevs, (w1, ps1))’ >>
  drule_all pacts_hacts >> strip_tac >> gvs[] >>
  ‘tk T w ps f c (csent w c) (EL (cl cm f) s.clients).outgoing’ by simp[tk_def] >>
  ‘EVERY small_send aevs ∧ EVERY small_send tevs’ by fs[] >>
  ‘¬T ⇒ ¬MEM f ps.acq’ by simp[] >>
  drule_all pacts_tk >> strip_tac >>
  ‘qfresh w’ by fs[out_rel_def] >>
  drule_all pacts_winv >> strip_tac >>
  drule_all pacts_qfresh >> strip_tac >>
  drule_all tail_tk >> strip_tac >>
  qexists_tac ‘live''’ >> fs[]
QED

Theorem prounds_SUC_step:
  prounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ∧
  prounds lfd pol ifds m ws0 (SUC n) = SOME (h', ws', evs', logs') ⇒
  ∃snap log revs.
    pround lfd pol (ifds h) ws (new_actions (log_of m) h) = SOME (snap, ws', log, revs) ∧
    evs' = evs ++ revs
Proof
  rw[] >> qpat_x_assum ‘prounds _ _ _ _ _ (SUC _) = _’ mp_tac >>
  simp[Once prounds_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

(* MAIN (step 2, the raw trace round by round): an fd L1 holds or has
   pre-accepted at the start of round n, with channel c, is either still
   live after the round (tk T: held or pre-accepted, same channel, whose
   sent is the start's plus what round n's sys_send events took on f, and
   with its account), or was closed in the round (tk F: the start's sent
   plus what the round took on f is a prefix of what the server wrote to
   its client, cl (pcm n) f, in psk) *)
Theorem l1pf_round_sent_upto:
  winv w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ N ⇒ SND (pcm lfd pol ifds m w0 n') + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs h' ws' evs' logs'.
    SUC n ≤ N ∧
    prounds lfd pol ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ∧
    prounds lfd pol ifds m (w0, pinit) (SUC n) = SOME (h', ws', evs', logs') ∧
    EVERY small_send evs' ∧
    (MEM f (MAP SND (SND ws).b.tbl) ∨ MEM f (SND ws).b.closing ∨ MEM f (SND ws).acq) ∧
    l0_chan_of (FST ws) f = SOME c ⇒
    ∃live. tk live (FST ws') (SND ws') f c
             (csent (FST ws) c ++ evs_sent f (DROP (LENGTH evs) evs'))
             (EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
                 (FST (hst lfd ifds m (psk lfd pol ifds m w0) (SUC n))).clients).outgoing
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[winv_def] >>
  drule_all prounds_SUC_step >> strip_tac >>
  qpat_x_assum ‘evs' = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘EVERY _ (_ ++ _)’ (strip_assume_tac o REWRITE_RULE [EVERY_APPEND]) >>
  REWRITE_TAC [DROP_LENGTH_APPEND] >>
  ‘n ≤ N’ by simp[] >>
  mp_tac (Q.INST [‘N’ |-> ‘N’] l1pf_refines_hl_out_upto) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  mp_tac (Q.INST [‘N’ |-> ‘N’] l1pf_refines_hl_upto) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  PairCases_on ‘ws’ >> PairCases_on ‘ws'’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [FST, SND]) >> REWRITE_TAC [FST, SND] >>
  Cases_on ‘hst lfd ifds m (psk lfd pol ifds m w0) n’ >> rename1 ‘_ = (s, hs)’ >> gvs[] >>
  ‘hacts_of lfd ifds m (psk lfd pol ifds m w0) n =
   new_actions (log_of m) (hhist lfd ifds m (psk lfd pol ifds m w0) n)’
    by simp[hacts_of_def] >>
  Q.SUBGOAL_THEN ‘MEM f (MAP SND ws1.b.tbl) ∨ MEM f ws1.b.closing ∨ MEM f ws1.acq’
    ASSUME_TAC >> TRY (fs[] >> NO_TAC) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ assume_tac >>
  drule round_tk >>
  disch_then (qspecl_then [‘s’, ‘f’, ‘FST (pcm lfd pol ifds m w0 n)’, ‘c’] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  ‘hacts_tot lfd (hst lfd ifds m (psk lfd pol ifds m w0) n)
     (hacts_of lfd ifds m (psk lfd pol ifds m w0) n) = (rs, hevs, (s1, hs1))’
    by fs[hacts_tot_def] >>
  drule hround_step >> strip_tac >> simp[] >>
  ‘cl (FST (pcm lfd pol ifds m w0 n)) f < LENGTH s1.clients’
    by (drule hacts_world >> strip_tac >>
        qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> simp[pv_rel_def] >> strip_tac >>
        drule cl_mem >> gvs[EVERY_MEM]) >>
  ‘∀hf. (EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
           (SND (hpoll lfd hs1 hf s1)).clients).outgoing =
        (EL (cl (FST (pcm lfd pol ifds m w0 n)) f) s1.clients).outgoing’
    by (gen_tac >> qspecl_then [‘s1’, ‘lfd’, ‘hs1’, ‘hf’] mp_tac
          (Q.GENL [‘s’, ‘lfd’, ‘hs’, ‘hfds’] cext_hpoll) >>
        simp[cext_def]) >>
  simp[] >> qexists_tac ‘live’ >> simp[]
QED
