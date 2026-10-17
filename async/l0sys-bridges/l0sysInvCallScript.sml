(*
  The per-process invariant pinv (l0sysInv) after each L0 call, as l0sys
  makes it (a blocking poll is answered as a non-blocking one): the event
  the call records is IO_event (ExtCall nm) conf (ZIP (bytes, out)).
*)
Theory l0sysInvCall
Ancestors
  Marshalling honestL0 honestL0World honestL0Rely honestL0WorldProps l0sys l0sysEpisodes
  l0sysEpisodesEcho l0sysInv
Libs
  preamble

(* The counts send and recv report fit in the result's 8-byte field
   (pending: design/45 §9, the rely or a B2 hypothesis) *)
Definition small_ch_def:
  small_ch (ch : lchoices) ⇔
    (∀j h b n. ch.takes j h b n < 256 ** 8) ∧ (∀j h a. ch.short j h a < 256 ** 8)
End

(*---------------------------------------------------------------------------*)
(* Events *)

Theorem ev_quiet:
  nm ≠ «sys_connect» ∧ nm ≠ «sys_accept» ∧ nm ≠ «sys_listen» ∧ nm ≠ «sys_send» ∧
  nm ≠ «sys_recv» ⇒
  ev_new (IO_event (ExtCall nm) conf bl) = NONE ∧
  ev_listen (IO_event (ExtCall nm) conf bl) = NONE ∧
  ev_sent (IO_event (ExtCall nm) conf bl) = NONE ∧
  ev_recvd (IO_event (ExtCall nm) conf bl) = NONE
Proof
  simp[ev_new_def, ev_listen_def, ev_sent_def, ev_recvd_def]
QED

(* An event whose sends and recvs carry no bytes changes no projection *)
Theorem pinv_noop_empty:
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧
  (∀f bs. ev_sent ev = SOME (f, bs) ⇒ bs = []) ∧
  (∀f bs. ev_recvd ev = SOME (f, bs) ⇒ bs = []) ⇒
  (pinv (evs ++ [ev]) w cs ⇔ pinv evs w cs)
Proof
  rw[pinv_def, ep_fds_SNOC, ep_io_SNOC, FOLDL_APPEND, m_step_none, lsn_step_def] >>
  ‘∀j. (case ev_sent ev of NONE => [] | SOME (f, bs) =>
          if ALOOKUP (FST (m_of evs)) f = SOME j then bs else []) = [] ∧
       (case ev_recvd ev of NONE => [] | SOME (f, bs) =>
          if ALOOKUP (FST (m_of evs)) f = SOME j then bs else []) = []’
    by (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[]) >>
  simp[]
QED

Theorem pinv_noop_empty_imp:
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧
  (∀f bs. ev_sent ev = SOME (f, bs) ⇒ bs = []) ∧
  (∀f bs. ev_recvd ev = SOME (f, bs) ⇒ bs = []) ∧ pinv evs w cs ⇒
  pinv (evs ++ [ev]) w cs
Proof
  metis_tac[pinv_noop_empty]
QED

Theorem dec_res_err:
  dec_res (n2w (err_code e) :: rest) ≠ SOME (Ok v)
Proof
  ‘n2w (err_code e) ≠ (0w : word8)’
    by (assume_tac err_code_range >> simp[]) >>
  rw[dec_res_def]
QED

Theorem dec_res_fail:
  l0_rely w ⇒ dec_res (enc_res (fail w e) ++ rest) ≠ SOME (Ok v)
Proof
  rw[fail_def, enc_res_def] >> simp[dec_res_err]
QED

Theorem dec_res_listen_fail:
  dec_res (enc_listen_fail w ke) ≠ SOME (Ok v)
Proof
  Cases_on ‘ke’ >> simp[enc_listen_fail_def, dec_res_err]
QED

(* A result that is no success records no listener, send or recv *)
Theorem ev_not_ok:
  (∀v. dec_res (MAP SND bl) ≠ SOME (Ok v)) ⇒
  ev_listen (IO_event (ExtCall n) conf bl) = NONE ∧
  ev_sent (IO_event (ExtCall n) conf bl) = NONE ∧
  ev_recvd (IO_event (ExtCall n) conf bl) = NONE
Proof
  rw[ev_listen_def, ev_sent_def, ev_recvd_def] >> every_case_tac >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* Calls that start nothing *)

Theorem pinv_call_shutdown:
  pinv evs w cs ∧ l0_call «sys_shutdown» conf bytes w = SOME (FFIreturn out w1) ⇒
  pinv (evs ++ [IO_event (ExtCall «sys_shutdown») conf bl]) w1 cs
Proof
  strip_tac >> simp[pinv_noop, ev_quiet] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >>
  gvs[l0_shutdown_def, AllCaseEqs()] >>
  irule pinv_upd >> gvs[l0_chan_of_def, AllCaseEqs(), in_ok_def]
QED

Theorem pinv_call_connerr:
  pinv evs w cs ∧ l0_call «sys_connerr» conf bytes w = SOME (FFIreturn out w1) ⇒
  pinv (evs ++ [IO_event (ExtCall «sys_connerr») conf bl]) w1 cs
Proof
  strip_tac >> simp[pinv_noop, ev_quiet] >>
  gvs[l0_call_def, AllCaseEqs(), l0_connerr_def] >>
  irule pinv_upd >> gvs[l0_chan_of_def, AllCaseEqs(), in_ok_def]
QED

Theorem pinv_call_close:
  pinv evs w cs ∧ l0_call «sys_close» conf bytes w = SOME (FFIreturn out w1) ⇒
  pinv (evs ++ [IO_event (ExtCall «sys_close») conf bl]) w1 cs
Proof
  strip_tac >> simp[pinv_noop, ev_quiet] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >>
  gvs[l0_close_def, AllCaseEqs()] >> rw[pinv_close_fd]
QED

(* l0sys answers a blocking poll as a non-blocking one: nothing changes *)
Theorem l0_call_poll_unblock:
  l0_call «sys_poll» (unblock «sys_poll» conf) bytes w = SOME (FFIreturn out w1) ⇒ w1 = w
Proof
  rw[l0_call_def, unblock_def] >> gvs[AllCaseEqs()]
QED

Theorem pinv_call_poll:
  pinv evs w cs ⇒ pinv (evs ++ [IO_event (ExtCall «sys_poll») conf bl]) w cs
Proof
  simp[pinv_noop, ev_quiet]
QED

(*---------------------------------------------------------------------------*)
(* listen *)

Theorem pinv_call_listen:
  l0_rely w ∧ pinv evs w cs ∧ l0_call «sys_listen» conf bytes w = SOME (FFIreturn out w1) ∧
  LENGTH out = LENGTH bytes ⇒
  pinv (evs ++ [IO_event (ExtCall «sys_listen») conf (ZIP (bytes, out))]) w1 cs
Proof
  strip_tac >> ‘MAP SND (ZIP (bytes, out)) = out’ by metis_tac[MAP_ZIP] >>
  gvs[l0_call_def, AllCaseEqs()] >>
  gvs[l0_listen_def, AllCaseEqs()] >>
  TRY (qmatch_goalsub_abbrev_tac ‘IO_event _ _ bl’ >>
       ‘∀v. dec_res (MAP SND bl) ≠ SOME (Ok v)’
         by (unabbrev_all_tac >> gvs[dec_res_listen_fail]) >>
       drule ev_not_ok >> strip_tac >>
       simp[pinv_noop, ev_new_def, Abbr ‘bl’] >> NO_TAC) >>
  rename1 ‘l0_alloc w = SOME f’ >>
  ‘¬MEM f (l0_used w) ∧ w2n f < w.fd_limit’
    by (irule l0_alloc_fresh >> gvs[pinv_def, l0_rely_def]) >>
  irule pinv_listen >>
  ‘dec_res (enc_res (Ok (w2n f))) = SOME (Ok (w2n f))’
    by (‘enc_res (Ok (w2n f)) = enc_res (Ok (w2n f)) ++ []’ by simp[] >>
        pop_assum SUBST1_TAC >> irule dec_enc_res >> simp[l0_res_ok_def] >>
        assume_tac (w2n_lt |> INST_TYPE [alpha |-> “:64”]) >> gvs[]) >>
  gvs[ev_new_def, ev_listen_def, ev_sent_def, ev_recvd_def]
QED

(*---------------------------------------------------------------------------*)
(* send *)

Theorem not_chan_fail:
  ∃e. not_chan w f = fail w e
Proof
  rw[not_chan_def] >> metis_tac[]
QED

Theorem l0_send_cases:
  l0_send f bs w = (r, w') ⇒
  (∃e. r = fail w e) ∧
  (w' = w ∨ ∃j. l0_chan_of w f = SOME j ∧ w' = upd_lchan j (λc. c with err := NONE) w) ∨
  ∃j k. l0_chan_of w f = SOME j ∧ r = Ok k ∧ k ≤ w.ch.takes j w.hist (EL j w.chans).inflight (LENGTH bs) ∧
        w' = upd_lchan j (λc. c with <| sent := c.sent ++ TAKE k bs;
                                        inflight := c.inflight + k |>) w
Proof
  rw[l0_send_def, AllCaseEqs()] >> gvs[not_chan_fail] >> metis_tac[]
QED

Theorem dec_res_ok:
  k < 256 ** 8 ⇒ dec_res (enc_res (Ok k) ++ rest) = SOME (Ok k)
Proof
  strip_tac >> irule dec_enc_res >> simp[l0_res_ok_def]
QED

Theorem pinv_call_send:
  l0_rely w ∧ small_ch w.ch ∧ pinv evs w cs ∧
  l0_call «sys_send» conf bytes w = SOME (FFIreturn out w1) ∧ LENGTH out = LENGTH bytes ⇒
  pinv (evs ++ [IO_event (ExtCall «sys_send») conf (ZIP (bytes, out))]) w1 cs
Proof
  strip_tac >> ‘MAP SND (ZIP (bytes, out)) = out’ by metis_tac[MAP_ZIP] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  drule l0_send_cases >> strip_tac >> gvs[]
  >- (‘∀v. dec_res (MAP SND (ZIP (bytes, enc_res (fail w e)))) ≠ SOME (Ok v)’
        by (gvs[] >> ‘enc_res (fail w e) = enc_res (fail w e) ++ []’ by simp[] >>
            pop_assum SUBST1_TAC >> simp[dec_res_fail]) >>
      drule ev_not_ok >> strip_tac >> simp[pinv_noop, ev_new_def])
  >- (‘∀v. dec_res (MAP SND (ZIP (bytes, enc_res (fail w e)))) ≠ SOME (Ok v)’
        by (gvs[] >> ‘enc_res (fail w e) = enc_res (fail w e) ++ []’ by simp[] >>
            pop_assum SUBST1_TAC >> simp[dec_res_fail]) >>
      drule ev_not_ok >> strip_tac >> simp[pinv_noop, ev_new_def] >>
      irule pinv_upd >> gvs[l0_chan_of_def, AllCaseEqs(), in_ok_def]) >>
  ‘k < 256 ** 8’ by (gvs[small_ch_def] >> irule LESS_EQ_LESS_TRANS >> metis_tac[]) >>
  irule (SIMP_RULE std_ss [] (Q.INST [‘x’ |-> ‘λch:lchan. k + ch.inflight’] pinv_sent)) >>
  simp[ev_new_def, ev_listen_def, ev_recvd_def, ev_sent_def] >>
  ‘enc_res (Ok k) = enc_res (Ok k) ++ []’ by simp[] >>
  pop_assum SUBST1_TAC >> simp[dec_res_ok]
QED

(*---------------------------------------------------------------------------*)
(* recv *)

Theorem l0_recv_cases:
  l0_recv f n w = (r, d, w') ⇒
  (∃e. r = fail w e) ∧ d = [] ∧
  (w' = w ∨ ∃j. l0_chan_of w f = SOME j ∧ w' = upd_lchan j (λc. c with err := NONE) w) ∨
  r = Ok 0 ∧ d = [] ∧ w' = w ∨
  ∃j k. l0_chan_of w f = SOME j ∧ r = Ok k ∧ (EL j w.chans).inbox ≠ [] ∧
        k ≤ w.ch.short j w.hist (LENGTH (EL j w.chans).inbox) ∧
        d = TAKE k (EL j w.chans).inbox ∧
        w' = upd_lchan j (λc. c with inbox := DROP k c.inbox) w
Proof
  rw[l0_recv_def, AllCaseEqs()] >> gvs[not_chan_fail] >> metis_tac[]
QED

Theorem pinv_call_recv:
  l0_rely w ∧ small_ch w.ch ∧ pinv evs w cs ∧
  l0_call «sys_recv» conf bytes w = SOME (FFIreturn out w1) ∧ LENGTH out = LENGTH bytes ⇒
  pinv (evs ++ [IO_event (ExtCall «sys_recv») conf (ZIP (bytes, out))]) w1 cs
Proof
  strip_tac >> ‘MAP SND (ZIP (bytes, out)) = out’ by metis_tac[MAP_ZIP] >>
  gvs[l0_call_def, AllCaseEqs()] >>
  Cases_on ‘l0_recv (bytes_fd conf) (LENGTH bytes − l0_hdr) w’ >>
  PairCases_on ‘r’ >> gvs[] >>
  drule l0_recv_cases >> strip_tac >> gvs[]
  >- (qmatch_goalsub_abbrev_tac ‘IO_event _ _ bl’ >>
      ‘∀v. dec_res (MAP SND bl) ≠ SOME (Ok v)’
        by (unabbrev_all_tac >> gvs[dec_res_fail]) >>
      drule ev_not_ok >> strip_tac >> simp[pinv_noop, ev_new_def, Abbr ‘bl’])
  >- (qmatch_goalsub_abbrev_tac ‘IO_event _ _ bl’ >>
      ‘∀v. dec_res (MAP SND bl) ≠ SOME (Ok v)’
        by (unabbrev_all_tac >> gvs[dec_res_fail]) >>
      drule ev_not_ok >> strip_tac >> simp[pinv_noop, ev_new_def, Abbr ‘bl’] >>
      irule pinv_upd >> gvs[l0_chan_of_def, AllCaseEqs(), in_ok_def])
  >- (irule pinv_noop_empty_imp >>
      gvs[ev_new_def, ev_listen_def, ev_sent_def, ev_recvd_def, dec_res_ok]) >>
  ‘k < 256 ** 8’ by (gvs[small_ch_def] >> irule LESS_EQ_LESS_TRANS >> metis_tac[]) >>
  ‘0 < LENGTH (EL j w.chans).inbox’ by (Cases_on ‘(EL j w.chans).inbox’ >> gvs[]) >>
  ‘w.ch.short j w.hist (LENGTH (EL j w.chans).inbox) ≤ LENGTH (EL j w.chans).inbox’
    by (qpat_x_assum ‘l0_rely w’ mp_tac >> rw[l0_rely_def] >>
        qpat_x_assum ‘∀j h a. 0 < a ⇒ _’
          (qspecl_then [‘j’, ‘w.hist’, ‘LENGTH (EL j w.chans).inbox’] mp_tac) >> simp[]) >>
  ‘k ≤ LENGTH (EL j w.chans).inbox’ by simp[] >>
  ‘LENGTH (enc_res (Ok k)) = 13’ by simp[LENGTH_enc_res, l0_res_ok_def] >>
  ‘LENGTH (TAKE k (EL j w.chans).inbox) = k’ by simp[LENGTH_TAKE] >>
  irule pinv_recvd >> gvs[] >> rpt conj_tac
  >- (qexists_tac ‘bytes_fd conf’ >> gvs[ev_recvd_def, l0_hdr_def] >>
      ‘dec_res (enc_res (Ok k) ++ TAKE k (EL j w.chans).inbox ++ DROP (k + 13) bytes) =
       SOME (Ok k)’ by (REWRITE_TAC[GSYM APPEND_ASSOC] >> irule dec_res_ok >> simp[]) >>
      gvs[DROP_APPEND, DROP_LENGTH_TOO_LONG, TAKE_APPEND1]) >>
  gvs[ev_new_def, ev_listen_def, ev_sent_def]
QED

(*---------------------------------------------------------------------------*)
(* accept *)

Theorem l0_accept_cases:
  l0_accept l w = (r, w') ⇒
  (∃e. r = fail w e) ∧
  (w' = w ∨
   ∃l1 p j q' t. FILTER (λ(l', p, q). l' = l) w.listeners = (l1, p, j :: q') :: t ∧
     (w' = w with listeners := AFUPDKEY l (K (p, q')) w.listeners ∨
      w' = upd_lchan j (break_lchan E_CONNRESET F)
             (w with listeners := AFUPDKEY l (K (p, q')) w.listeners))) ∨
  ∃l1 p j q' t f.
    FILTER (λ(l', p, q). l' = l) w.listeners = (l1, p, j :: q') :: t ∧
    l0_alloc w = SOME f ∧ r = Ok (w2n f) ∧
    w' = w with <| listeners := AFUPDKEY l (K (p, q')) w.listeners;
                   open_fds := (f, j) :: w.open_fds |>
Proof
  rw[l0_accept_def, AllCaseEqs()] >> gvs[] >> metis_tac[]
QED

Theorem pinv_call_accept:
  l0_rely w ∧ pinv evs w cs ∧
  l0_call «sys_accept» conf bytes w = SOME (FFIreturn out w1) ∧ LENGTH out = LENGTH bytes ⇒
  ∃cs'. cs ≼ cs' ∧
        pinv (evs ++ [IO_event (ExtCall «sys_accept») conf (ZIP (bytes, out))]) w1 cs'
Proof
  strip_tac >> ‘MAP SND (ZIP (bytes, out)) = out’ by metis_tac[MAP_ZIP] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  drule l0_accept_cases >> strip_tac >> gvs[] >>
  TRY (qexists_tac ‘cs’ >> simp[] >>
       qmatch_goalsub_abbrev_tac ‘IO_event _ _ bl’ >>
       ‘∀v. dec_res (MAP SND bl) ≠ SOME (Ok v)’
         by (unabbrev_all_tac >> gvs[] >>
             ‘enc_res (fail w e) = enc_res (fail w e) ++ []’ by simp[] >>
             pop_assum SUBST1_TAC >> simp[dec_res_fail]) >>
       ‘ev_new (IO_event (ExtCall «sys_accept») conf bl) = NONE’
         by (simp[ev_new_def] >> every_case_tac >> gvs[]) >>
       drule ev_not_ok >> strip_tac >> simp[pinv_noop] >>
       TRY (drule_all pinv_pop >> simp[] >> NO_TAC) >>
       TRY (irule pinv_break >> drule_all pinv_pop >> simp[] >> NO_TAC) >> NO_TAC) >>
  (* the accepted connection: a new episode *)
  qexists_tac ‘cs ++ [j]’ >> simp[] >>
  qabbrev_tac ‘pop = w with listeners := AFUPDKEY (bytes_fd conf) (K (p, q')) w.listeners’ >>
  ‘pinv evs pop cs ∧ ∀l' p' q''. MEM (l', p', q'') pop.listeners ⇒ ¬MEM j q''’
    by (simp[Abbr ‘pop’] >> irule pinv_pop >> metis_tac[]) >>
  ‘MEM (l1, p, j :: q') (FILTER (λ(l', p, q). l' = bytes_fd conf) w.listeners)’ by simp[] >>
  ‘MEM (bytes_fd conf, p, j :: q') w.listeners’ by gvs[MEM_FILTER] >>
  ‘j < LENGTH w.chans ∧ ¬MEM j cs ∧ (∀g. l0_chan_of w g ≠ SOME j) ∧
   (EL j w.chans).sent = [] ∧ in_ok [] (EL j w.chans)’
    by (gvs[pinv_def] >> res_tac >> gvs[]) >>
  ‘¬MEM f (l0_used w) ∧ w2n f < w.fd_limit’
    by (irule l0_alloc_fresh >> gvs[pinv_def, l0_rely_def]) >>
  ‘l0_used pop = l0_used w ∧ pop.chans = w.chans ∧ pop.fd_limit = w.fd_limit ∧
   (∀g. l0_chan_of pop g = l0_chan_of w g)’
    by simp[Abbr ‘pop’, l0_used_def, l0_chan_of_def] >>
  ‘w with <| listeners := pop.listeners; open_fds := (f, j) :: w.open_fds |> =
   pop with open_fds := (f, j) :: pop.open_fds’ by simp[Abbr ‘pop’] >>
  ‘dec_res (enc_res (Ok (w2n f))) = SOME (Ok (w2n f))’
    by (‘enc_res (Ok (w2n f)) = enc_res (Ok (w2n f)) ++ []’ by simp[] >>
        pop_assum SUBST1_TAC >> irule dec_res_ok >>
        assume_tac (w2n_lt |> INST_TYPE [alpha |-> “:64”]) >> gvs[]) >>
  gvs[Abbr ‘pop’] >>
  irule (pinv_open
         |> Q.INST [‘w’ |-> ‘w with listeners := AFUPDKEY (bytes_fd conf) (K (p, q')) w.listeners’]
         |> SIMP_RULE (srw_ss()) []) >>
  gvs[ev_new_def, ev_listen_def, ev_sent_def, ev_recvd_def] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* connect *)

(* The facts about the channel a connect appends *)
Theorem pinv_new_chan_facts:
  pinv evs w cs ⇒
  pinv evs (w with chans := w.chans ++ [c0]) cs ∧ ¬MEM (LENGTH w.chans) cs ∧
  (∀g. l0_chan_of (w with chans := w.chans ++ [c0]) g ≠ SOME (LENGTH w.chans)) ∧
  (∀l p q. MEM (l, p, q) w.listeners ⇒ ¬MEM (LENGTH w.chans) q)
Proof
  strip_tac >> simp[pinv_new_chan] >>
  ‘∀g. l0_chan_of (w with chans := w.chans ++ [c0]) g = l0_chan_of w g’
    by (fs[pinv_def] >> rw[l0_chan_of_def] >> every_case_tac >>
        gvs[EVERY_MEM, FORALL_PROD] >> imp_res_tac ALOOKUP_MEM >> res_tac >> gvs[]) >>
  fs[pinv_def] >> rw[]
  >- (strip_tac >> gvs[EVERY_MEM] >> res_tac >> gvs[])
  >- (strip_tac >> gvs[l0_chan_of_def, AllCaseEqs()])
  >> strip_tac >> res_tac >> gvs[]
QED

Theorem pinv_connect_episode:
  pinv evs w cs ∧ ¬MEM f (l0_used w) ∧ w2n f < w.fd_limit ∧
  ev_new ev = SOME (f, h) ∧ ev_listen ev = NONE ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE ⇒
  pinv (evs ++ [ev])
       (w with <| chans := w.chans ++ [fresh_lchan with connecting := T];
                  open_fds := (f, LENGTH w.chans) :: w.open_fds |>)
       (cs ++ [LENGTH w.chans])
Proof
  strip_tac >>
  drule (Q.INST [‘c0’ |-> ‘fresh_lchan with connecting := T’] pinv_new_chan_facts) >>
  strip_tac >>
  irule (pinv_open
         |> Q.INST [‘w’ |-> ‘w with chans := w.chans ++ [fresh_lchan with connecting := T]’,
                    ‘j’ |-> ‘LENGTH (w.chans : lchan list)’]
         |> SIMP_RULE (srw_ss()) []) >>
  gvs[l0_used_def, EL_APPEND2, fresh_lchan_def, in_ok_def] >> metis_tac[]
QED

Theorem pinv_connect_hidden:
  pinv evs w cs ∧ ¬MEM 0w (l0_used w) ∧ 0 < w.fd_limit ∧
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE ⇒
  pinv (evs ++ [ev])
       (w with <| chans := w.chans ++ [fresh_lchan with connecting := T];
                  open_fds := (0w, LENGTH w.chans) :: w.open_fds |>) cs
Proof
  strip_tac >>
  drule (Q.INST [‘c0’ |-> ‘fresh_lchan with connecting := T’] pinv_new_chan_facts) >>
  strip_tac >>
  irule (pinv_hidden
         |> Q.INST [‘w’ |-> ‘w with chans := w.chans ++ [fresh_lchan with connecting := T]’,
                    ‘j’ |-> ‘LENGTH (w.chans : lchan list)’]
         |> SIMP_RULE (srw_ss()) []) >>
  gvs[l0_used_def] >> metis_tac[]
QED

Theorem l0_connect_cases:
  l0_connect p w = (r, v, w') ⇒
  (∃e. r = fail w e) ∧ v = 0 ∧ w' = w ∨
  ∃f. l0_alloc w = SOME f ∧ v = w2n f ∧
      let W1 = w with <| chans := w.chans ++ [fresh_lchan with connecting := T];
                         open_fds := (f, LENGTH w.chans) :: w.open_fds |> in
        ((∃e. r = fail w e) ∧
         (w' = W1 ∨
          w' = upd_lchan (LENGTH w.chans) (λc. c with <| connecting := F; broken := T |>) W1) ∨
         r = Ok (w2n f) ∧ w' = upd_lchan (LENGTH w.chans) (λc. c with connecting := F) W1)
Proof
  rw[l0_connect_def, AllCaseEqs()] >> metis_tac[]
QED

(* A failed connect's result: the error, and the value field *)
Theorem enc_err_val_dec:
  l0_rely w ∧ v < 256 ** 8 ⇒
  (∀k. dec_res (enc_err_val w e v) ≠ SOME (Ok k)) ∧
  (∃raw. dec_res (enc_err_val w e v) = SOME (Fail e raw)) ∧
  res_val (enc_err_val w e v) = v
Proof
  strip_tac >> ‘LENGTH (w.ch.errno_of w.hist) = 4’ by gvs[l0_rely_def] >>
  ‘n2w (err_code e) ≠ (0w : word8) ∧ w2n (n2w (err_code e) : word8) = err_code e’
    by (assume_tac err_code_range >> simp[]) >>
  simp[enc_err_val_def, dec_res_def, res_val_def, LENGTH_n2w8, TAKE_APPEND1] >>
  simp[TAKE_LENGTH_ID_rwt, LENGTH_n2w8] >> irule w82n_n2w8 >> gvs[]
QED

(* A failed connect's event: an episode iff the value field is a socket *)
Theorem ev_new_connect_fail:
  l0_rely w ∧ v < 256 ** 8 ∧ LENGTH conf = 2 ∧ LENGTH bytes = 13 ⇒
  ev_new (IO_event (ExtCall «sys_connect») conf (ZIP (bytes, enc_err_val w e v))) =
  if v = 0 then NONE else SOME (n2w v, INL (w22n conf))
Proof
  strip_tac >> drule_all enc_err_val_dec >> strip_tac >>
  ‘LENGTH (enc_err_val w e v) = 13’
    by gvs[enc_err_val_def, LENGTH_n2w8, l0_rely_def] >>
  ‘MAP SND (ZIP (bytes, enc_err_val w e v)) = enc_err_val w e v’ by simp[MAP_ZIP] >>
  simp[ev_new_def] >> first_x_assum (qspec_then ‘e’ strip_assume_tac) >> gvs[] >> rw[]
QED

Theorem pinv_call_connect:
  l0_rely w ∧ pinv evs w cs ∧
  l0_call «sys_connect» conf bytes w = SOME (FFIreturn out w1) ∧ LENGTH out = LENGTH bytes ⇒
  ∃cs'. cs ≼ cs' ∧
        pinv (evs ++ [IO_event (ExtCall «sys_connect») conf (ZIP (bytes, out))]) w1 cs'
Proof
  strip_tac >> ‘MAP SND (ZIP (bytes, out)) = out’ by metis_tac[MAP_ZIP] >>
  qabbrev_tac ‘ev = IO_event (ExtCall «sys_connect») conf (ZIP (bytes, out))’ >>
  ‘ev_listen ev = NONE ∧ ev_sent ev = NONE ∧ ev_recvd ev = NONE’
    by simp[Abbr ‘ev’, ev_listen_def, ev_sent_def, ev_recvd_def] >>
  gvs[l0_call_def, AllCaseEqs()] >> drule l0_connect_cases >> strip_tac >>
  gvs[fail_def]
  >~ [‘l0_connect _ _ = (Ok _, _, _)’]
  >- (‘¬MEM f (l0_used w) ∧ w2n f < w.fd_limit’
        by (irule l0_alloc_fresh >> gvs[pinv_def, l0_rely_def]) >>
      ‘dec_res (enc_res (Ok (w2n f))) = SOME (Ok (w2n f))’
        by (‘enc_res (Ok (w2n f)) = enc_res (Ok (w2n f)) ++ []’ by simp[] >>
            pop_assum SUBST1_TAC >> irule dec_res_ok >>
            assume_tac (w2n_lt |> INST_TYPE [alpha |-> “:64”]) >> gvs[]) >>
      ‘ev_new ev = SOME (f, INL (w22n conf))’ by gvs[Abbr ‘ev’, ev_new_def] >>
      qexists_tac ‘cs ++ [LENGTH w.chans]’ >> simp[] >>
      irule pinv_upd >> rpt conj_tac >>
      TRY (irule pinv_connect_episode >> gvs[] >> NO_TAC) >>
      simp[EL_APPEND2, in_ok_def]) >>
  (* a failed connect *)
  ‘LENGTH bytes = 13’ by gvs[l0_hdr_def] >>
  TRY (‘ev_new ev = NONE’ by simp[Abbr ‘ev’, ev_new_connect_fail] >>
       qexists_tac ‘cs’ >> simp[pinv_noop] >> NO_TAC) >>
  ‘¬MEM f (l0_used w) ∧ w2n f < w.fd_limit’
    by (irule l0_alloc_fresh >> gvs[pinv_def, l0_rely_def]) >>
  ‘w2n f < 256 ** 8’ by (assume_tac (w2n_lt |> INST_TYPE [alpha |-> “:64”]) >> gvs[]) >>
  ‘ev_new ev = if w2n f = 0 then NONE else SOME (f, INL (w22n conf))’
    by (simp[Abbr ‘ev’, ev_new_connect_fail] >> rw[]) >>
  Cases_on ‘f = 0w’ >> gvs[] >>
  FIRST [
    qexists_tac ‘cs’ >> simp[] >>
    FIRST [irule pinv_connect_hidden >> gvs[] >> NO_TAC,
           irule pinv_upd >> rpt conj_tac >>
           TRY (irule pinv_connect_hidden >> gvs[] >> NO_TAC) >>
           simp[EL_APPEND2, in_ok_def] >> NO_TAC],
    qexists_tac ‘cs ++ [LENGTH w.chans]’ >> simp[] >>
    FIRST [irule pinv_connect_episode >> gvs[] >> NO_TAC,
           irule pinv_upd >> rpt conj_tac >>
           TRY (irule pinv_connect_episode >> gvs[] >> NO_TAC) >>
           simp[EL_APPEND2, in_ok_def] >> NO_TAC]]
QED

(*---------------------------------------------------------------------------*)
(* Every call *)

Theorem unblock_other:
  nm ≠ «sys_poll» ⇒ unblock nm conf = conf
Proof
  simp[unblock_def]
QED

(* MAIN: a call as l0sys makes it keeps the invariant; the episodes it
   knows only grow *)
Theorem pinv_call:
  l0_rely w ∧ small_ch w.ch ∧ pinv evs w cs ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  ∃cs'. cs ≼ cs' ∧ pinv (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))]) w1 cs'
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’
  >- (gvs[] >> drule l0_call_poll_unblock >> strip_tac >> gvs[] >>
      qexists_tac ‘cs’ >> simp[pinv_call_poll]) >>
  gvs[unblock_other] >>
  ‘LENGTH out = LENGTH bytes’ by metis_tac[l0_call_length] >>
  Cases_on ‘nm = «sys_listen»’
  >- (gvs[] >> qexists_tac ‘cs’ >> simp[] >> irule pinv_call_listen >> metis_tac[]) >>
  Cases_on ‘nm = «sys_accept»’ >- (gvs[] >> irule pinv_call_accept >> metis_tac[]) >>
  Cases_on ‘nm = «sys_connect»’ >- (gvs[] >> irule pinv_call_connect >> metis_tac[]) >>
  qexists_tac ‘cs’ >> simp[] >>
  Cases_on ‘nm = «sys_send»’ >- (gvs[] >> irule pinv_call_send >> metis_tac[]) >>
  Cases_on ‘nm = «sys_recv»’ >- (gvs[] >> irule pinv_call_recv >> metis_tac[]) >>
  Cases_on ‘nm = «sys_shutdown»’ >- (gvs[] >> irule pinv_call_shutdown >> metis_tac[]) >>
  Cases_on ‘nm = «sys_connerr»’ >- (gvs[] >> irule pinv_call_connerr >> metis_tac[]) >>
  Cases_on ‘nm = «sys_close»’ >- (gvs[] >> irule pinv_call_close >> metis_tac[]) >>
  gvs[l0_call_def]
QED
