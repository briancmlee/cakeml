(*
  L-D (m4-server's proxy buffer bound): an fd that L1 has marked gone at
  the end of an E1 run was dropped for a reason visible on the raw trace.
  Each episode of it still open has a hard error (pos_hard_err) or has
  timed out (pos_timed_out pf_sendwait).  The theory is generic over the
  E1 program; proxyGone instantiates it (proxy_gone_excuse).

  The invariant (ginv) holds at every round boundary, on the trace tr so
  far:
   - a gone fd's open episodes are excused (xc);
   - an fd with stall count c > 0 has each open episode end in a span
     with c output polls on it and nothing taken by a send (sc).
  One round: an fd gone or stalled at the round's end opens no episode in
  it (E1's ownership, eround_live).  It is gone or stalled because it
  already was, or because a send or recv on it failed hard, or because
  the write timeout fired (stall count pf_sendwait − 1 plus one more
  stalled round).
*)
Theory ldGone
Ancestors
  llist alist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  honestL1Model honestL1Props honestL1Steps honestL1Inv honestL1PFModel honestL1PFRound
  honestL1PFInv honestL1PFFlush honestL1PFDead honestL1PFOut honestL1PFOutLive honestL1PFRefine
  honestL1EPModel honestL1EPRefine honestL1EPOut
  honestL1PFConn honestL1PFConnRun Marshalling
  honestEchoL0Spec honestL1BStmts proxyL0Stmts
Libs
  preamble

(* ------------------------------------------------------------------------
   Episodes on a trace
   ------------------------------------------------------------------------ *)

Definition opens_def:
  opens f e ⇔ l0_event_opened e = SOME f
End

Theorem LPREFIX_fromList_APPEND:
  LPREFIX (fromList l1) (fromList (l1 ++ l2))
Proof
  simp[LPREFIX_APPEND] >> qexists_tac ‘fromList l2’ >> simp[LAPPEND_fromList]
QED

Theorem pos_fd_APPEND:
  q < LENGTH xs ⇒ pos_fd q (xs ++ ys) = pos_fd q xs
Proof
  simp[pos_fd_def, EL_APPEND1]
QED

Theorem pos_open_APPEND:
  q < LENGTH xs ⇒
  (pos_open q (xs ++ ys) ⇔ pos_open q xs ∧ ∀f. pos_fd q xs = SOME f ⇒ ¬EXISTS (pos_ends f) ys)
Proof
  strip_tac >> ‘DROP (SUC q) (xs ++ ys) = DROP (SUC q) xs ++ ys’ by simp[DROP_APPEND1] >>
  simp[pos_open_def, pos_fd_APPEND, EVERY_APPEND] >> eq_tac >> rw[] >> gvs[]
QED

(* An episode open at the end of tr ++ R, where R opens no episode of its
   fd, was open at the end of tr, and R does not end it *)
Theorem pos_open_noopen:
  pos_open q (tr ++ R) ∧ pos_fd q (tr ++ R) = SOME f ∧ ¬EXISTS (opens f) R ⇒
  q < LENGTH tr ∧ pos_open q tr ∧ pos_fd q tr = SOME f ∧ ¬EXISTS (pos_ends f) R
Proof
  strip_tac >>
  ‘q < LENGTH tr’
    by (CCONTR_TAC >> qpat_x_assum ‘pos_fd _ _ = _’ mp_tac >>
        rewrite_tac[pos_fd_def] >> IF_CASES_TAC >> simp[] >> strip_tac >>
        ‘q − LENGTH tr < LENGTH R’ by fs[] >>
        ‘EL q (tr ++ R) = EL (q − LENGTH tr) R’ by simp[EL_APPEND2] >>
        qpat_x_assum ‘¬EXISTS _ _’ mp_tac >> simp[EXISTS_MEM, opens_def] >>
        qexists_tac ‘EL (q − LENGTH tr) R’ >> gvs[EL_MEM]) >>
  ‘pos_fd q tr = SOME f’ by metis_tac[pos_fd_APPEND] >>
  qpat_x_assum ‘pos_open _ _’ mp_tac >> simp[pos_open_APPEND]
QED

Theorem pos_hard_err_mono:
  pos_hard_err q (fromList tr) ⇒ pos_hard_err q (fromList (tr ++ R))
Proof
  rw[pos_hard_err_def] >> qexistsl [‘evs’, ‘ev’, ‘f’] >> simp[] >>
  metis_tac[LPREFIX_TRANS, LPREFIX_fromList_APPEND]
QED

Theorem pos_timed_out_mono:
  pos_timed_out k q (fromList tr) ⇒ pos_timed_out k q (fromList (tr ++ R))
Proof
  rw[pos_timed_out_def] >> qexistsl [‘evs’, ‘span’, ‘f’] >> simp[] >>
  metis_tac[LPREFIX_TRANS, LPREFIX_fromList_APPEND]
QED

Theorem hard_err_on_opened:
  hard_err_on f ev ⇒ l0_event_opened ev = NONE
Proof
  Cases_on ‘ev’ >> rw[hard_err_on_def] >>
  simp[l0_event_opened_def, l0_event_accepted_def, l0_event_connected_def]
QED

(* ------------------------------------------------------------------------
   The excuses, and the round steps that keep them
   ------------------------------------------------------------------------ *)

(* Every episode of f open at the end of tr is excused *)
Definition xc_def:
  xc f tr ⇔
    ∀q. pos_open q tr ∧ pos_fd q tr = SOME f ⇒
        pos_hard_err q (fromList tr) ∨ pos_timed_out pf_sendwait q (fromList tr)
End

(* Every episode of f open at the end of tr ends in a span with c output
   polls on f and no send that took bytes on f *)
Definition sc_def:
  sc f c tr ⇔
    ∀q. pos_open q tr ∧ pos_fd q tr = SOME f ⇒
        ∃evs span. tr = evs ++ span ∧ q < LENGTH evs ∧ c ≤ n_out_polls f span ∧
                   EVERY (λe. poll_ev e ⇒ out_poll f e) span ∧ ¬EXISTS (send_took f) span
End

(* A stalled round's events: one poll, listing f for output; no send
   after it took bytes on f (nor before it, when full) *)
Definition stalled_def:
  stalled f full R ⇔
    ∃A pev Z. R = A ++ [pev] ++ Z ∧ out_poll f pev ∧
              EVERY (λe. ¬poll_ev e) A ∧ EVERY (λe. ¬poll_ev e) Z ∧
              ¬EXISTS (send_took f) Z ∧ (full ⇒ ¬EXISTS (send_took f) A)
End

Theorem out_poll_poll_ev:
  out_poll f e ⇒ poll_ev e
Proof
  rw[out_poll_def, poll_ev_def] >> metis_tac[]
QED

Theorem out_poll_send_took:
  out_poll f e ⇒ ¬send_took f e
Proof
  rw[out_poll_def] >> simp[send_took_def]
QED

Theorem n_out_polls_APPEND[simp]:
  n_out_polls f (xs ++ ys) = n_out_polls f xs + n_out_polls f ys
Proof
  simp[n_out_polls_def, FILTER_APPEND]
QED

Theorem nopoll_quiet:
  ∀xs. EVERY (λe. ¬poll_ev e) xs ⇒
       n_out_polls f xs = 0 ∧ EVERY (λe. poll_ev e ⇒ out_poll f e) xs
Proof
  Induct >> simp[n_out_polls_def] >> rpt strip_tac >> fs[n_out_polls_def] >>
  metis_tac[out_poll_poll_ev]
QED

Theorem stalled_span:
  stalled f full R ⇒
  ∃A Z. R = A ++ Z ∧ n_out_polls f Z = 1 ∧ EVERY (λe. poll_ev e ⇒ out_poll f e) Z ∧
        ¬EXISTS (send_took f) Z ∧
        (full ⇒ n_out_polls f A = 0 ∧ EVERY (λe. poll_ev e ⇒ out_poll f e) A ∧
                ¬EXISTS (send_took f) A)
Proof
  rw[stalled_def] >> qexistsl [‘A’, ‘[pev] ++ Z’] >>
  imp_res_tac nopoll_quiet >> simp[] >>
  simp[n_out_polls_def, out_poll_send_took]
QED

Theorem xc_ext:
  xc f tr ∧ ¬EXISTS (opens f) R ⇒ xc f (tr ++ R)
Proof
  rewrite_tac[xc_def] >> rpt strip_tac >> drule_all pos_open_noopen >> strip_tac >>
  first_x_assum drule_all >> metis_tac[pos_hard_err_mono, pos_timed_out_mono]
QED

Theorem xc_err_split:
  hard_err_on f ev ∧ ¬EXISTS (opens f) (ev :: Z) ⇒ xc f (P ++ ev :: Z)
Proof
  rw[xc_def] >> disj1_tac >>
  ‘pos_open q (P ++ [ev] ++ Z) ∧ pos_fd q (P ++ [ev] ++ Z) = SOME f’
    by (REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  ‘¬EXISTS (opens f) Z’ by fs[] >>
  drule_all pos_open_noopen >> strip_tac >>
  ‘q ≠ LENGTH P’
    by (strip_tac >> qpat_x_assum ‘pos_fd q (P ++ [ev]) = _’ mp_tac >>
        simp[pos_fd_def, EL_APPEND2] >> drule hard_err_on_opened >> simp[]) >>
  ‘q < LENGTH P’ by fs[] >>
  simp[pos_hard_err_def] >> qexistsl [‘P’, ‘ev’, ‘f’] >>
  ‘pos_fd q P = SOME f’ by metis_tac[pos_fd_APPEND] >>
  qpat_x_assum ‘pos_open q (P ++ [ev])’ mp_tac >> simp[pos_open_APPEND] >> strip_tac >>
  ‘P ++ ev :: Z = (P ++ [ev]) ++ Z’ by simp[] >>
  pop_assum SUBST1_TAC >> simp[LPREFIX_fromList_APPEND]
QED

Theorem xc_err:
  EXISTS (hard_err_on f) R ∧ ¬EXISTS (opens f) R ⇒ xc f (tr ++ R)
Proof
  strip_tac >> qpat_x_assum ‘EXISTS _ R’ (strip_assume_tac o REWRITE_RULE[EXISTS_MEM]) >>
  qpat_x_assum ‘MEM _ R’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
  ‘tr ++ (l1 ++ e :: l2) = (tr ++ l1) ++ e :: l2’ by simp[] >>
  pop_assum SUBST1_TAC >> irule xc_err_split >> fs[]
QED

Theorem sc_xc:
  sc f c tr ∧ pf_sendwait ≤ c ⇒ xc f tr
Proof
  rw[sc_def, xc_def] >> disj2_tac >> first_x_assum drule_all >> strip_tac >>
  gvs[] >>
  ‘pos_fd q evs = SOME f’ by metis_tac[pos_fd_APPEND] >>
  qpat_x_assum ‘pos_open _ _’ mp_tac >> simp[pos_open_APPEND] >> strip_tac >>
  simp[pos_timed_out_def] >> qexistsl [‘evs’, ‘span’, ‘f’] >> simp[LPREFIX_REFL]
QED

(* A first stalled round: count 1 *)
Theorem sc_one:
  stalled f full R ∧ ¬EXISTS (opens f) R ⇒ sc f 1 (tr ++ R)
Proof
  rewrite_tac[sc_def] >> rpt strip_tac >> drule_all pos_open_noopen >> strip_tac >>
  drule stalled_span >> strip_tac >> gvs[] >>
  qexistsl [‘tr ++ A’, ‘Z’] >> simp[]
QED

(* A further stalled round (full: nothing taken before its poll either) *)
Theorem sc_suc:
  sc f c tr ∧ stalled f T R ∧ ¬EXISTS (opens f) R ⇒ sc f (c + 1) (tr ++ R)
Proof
  rewrite_tac[sc_def] >> rpt strip_tac >> drule_all pos_open_noopen >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule stalled_span >> simp[] >> strip_tac >> gvs[] >>
  qexistsl [‘evs’, ‘span ++ A ++ Z’] >> simp[]
QED

(* The run's invariant on the trace so far *)
Definition ginv_def:
  ginv tr (es : l1e) ⇔
    (∀f. MEM f es.p.b.gone ⇒ xc f tr) ∧
    (∀f c. MEM (f, c) es.p.stalls ∧ 0 < c ⇒ sc f c tr)
End

(* What one round gives, as events R from state es to es' *)
Definition gstep_def:
  gstep (es : l1e) (es' : l1e) R ⇔
    (∀f. MEM f es'.p.b.gone ⇒
         ¬EXISTS (opens f) R ∧
         (MEM f es.p.b.gone ∨ EXISTS (hard_err_on f) R ∨
          (∃n. pf_sendwait ≤ n + 1 ∧ MEM (f, n) es.p.stalls) ∧ stalled f T R)) ∧
    (∀f c. MEM (f, c) es'.p.stalls ∧ 0 < c ⇒
           ¬EXISTS (opens f) R ∧
           (c = 1 ∧ stalled f F R ∨ 1 < c ∧ MEM (f, c − 1) es.p.stalls ∧ stalled f T R))
End

Theorem ginv_step:
  ginv tr es ∧ gstep es es' R ⇒ ginv (tr ++ R) es'
Proof
  rewrite_tac[ginv_def, gstep_def] >> rpt strip_tac
  >- (qpat_x_assum ‘∀f. MEM f es'.p.b.gone ⇒ _’ drule >> rpt strip_tac
      >- (irule xc_ext >> conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qpat_x_assum ‘∀f. MEM f es.p.b.gone ⇒ _’ irule >> first_assum ACCEPT_TAC)
      >- (irule xc_err >> conj_tac >> first_assum ACCEPT_TAC) >>
      ‘0 < n’ by (assume_tac pf_sendwait_pos >> decide_tac) >>
      ‘sc f n tr’ by (qpat_x_assum ‘∀f c. MEM (f,c) es.p.stalls ∧ _ ⇒ _’ irule >> simp[]) >>
      ‘sc f (n + 1) (tr ++ R)’ by (irule sc_suc >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      irule sc_xc >> qexists_tac ‘n + 1’ >> simp[]) >>
  qpat_x_assum ‘∀f c. MEM (f,c) es'.p.stalls ∧ _ ⇒ _’ drule_all >> rpt strip_tac
  >- (qpat_x_assum ‘c = 1’ SUBST_ALL_TAC >> irule sc_one >> metis_tac[]) >>
  ‘sc f (c − 1) tr’ by (qpat_x_assum ‘∀f c. MEM (f,c) es.p.stalls ∧ _ ⇒ _’ irule >> simp[]) >>
  ‘sc f (c − 1 + 1) (tr ++ R)’ by (irule sc_suc >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘c − 1 + 1 = c’ by decide_tac >> fs[]
QED

(* ------------------------------------------------------------------------
   Events: what L1's calls put on the trace
   ------------------------------------------------------------------------ *)

Theorem l0_do_ev:
  l0_do n conf alen w = SOME (out, w', ev) ∧ l0_rely w ⇒
  LENGTH out = alen ∧ l0_rely w' ∧
  ev = IO_event (ExtCall n) conf (ZIP (REPLICATE alen 0w, out)) ∧
  MAP SND (ZIP (REPLICATE alen (0w:word8), out)) = out
Proof
  simp[l0_do_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all l0_ffi_fn_length >> simp[MAP_ZIP]
QED

Theorem name_not_took:
  ev_name ev = ExtCall n ∧ n ≠ «sys_send» ⇒ ¬send_took f ev
Proof
  Cases_on ‘ev’ >> simp[ev_name_def, send_took_def] >> rpt strip_tac >> gvs[]
QED

Theorem name_not_poll:
  ev_name ev = ExtCall n ∧ n ≠ «sys_poll» ⇒ ¬poll_ev ev
Proof
  Cases_on ‘ev’ >> simp[ev_name_def, poll_ev_def] >> rpt strip_tac >> gvs[]
QED

Theorem name_not_opens:
  ev_name ev = ExtCall n ∧ n ≠ «sys_accept» ∧ n ≠ «sys_connect» ⇒ ¬opens f ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  simp[ev_name_def, opens_def, l0_event_opened_def, l0_event_accepted_def,
       l0_event_connected_def] >> rpt strip_tac >> gvs[]
QED

Theorem name_not_hard:
  ev_name ev = ExtCall n ∧ n ≠ «sys_send» ∧ n ≠ «sys_recv» ⇒ ¬hard_err_on f ev
Proof
  Cases_on ‘ev’ >> simp[ev_name_def, hard_err_on_def] >> rpt strip_tac >> gvs[]
QED

(* Events of calls that are none of the interesting kinds *)
Definition plain_def:
  plain f ev ⇔ ¬poll_ev ev ∧ ¬opens f ev ∧ ¬send_took f ev
End

Theorem name_plain:
  ev_name ev = ExtCall n ∧ n ≠ «sys_poll» ∧ n ≠ «sys_accept» ∧ n ≠ «sys_connect» ∧
  n ≠ «sys_send» ⇒ plain f ev
Proof
  strip_tac >> simp[plain_def] >>
  metis_tac[name_not_poll, name_not_opens, name_not_took]
QED

(* honestEchoL0Excuse's: every send or recv result decodes *)
Theorem gone_send_res[local]:
  ∀f bs w. ∃e. FST (l0_send f bs w) = fail w e ∨ ∃v. FST (l0_send f bs w) = Ok v
Proof
  rw[l0_send_def, not_chan_def] >> every_case_tac >> simp[] >> metis_tac[]
QED

Theorem gone_recv_res[local]:
  ∀f n w. ∃e. FST (l0_recv f n w) = fail w e ∨ ∃v. FST (l0_recv f n w) = Ok v
Proof
  rw[l0_recv_def, not_chan_def] >> every_case_tac >> simp[] >> metis_tac[]
QED

Theorem gone_sendrecv_dec[local]:
  l0_rely x ∧ l0_ffi_fn n conf b x = SOME (FFIreturn out u) ∧
  (n = «sys_send» ∨ n = «sys_recv») ⇒
  8 ≤ LENGTH conf ∧ ∀e raw. l0_res_of out = Fail e raw ⇒ dec_res out = SOME (Fail e raw)
Proof
  strip_tac >>
  ‘∀nm. l0_rely (l0_tick nm x)’ by (rw[] >> irule l0_rely_ch >> qexists_tac ‘x’ >> simp[]) >>
  qpat_x_assum ‘l0_ffi_fn _ _ _ _ = _’ mp_tac >>
  simp[l0_ffi_fn_def, l0_call_def, AllCaseEqs()] >> rw[] >>
  rpt (pairarg_tac >> gvs[])
  >- (qspecl_then [‘bytes_fd (TAKE 8 conf)’, ‘DROP 8 conf’, ‘l0_tick «sys_send» x’]
        strip_assume_tac gone_send_res >> gvs[] >>
      TRY (gvs[l0_res_of_def, enc_res_def, dec_res_def, LENGTH_n2w8] >> NO_TAC) >>
      ‘l0_res_ok (fail (l0_tick «sys_send» x) e')’ by simp[fail_ok] >>
      drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >>
      qpat_x_assum ‘l0_res_of _ = _’ mp_tac >> rw[] >> gvs[l0_res_of_def]) >>
  qspecl_then [‘bytes_fd conf’, ‘LENGTH b − l0_hdr’, ‘l0_tick «sys_recv» x’]
    strip_assume_tac gone_recv_res >> gvs[] >>
  TRY (gvs[l0_res_of_def, enc_res_def, dec_res_def, LENGTH_n2w8] >> NO_TAC) >>
  ‘l0_res_ok (fail (l0_tick «sys_recv» x) e')’ by simp[fail_ok] >>
  drule dec_enc_res >> disch_then (qspec_then ‘d ++ DROP (l0_hdr + LENGTH d) b’ mp_tac) >>
  qpat_x_assum ‘l0_res_of _ = _’ mp_tac >> rw[] >> gvs[l0_res_of_def]
QED

Theorem TAKE_fd_bytes[local]:
  TAKE 8 (fd_bytes g ++ bs) = fd_bytes g ∧ TAKE 8 (fd_bytes g) = fd_bytes g
Proof
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  simp[TAKE_APPEND1, TAKE_LENGTH_ID_rwt]
QED

Theorem sys_send_hard:
  sys_send g bs w = SOME (out, w', ev) ∧ l0_rely w ∧ l0_res_of out = Fail e x ∧
  ¬l1_transient e ⇒
  hard_err_on g ev
Proof
  rw[sys_send_def] >>
  ‘l0_ffi_fn «sys_send» (fd_bytes g ++ bs) (REPLICATE 13 0w) w = SOME (FFIreturn out w')’
    by gvs[l0_do_def, AllCaseEqs()] >>
  drule_all l0_do_ev >> strip_tac >>
  ‘8 ≤ LENGTH (fd_bytes g ++ bs) ∧ dec_res out = SOME (Fail e x)’
    by metis_tac[gone_sendrecv_dec] >>
  gvs[hard_err_on_def, l0_ev_res_def, TAKE_fd_bytes]
QED

Theorem sys_recv_hard:
  sys_recv g n w = SOME (out, w', ev) ∧ l0_rely w ∧ l0_res_of out = Fail e x ∧
  ¬l1_transient e ⇒
  hard_err_on g ev
Proof
  rw[sys_recv_def] >>
  ‘l0_ffi_fn «sys_recv» (fd_bytes g) (REPLICATE (13 + n) 0w) w = SOME (FFIreturn out w')’
    by gvs[l0_do_def, AllCaseEqs()] >>
  drule_all l0_do_ev >> strip_tac >>
  ‘8 ≤ LENGTH (fd_bytes g) ∧ dec_res out = SOME (Fail e x)’
    by metis_tac[gone_sendrecv_dec] >>
  gvs[hard_err_on_def, l0_ev_res_def, TAKE_fd_bytes]
QED

Theorem sys_send_took:
  sys_send g bs w = SOME (out, w', ev) ∧ l0_rely w ∧ send_took f ev ⇒
  g = f ∧ ∃k. l0_res_of out = Ok k ∧ 0 < k
Proof
  rw[sys_send_def] >> drule_all l0_do_ev >> strip_tac >>
  gvs[send_took_def, l0_ev_res_def, l0_res_of_def, TAKE_fd_bytes]
QED

Theorem sys_send_ev:
  sys_send g bs w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_send»
Proof
  rw[sys_send_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem sys_recv_ev:
  sys_recv g n w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_recv»
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem sys_close_ev:
  sys_close g w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_close»
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem sys_connerr_ev:
  sys_connerr g w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_connerr»
Proof
  rw[sys_connerr_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem sys_accept_opens:
  sys_accept l w = SOME (out, w', ev) ∧ l0_rely w ∧ opens g ev ⇒
  ∃k. l0_res_of out = Ok k ∧ g = n2w k
Proof
  rw[sys_accept_def] >> drule_all l0_do_ev >> strip_tac >>
  gvs[opens_def, l0_event_opened_def, l0_event_accepted_def, l0_event_connected_def,
      l0_ev_res_def, l0_res_of_def, AllCaseEqs()]
QED

Theorem sys_connect_opens:
  sys_connect p w = SOME (out, w', ev) ∧ l0_rely w ∧ opens g ev ⇒
  res_val out ≠ 0 ∧ g = n2w (res_val out)
Proof
  rw[sys_connect_def] >> drule_all l0_do_ev >> strip_tac >>
  Cases_on ‘out’ >> gvs[] >>
  gvs[opens_def, l0_event_opened_def, l0_event_accepted_def, l0_event_connected_def,
      res_val_def, port_bytes_def, AllCaseEqs()]
QED

Theorem sys_connect_ev:
  sys_connect a w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_connect»
Proof
  rw[sys_connect_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

(* The output poll on f: f's entry asks for output *)
Theorem sys_poll_out:
  sys_poll fes w = SOME (out, w', ev) ∧ l0_rely w ∧ MEM (f, e) fes ∧ small f ∧
  2 ≤ e ∧ e < 4 ⇒
  out_poll f ev
Proof
  simp[sys_poll_def] >> strip_tac >>
  ‘LENGTH out = LENGTH (poll_buf fes)’
    by (gvs[l0_do_buf_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_buf_cases >> strip_tac >> gvs[out_poll_def, MAP_ZIP] >>
  simp[poll_buf_def, DROP_APPEND, pollfd_entries_buf, MAP_MAP_o, MEM_MAP, PULL_EXISTS] >>
  ‘pe_fe (pfd_bytes (f, e)) = (f, e)’ by metis_tac[pe_pfd_bytes] >>
  qexists_tac ‘e’ >> qexists_tac ‘(f, e)’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   The actions
   ------------------------------------------------------------------------ *)

Theorem forget_gone_sub:
  MEM f (forget g b).gone ⇒ MEM f b.gone
Proof
  simp[forget_def, set_outbox_def, MEM_FILTER]
QED

Theorem after_send_gone:
  MEM f (after_send g r b).gone ⇒
  MEM f b.gone ∨ f = g ∧ ∃e x. r = Fail e x ∧ ¬l1_transient e
Proof
  rw[after_send_def] >> every_case_tac >> gvs[set_outbox_def, MEM_FILTER]
QED

Theorem ADELKEY_keep_snd:
  ALL_DISTINCT (MAP FST l) ∧ ALOOKUP l h = SOME g ∧ g ≠ f ∧ MEM f (MAP SND l) ⇒
  MEM f (MAP SND (ADELKEY h l))
Proof
  rw[ADELKEY_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 ‘MEM (k, f) l’ >> qexists_tac ‘k’ >> simp[] >> strip_tac >> gvs[] >>
  drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

(* f kept: held, with output pending, not gone *)
Definition kp_def:
  kp f (b : l1st) ⇔ held b f ∧ outbox_of b f ≠ [] ∧ ¬MEM f b.gone
End

Theorem kp_forget:
  g ≠ f ∧ kp f b ⇒ kp f (forget g b)
Proof
  strip_tac >> fs[kp_def, held_def, forget_def, outbox_of_set_outbox, MEM_FILTER] >>
  gvs[outbox_of_def]
QED

Theorem kp_set_outbox_other:
  g ≠ f ⇒ (kp f (set_outbox g bs b) ⇔ kp f b)
Proof
  rw[kp_def, held_def, outbox_of_set_outbox]
QED

Theorem kp_after_send_other:
  g ≠ f ∧ kp f b ⇒ kp f (after_send g r b)
Proof
  rw[after_send_def] >> every_case_tac >> simp[kp_set_outbox_other] >>
  gvs[kp_def, held_def, MEM_FILTER]
QED

Theorem kp_append:
  kp f b ⇒ kp f (set_outbox f (outbox_of b f ++ bs) b)
Proof
  rw[kp_def, held_def, outbox_of_set_outbox]
QED

Theorem kp_tbl_cons:
  kp f b ⇒ kp f (b with <| tbl := x :: b.tbl; nxt := n |>)
Proof
  strip_tac >> fs[kp_def, held_def, outbox_of_def]
QED

Theorem kp_adelkey:
  ALL_DISTINCT (MAP FST b.tbl) ∧ ALOOKUP b.tbl h = SOME g ∧ g ≠ f ∧ kp f b ⇒
  kp f (b with tbl := ADELKEY h b.tbl)
Proof
  rw[kp_def, held_def, outbox_of_def] >> metis_tac[ADELKEY_keep_snd]
QED

Theorem kp_adelkey_closing:
  kp f b ⇒ kp f (b with <| tbl := ADELKEY h b.tbl; closing := g :: b.closing |>) ∨ g ≠ f
Proof
  rw[kp_def, held_def, outbox_of_def] >> metis_tac[]
QED

Theorem pdo_gone:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧ MEM f ps'.b.gone ⇒
  MEM f ps.b.gone ∨ EXISTS (hard_err_on f) evs
Proof
  Cases_on ‘a’ >> simp[pdo_def, l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >>
  gvs[set_inb_def] >>
  TRY (drule forget_gone_sub >> simp[] >> NO_TAC) >>
  drule after_send_gone >> strip_tac >> gvs[] >>
  metis_tac[sys_send_hard]
QED

Theorem pdo_keep:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧ pown lfd ps ∧ kp f ps.b ⇒
  kp f ps'.b ∧ ¬EXISTS (send_took f) evs
Proof
  ‘ALL_DISTINCT (MAP FST ps.b.tbl) ⇒ ALL_DISTINCT (MAP FST ps.b.tbl)’ by simp[] >>
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- (gvs[AllCaseEqs()] >> irule kp_tbl_cons >> simp[])
  >- (‘ALL_DISTINCT (MAP FST ps.b.tbl)’ by fs[pown_def] >>
      gvs[AllCaseEqs()] >> TRY (gvs[set_inb_def] >> NO_TAC)
      >- (rename1 ‘ALOOKUP ps.b.tbl h = SOME g’ >>
          ‘g ≠ f’ by (strip_tac >> gvs[kp_def]) >>
          PairCases_on ‘z’ >> gvs[l1_close_def, AllCaseEqs()] >>
          drule sys_close_ev >> strip_tac >>
          ‘¬send_took f ev’ by (irule name_not_took >> simp[]) >> simp[] >>
          irule kp_forget >> simp[] >> irule kp_adelkey >> simp[] >> metis_tac[])
      >- (rename1 ‘ALOOKUP ps.b.tbl h = SOME g’ >>
          ‘g ≠ f’ by (strip_tac >> gvs[kp_def]) >>
          PairCases_on ‘z’ >> gvs[l1_close_def, AllCaseEqs()] >>
          drule sys_close_ev >> strip_tac >>
          ‘¬send_took f ev’ by (irule name_not_took >> simp[]) >> simp[] >>
          irule kp_forget >> simp[] >> irule kp_adelkey >> simp[] >> metis_tac[]) >>
      gvs[kp_def, held_def, outbox_of_def] >> metis_tac[ADELKEY_keep_snd]) >>
  PairCases_on ‘z’ >> gvs[l1do_def, AllCaseEqs()]
  >- (Cases_on ‘f' = f’ >- (gvs[] >> irule kp_append >> simp[]) >>
      simp[kp_set_outbox_other])
  >- (rename1 ‘ALOOKUP ps.b.tbl h = SOME g’ >>
      ‘g ≠ f’ by (strip_tac >> gvs[kp_def]) >>
      conj_tac >- (irule kp_after_send_other >> simp[kp_set_outbox_other]) >>
      strip_tac >> drule_all sys_send_took >> simp[])
QED

Theorem pdo_plain:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  EVERY (λe. ¬poll_ev e ∧ ¬opens g e) evs
Proof
  strip_tac >> drule pdo_names >> rw[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  FIRST [irule name_not_poll >> simp[] >> NO_TAC, irule name_not_opens >> simp[] >> NO_TAC]
QED

Theorem edo_gone:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ l0_rely w ∧ MEM f es'.p.b.gone ⇒
  MEM f es.p.b.gone ∨ EXISTS (hard_err_on f) evs
Proof
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_gone >> simp[] >> NO_TAC) >>
  PairCases_on ‘z’ >> gvs[l1_close_def, AllCaseEqs()] >> metis_tac[forget_gone_sub]
QED

Theorem eown_ctbl_not_held:
  eown lfd es ∧ ALOOKUP es.ctbl h = SOME g ∧ held es.p.b f ⇒ g ≠ f
Proof
  rw[eown_def, held_def] >>
  drule ALOOKUP_MEM >> strip_tac >>
  ‘MEM g (MAP SND es.ctbl)’ by (simp[MEM_MAP] >> qexists_tac ‘(h, g)’ >> simp[]) >>
  strip_tac >> gvs[ALL_DISTINCT_APPEND, MEM_APPEND]
QED

Theorem edo_keep:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ l0_rely w ∧ eown lfd es ∧ kp f es.p.b ⇒
  kp f es'.p.b ∧ ¬EXISTS (send_took f) evs
Proof
  strip_tac >> ‘pown lfd es.p’ by fs[eown_def] >>
  qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >>
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> strip_tac >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_keep >> simp[] >> NO_TAC) >>
  TRY (drule sys_connect_ev >> strip_tac >>
       ‘¬send_took f ev’ by (irule name_not_took >> simp[]) >>
       gvs[kp_def, held_def, outbox_of_def] >> NO_TAC) >>
  rename1 ‘ALOOKUP es.ctbl h = SOME g’ >>
  ‘g ≠ f’ by (irule eown_ctbl_not_held >> gvs[kp_def] >> metis_tac[]) >>
  PairCases_on ‘z’ >> gvs[l1_close_def, AllCaseEqs()] >>
  drule sys_close_ev >> strip_tac >>
  ‘¬send_took f ev’ by (irule name_not_took >> simp[]) >> simp[] >>
  irule kp_forget >> simp[]
QED

Theorem edo_nopoll:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒ EVERY (λe. ¬poll_ev e) evs
Proof
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule pdo_plain >> rw[EVERY_MEM] >> first_x_assum drule >> simp[] >> NO_TAC) >>
  TRY (drule sys_connect_ev >> strip_tac >> irule name_not_poll >> simp[] >> NO_TAC) >>
  gvs[l1_close_def, AllCaseEqs()] >> drule sys_close_ev >> strip_tac >>
  irule name_not_poll >> simp[]
QED

Theorem edo_stalls:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒ es'.p.stalls = es.p.stalls
Proof
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’) >> gvs[] >> imp_res_tac pdo_stalls >> simp[]
QED

Theorem edo_gok:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ gok f es.p.b ⇒ gok f es'.p.b
Proof
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule_all pdo_gok >> simp[] >> NO_TAC) >>
  TRY (gvs[gok_def, outbox_of_def] >> NO_TAC) >>
  gvs[l1_close_def, AllCaseEqs()] >> metis_tac[forget_gok]
QED

Theorem edo_opens:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ l0_rely w ∧ EXISTS (opens g) evs ⇒
  ∃h. ALOOKUP es'.ctbl h = SOME g ∧ cstat_of es' g = CPending
Proof
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule pdo_plain >>
       disch_then (qspec_then ‘g’ assume_tac) >> gvs[EVERY_MEM, EXISTS_MEM] >>
       metis_tac[] >> NO_TAC) >>
  TRY (drule_all sys_connect_opens >> strip_tac >> qexists_tac ‘hdl lfd es.p.b.nxt’ >>
       gvs[cstat_of_def] >> NO_TAC) >>
  PairCases_on ‘z’ >> gvs[l1_close_def, AllCaseEqs()] >>
  drule sys_close_ev >> strip_tac >>
  ‘¬opens g ev’ by (irule name_not_opens >> simp[]) >> gvs[]
QED

(* A property of the state before each action, passed to the rest *)
Theorem eacts_prefix_tl:
  edo lfd pol ws a = SOME (r1, ws1, evs1) ∧
  (∀i rs0 evs0 wi esi.
     i < LENGTH (a :: acts) ∧ eacts lfd pol ws (TAKE i (a :: acts)) = SOME (rs0, evs0, (wi, esi)) ⇒
     P esi) ⇒
  P (SND ws) ∧
  ∀i rs0 evs0 wi esi.
    i < LENGTH acts ∧ eacts lfd pol ws1 (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒ P esi
Proof
  strip_tac >> conj_tac
  >- (first_x_assum (qspecl_then [‘0’, ‘[]’, ‘[]’, ‘FST ws’, ‘SND ws’] mp_tac) >>
      simp[eacts_def]) >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [‘SUC i’, ‘r1 :: rs0’, ‘evs1 ++ evs0’, ‘wi’, ‘esi’] mp_tac) >>
  simp[eacts_def]
QED

(* A pending connect stays pending and in the table *)
Definition pendc_def:
  pendc es g ⇔ ∃h. ALOOKUP es.ctbl h = SOME g ∧ cstat_of es g = CPending
End

Theorem edo_pendc:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ eown lfd es ∧ pendc es g ⇒ pendc es' g
Proof
  rewrite_tac[pendc_def] >> strip_tac >>
  qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >>
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> strip_tac >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’ >> gvs[cstat_of_def] >> qexists_tac ‘h’ >> simp[] >> NO_TAC) >>
  TRY (qexists_tac ‘h’ >> simp[] >> NO_TAC) >>
  TRY (rename1 ‘sys_connect _ _ = SOME (out, _, _)’ >>
       Cases_on ‘n2w (res_val out) = g’
       >- (qexists_tac ‘hdl lfd es.p.b.nxt’ >> gvs[cstat_of_def]) >>
       qexists_tac ‘h’ >>
       ‘∃i. i < es.p.b.nxt ∧ h = hdl lfd i’ by (fs[eown_def] >> metis_tac[]) >>
       ‘h ≠ hdl lfd es.p.b.nxt’ by (rveq >> irule hdl_fresh >> gvs[l1hdl_hdl]) >>
       gvs[cstat_of_def, ALOOKUP_ADELKEY] >> NO_TAC) >>
  rename1 ‘ALOOKUP es.ctbl c = SOME f’ >>
  ‘f ≠ g’ by (strip_tac >> gvs[]) >>
  ‘c ≠ h’ by (strip_tac >> gvs[]) >>
  PairCases_on ‘z’ >> gvs[l1_close_def, AllCaseEqs()] >>
  qexists_tac ‘h’ >> gvs[cstat_of_def, ALOOKUP_ADELKEY]
QED

(* The round's actions *)
Theorem eacts_gone:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧
    l0_rely w ∧ fds_lt w ∧ l0owne lfd w es ∧
    (∀i rs0 evs0 wi esi.
       i < LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
       eown lfd esi) ⇒
    es'.p.stalls = es.p.stalls ∧ EVERY (λe. ¬poll_ev e) evs ∧
    (∀f. MEM f es'.p.b.gone ⇒ MEM f es.p.b.gone ∨ EXISTS (hard_err_on f) evs) ∧
    (∀f. kp f es.p.b ⇒ kp f es'.p.b ∧ ¬EXISTS (send_took f) evs) ∧
    (∀f. gok f es.p.b ⇒ gok f es'.p.b) ∧
    (∀g. pendc es g ⇒ pendc es' g) ∧
    (∀g. EXISTS (opens g) evs ⇒ pendc es' g)
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  qspecl_then [‘lfd’, ‘pol’, ‘(w, es)’, ‘h’, ‘r1’, ‘(ws10, ws11)’, ‘evs1’, ‘acts’, ‘eown lfd’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ws’, ‘a’, ‘r1’, ‘ws1’, ‘evs1’, ‘acts’, ‘P’] eacts_prefix_tl) >>
  impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> rewrite_tac[LENGTH] >> first_assum ACCEPT_TAC) >>
  simp[] >> strip_tac >>
  drule_all edo_l0 >> strip_tac >>
  first_x_assum (qspecl_then [‘ws10’, ‘ws11’, ‘rs'’, ‘evs'’, ‘w'’, ‘es'’] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum ‘∀i rs0 evs0 wi esi. i < SUC _ ∧ _ ⇒ _’ kall_tac >>
  qpat_x_assum ‘∀i rs0 evs0 wi esi. i < LENGTH _ ∧ _ ⇒ _’ kall_tac >>
  ‘ws11.p.stalls = es.p.stalls’ by (drule edo_stalls >> simp[]) >>
  ‘EVERY (λe. ¬poll_ev e) evs1’ by (drule edo_nopoll >> simp[]) >>
  rpt conj_tac
  >- asm_rewrite_tac[]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> qpat_x_assum ‘∀f. MEM f es'.p.b.gone ⇒ _’ drule >> strip_tac >> asm_rewrite_tac[] >>
      drule_all edo_gone >> strip_tac >> asm_rewrite_tac[])
  >- (gen_tac >> strip_tac >> drule_all edo_keep >> strip_tac >>
      qpat_x_assum ‘∀f. kp f ws11.p.b ⇒ _’ drule >> strip_tac >> fs[NOT_EXISTS])
  >- (rpt strip_tac >> qpat_x_assum ‘∀f. gok f ws11.p.b ⇒ _’ irule >>
      drule_all edo_gok >> simp[])
  >- (rpt strip_tac >> qpat_x_assum ‘∀g. pendc ws11 g ⇒ _’ irule >>
      drule_all edo_pendc >> simp[]) >>
  rpt strip_tac
  >- (qpat_x_assum ‘∀g. pendc ws11 g ⇒ _’ irule >> rewrite_tac[pendc_def] >>
      drule_all edo_opens >> simp[]) >>
  qpat_x_assum ‘∀g. EXISTS (opens g) evs' ⇒ _’ irule >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   The round's tail
   ------------------------------------------------------------------------ *)

Theorem used_small:
  l0_rely w ∧ fds_lt w ∧ MEM f (l0_used w) ⇒ small f
Proof
  rw[l0_rely_def, fds_lt_def, small_def] >> res_tac >> decide_tac
QED

Theorem l1_flush_gone:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ MEM f b'.gone ⇒
    MEM f b.gone ∨ EXISTS (hard_err_on f) evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘l0_rely w''’ by (gvs[sys_send_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  drule after_send_gone >> strip_tac >> simp[] >> gvs[] >>
  metis_tac[sys_send_hard]
QED

Theorem l1_flush_rely:
  ∀fs w b w' b' evs. l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒ l0_rely w'
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘l0_rely w''’ by (gvs[sys_send_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_took:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ EXISTS (send_took f) evs ⇒
    LENGTH (outbox_of b' f) < LENGTH (outbox_of b f)
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘l0_rely w''’ by (gvs[sys_send_def] >> metis_tac[l0_do_rely]) >>
  rename1 ‘sys_send g _ w = SOME (out, w1, ev)’ >>
  ‘LENGTH (outbox_of b' f) ≤ LENGTH (outbox_of (after_send g (l0_res_of out) b) f)’
    by (irule l1_flush_le >> metis_tac[]) >>
  ‘LENGTH (outbox_of (after_send g (l0_res_of out) b) f) ≤ LENGTH (outbox_of b f)’
    by simp[after_send_le] >>
  gvs[]
  >- (drule_all sys_send_took >> strip_tac >> gvs[] >>
      ‘LENGTH (outbox_of (after_send f (Ok k) b) f) < LENGTH (outbox_of b f)’
        by (simp[after_send_def, outbox_of_set_outbox] >>
            Cases_on ‘outbox_of b f’ >> gvs[]) >>
      gvs[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_plain:
  l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒ EVERY (λe. ¬poll_ev e ∧ ¬opens g e) evs
Proof
  strip_tac >> drule l1_flush_names >> rw[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  FIRST [irule name_not_poll >> simp[] >> NO_TAC, irule name_not_opens >> simp[] >> NO_TAC]
QED

Theorem pf_fetch_facts:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ⇒
    l0_rely w' ∧
    (∀f. MEM (FReset f) log ⇒ EXISTS (hard_err_on f) evs) ∧
    (∀g. EXISTS (opens g) evs ⇒ MEM (FConn g) log)
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (qpat_x_assum ‘(case sys_accept _ _ of NONE => _ | SOME _ => _) = _’ mp_tac >>
      CASE_TAC >> simp[] >> PairCases_on ‘x’ >> simp[] >> pairarg_tac >>
      simp[AllCaseEqs()] >> strip_tac >> rveq >>
      ‘l0_rely x1’ by (gvs[sys_accept_def] >> drule_all l0_do_ev >> simp[]) >>
      first_x_assum drule_all >> strip_tac >> simp[] >>
      ‘(∀f. ¬MEM (FReset f ) fl') ∧ ∀g. opens g x2 ⇒ MEM (FConn g) fl'’
        by (qpat_x_assum ‘_ = (ps1, fl')’ mp_tac >> CASE_TAC >> rw[] >>
            TRY (CCONTR_TAC >> fs[]) >> drule_all sys_accept_opens >> strip_tac >> gvs[]) >>
      metis_tac[]) >>
  qpat_x_assum ‘(case sys_recv _ _ _ of NONE => _ | SOME _ => _) = _’ mp_tac >>
  CASE_TAC >> simp[] >> PairCases_on ‘x’ >> simp[] >> pairarg_tac >>
  simp[AllCaseEqs()] >> strip_tac >> rveq >>
  ‘l0_rely x1’ by (gvs[sys_recv_def] >> drule_all l0_do_ev >> simp[]) >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  ‘∀g. ¬opens g x2’
    by (drule sys_recv_ev >> strip_tac >> gen_tac >> irule name_not_opens >> simp[]) >>
  ‘(∀g. ¬MEM (FConn g ) fl') ∧ ∀g. MEM (FReset g) fl' ⇒ hard_err_on g x2’
    by (qpat_x_assum ‘_ = (ps1, fl')’ mp_tac >> rpt CASE_TAC >> rw[] >> gvs[MEM] >>
        drule_all sys_recv_hard >> simp[]) >>
  metis_tac[]
QED

Theorem pf_fetch_plain:
  pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
  EVERY (λe. ¬poll_ev e ∧ ¬send_took f e) evs
Proof
  strip_tac >> drule pf_fetch_names >> rw[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  FIRST [irule name_not_poll >> simp[] >> NO_TAC, irule name_not_took >> simp[] >> NO_TAC]
QED

Theorem l1_reap_plain:
  l1_reap fs (w, b) = SOME ((w', b'), evs) ⇒ EVERY (plain f) evs
Proof
  strip_tac >> drule l1_reap_names >> simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> irule name_plain >> simp[]
QED

Theorem l1_reap_gone_sub:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ MEM f b'.gone ⇒ MEM f b.gone
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >> rw[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> gvs[l1_close_def, AllCaseEqs()] >>
  first_x_assum drule_all >> metis_tac[forget_gone_sub]
QED

Theorem settle_fds_plain:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ es'.p = es.p ∧ EVERY (plain f) evs
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> rveq >> first_x_assum drule >> strip_tac >>
  drule sys_connerr_ev >> strip_tac >> simp[] >>
  TRY (irule name_plain >> simp[] >> NO_TAC) >>
  rpt CASE_TAC >> simp[]
QED

(* The tail's events after its one poll: the stalled ones (a poll listing
   f for output, then no poll and no send that took bytes on f) *)
Definition tstall_def:
  tstall f tevs ⇔
    ∃pev Z. tevs = pev :: Z ∧ out_poll f pev ∧ EVERY (λe. ¬poll_ev e) Z ∧
            ¬EXISTS (send_took f) Z
End

(* L1's state facts kept across rounds *)
Definition RI_def:
  RI (es : l1e) ⇔
    (∀f. gok f es.p.b) ∧ ALL_DISTINCT (MAP FST es.p.stalls) ∧
    ∀f c. MEM (f, c) es.p.stalls ∧ 0 < c ⇒ kp f es.p.b
End

(* etail, step by step *)
Theorem etail_split:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ⇒
  ∃fes pout w1 pev fs1 w2 b2 fevs fs2 w3 ps3' gevs w4 b4 cevs sevs.
    fes = pf_poll_set lfd pol es.p hs ++ MAP (λf. (f, 2n)) (pend_fds es) ∧
    sys_poll fes w = SOME (pout, w1, pev) ∧
    l1_flush fs1 (w1, es.p.b) = SOME ((w2, b2), fevs) ∧
    pf_fetch lfd pol fs2 (w2, es.p with b := b2) = SOME ((w3, ps3'), log, gevs) ∧
    l1_reap (stall_step (pf_held ps3') (outbox_of es.p.b) log ps3').b.closing
      (w3, (stall_step (pf_held ps3') (outbox_of es.p.b) log ps3').b) = SOME ((w4, b4), cevs) ∧
    (∀f. EVERY (plain f) sevs) ∧
    es'.p.stalls = (stall_step (pf_held ps3') (outbox_of es.p.b) log ps3').stalls ∧
    es'.p.b.gone = b4.gone ∧ es'.p.b.outbox = b4.outbox ∧ es'.p.b.closing = b4.closing ∧
    (∀f. MEM f (MAP SND b4.tbl) ⇒ MEM f (MAP SND es'.p.b.tbl)) ∧
    tevs = pev :: (fevs ++ gevs ++ cevs ++ sevs)
Proof
  simp[etail_def, AllCaseEqs(), l1_polls_def] >> strip_tac >> gvs[] >>
  ‘∀f. EVERY (plain f) sevs’ by (gen_tac >> drule settle_fds_plain >> simp[]) >>
  drule settle_fds_plain >> simp[apply_early_def] >> strip_tac >>
  ntac 3 (first_assum (irule_at Any)) >>
  simp[promote_def, MEM_MAP, MEM_FILTER, PULL_EXISTS] >> metis_tac[]
QED

(* A held fd with output pending is polled for output *)
Theorem out_poll_held:
  sys_poll (pf_poll_set lfd pol es.p hs ++ X) w = SOME (pout, w1, pev) ∧ l0_rely w ∧ fds_lt w ∧
  eown lfd es ∧ l0owne lfd w es ∧ okeys es.p.b ∧ outbox_of es.p.b f ≠ [] ⇒
  out_poll f pev
Proof
  strip_tac >>
  ‘MEM f (MAP SND es.p.b.tbl) ∨ MEM f es.p.b.closing’ by fs[okeys_def] >>
  ‘f ≠ lfd’ by (fs[eown_def] >> strip_tac >> rveq >> fs[ALL_DISTINCT_APPEND, MEM_APPEND]) >>
  ‘MEM f (l0_used w)’ by fs[l0owne_def, l0own_def] >>
  ‘small f’ by metis_tac[used_small] >>
  ‘∃e. MEM (f, e) (pf_poll_set lfd pol es.p hs) ∧ 2 ≤ e ∧ e < 4’
    by (irule pf_poll_set_out >> simp[]) >>
  drule_then irule sys_poll_out >> simp[] >> qexists_tac ‘e’ >> simp[]
QED

(* The tail stalls f when its flush took nothing from f's outbox *)
Theorem tail_tstall:
  sys_poll fes w = SOME (pout, w1, pev) ∧ l0_rely w ∧ out_poll f pev ∧
  l1_flush fs1 (w1, b0) = SOME ((w2, b2), fevs) ∧
  pf_fetch lfd pol fs2 (w2, ps2) = SOME ((w3, ps3'), log, gevs) ∧
  l1_reap fs3 (w3, b3) = SOME ((w4, b4), cevs) ∧ EVERY (plain f) sevs ∧
  ¬(LENGTH (outbox_of b2 f) < LENGTH (outbox_of b0 f)) ⇒
  tstall f (pev :: (fevs ++ gevs ++ cevs ++ sevs))
Proof
  strip_tac >>
  ‘l0_rely w1’
    by (qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >>
        strip_tac >> drule_all l0_do_buf_rely >> simp[]) >>
  ‘¬EXISTS (send_took f) fevs’ by (strip_tac >> drule_all l1_flush_took >> simp[]) >>
  ‘EVERY (λe. ¬poll_ev e ∧ ¬opens f e) fevs’ by (drule l1_flush_plain >> simp[]) >>
  ‘EVERY (λe. ¬poll_ev e ∧ ¬send_took f e) gevs’ by (drule pf_fetch_plain >> simp[]) >>
  ‘EVERY (plain f) cevs’ by (drule l1_reap_plain >> simp[]) >>
  rewrite_tac[tstall_def] >> qexistsl [‘pev’, ‘fevs ++ gevs ++ cevs ++ sevs’] >>
  fs[EVERY_MEM, EXISTS_MEM, plain_def] >> metis_tac[]
QED

Theorem sys_poll_ev:
  sys_poll fes w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_poll»
Proof
  rw[sys_poll_def] >> drule l0_do_buf_cases >> rw[] >> simp[ev_name_def]
QED

(* The tail's opens are its fetch's *)
Theorem tail_opens:
  sys_poll fes w = SOME (pout, w1, pev) ∧
  l1_flush fs1 (w1, b0) = SOME ((w2, b2), fevs) ∧
  l1_reap fs3 (w3, b3) = SOME ((w4, b4), cevs) ∧ EVERY (plain g) sevs ∧
  EXISTS (opens g) (pev :: (fevs ++ gevs ++ cevs ++ sevs)) ⇒
  EXISTS (opens g) gevs
Proof
  strip_tac >>
  ‘¬opens g pev’ by (drule sys_poll_ev >> strip_tac >> irule name_not_opens >> simp[]) >>
  ‘EVERY (λe. ¬poll_ev e ∧ ¬opens g e) fevs’ by (drule l1_flush_plain >> simp[]) >>
  ‘EVERY (plain g) cevs’ by (drule l1_reap_plain >> simp[]) >>
  fs[EVERY_MEM, EXISTS_MEM, plain_def] >> metis_tac[]
QED

Theorem gok_fields:
  b'.gone = b.gone ∧ b'.outbox = b.outbox ⇒ (gok f b' ⇔ gok f b)
Proof
  simp[gok_def, outbox_of_def]
QED

Theorem stall_reap_gok:
  gok f ps.b ∧ l1_reap fs (w, (stall_step hfs ob lg ps).b) = SOME ((w', b'), evs) ⇒ gok f b'
Proof
  strip_tac >> irule l1_reap_gok >> first_assum (irule_at Any) >>
  qspecl_then [‘stall_step hfs ob lg ps’, ‘hfs’, ‘ob’, ‘lg’, ‘ps’, ‘f’] mp_tac
    (Q.GENL [‘ps'’, ‘hfs’, ‘ob’, ‘log’, ‘ps’, ‘f’] stall_f) >>
  fs[gok_def]
QED

(* A stalled f still counted after the stall step ends the reap kept *)
Theorem stall_reap_kp:
  gok f ps.b ∧ ALL_DISTINCT (MAP FST ps.stalls) ∧
  MEM (f, m) (stall_step hfs ob lg ps).stalls ∧ 0 < m ∧
  l1_reap fs (w, (stall_step hfs ob lg ps).b) = SOME ((w', b'), evs) ⇒
  outbox_of b' f ≠ [] ∧ ¬MEM f b'.gone ∧ (MEM f (MAP SND b'.tbl) ∨ MEM f b'.closing)
Proof
  strip_tac >>
  ‘outbox_of ps.b f ≠ []’ by (drule stall_step_entry >> strip_tac >> gvs[]) >>
  ‘MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing’ by (drule stall_step_held >> simp[]) >>
  ‘¬MEM f ps.b.gone’ by gvs[gok_def] >>
  ‘∀g. MEM g (stall_drops hfs ob lg ps) ⇒ ¬MEM g (MAP FST (stall_step hfs ob lg ps).stalls)’
    by metis_tac[stall_step_distinct] >>
  ‘¬MEM f (stall_drops hfs ob lg ps)’
    by (strip_tac >> first_x_assum drule >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘outbox_of (stall_step hfs ob lg ps).b f = outbox_of ps.b f ∧
   ¬MEM f (stall_step hfs ob lg ps).b.gone’
    by (simp[stall_step_drops] >> drule FOLDL_drop_other >>
        disch_then (qspec_then ‘ps.b’ mp_tac) >> simp[]) >>
  drule l1_reap_keep_b >> disch_then (qspec_then ‘f’ mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem etail_gone:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  l0_rely w ∧ fds_lt w ∧ eown lfd es ∧ l0owne lfd w es ∧ okeys es.p.b ∧
  (∀f. gok f es.p.b) ∧ ALL_DISTINCT (MAP FST es.p.stalls) ⇒
  (∀g. EXISTS (opens g) tevs ⇒ MEM (FConn g) log) ∧
  (∀f. MEM f es'.p.b.gone ⇒
       MEM f es.p.b.gone ∨ EXISTS (hard_err_on f) tevs ∨
       (∃n. pf_sendwait ≤ n + 1 ∧ MEM (f, n) es.p.stalls) ∧ tstall f tevs) ∧
  (∀f m. MEM (f, m) es'.p.stalls ∧ 0 < m ⇒
         tstall f tevs ∧ (m = 1 ∨ MEM (f, m − 1) es.p.stalls)) ∧
  RI es'
Proof
  strip_tac >> drule etail_split >> strip_tac >>
  qpat_x_assum ‘fes = _’ SUBST_ALL_TAC >>
  ‘ps3'.stalls = es.p.stalls ∧ ps3'.b = b2’
    by (drule pf_fetch_stalls >> drule pf_fetch_b >> simp[]) >>
  ‘l0_rely w1’
    by (qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >>
        strip_tac >> drule_all l0_do_buf_rely >> simp[]) >>
  ‘l0_rely w2’ by (drule_all l1_flush_rely >> simp[]) >>
  drule_all pf_fetch_facts >> strip_tac >>
  ‘∀f. outbox_of b2 f ≠ [] ∧ ¬(LENGTH (outbox_of b2 f) < LENGTH (outbox_of es.p.b f)) ⇒
       tstall f tevs’
    by (rpt strip_tac >>
        ‘outbox_of es.p.b f ≠ []’
          by (drule l1_flush_le >> disch_then (qspec_then ‘f’ mp_tac) >>
              strip_tac >> strip_tac >> fs[]) >>
        ‘out_poll f pev’
          by (drule out_poll_held >> disch_then (qspec_then ‘f’ mp_tac) >>
              impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
        ‘EVERY (plain f) sevs’
          by (qpat_x_assum ‘∀f. EVERY (plain f) sevs’ (qspec_then ‘f’ ACCEPT_TAC)) >>
        qpat_x_assum ‘tevs = _’ SUBST1_TAC >> drule_all tail_tstall >> simp[]) >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3'’ >>
  rpt conj_tac
  >- ((* opens *)
      gen_tac >> strip_tac >>
      qpat_x_assum ‘∀g. EXISTS (opens g) gevs ⇒ _’ irule >>
      ‘EVERY (plain g) sevs’
        by (qpat_x_assum ‘∀f. EVERY (plain f) sevs’ (qspec_then ‘g’ ACCEPT_TAC)) >>
      qpat_x_assum ‘EXISTS _ tevs’ mp_tac >> qpat_x_assum ‘tevs = _’ SUBST1_TAC >>
      strip_tac >> drule_all tail_opens >> simp[])
  >- ((* gone *)
      gen_tac >> qpat_x_assum ‘es'.p.b.gone = _’ SUBST1_TAC >> strip_tac >>
      drule_all l1_reap_gone >>
      simp[Abbr ‘ps3’, stall_gone] >>
      qpat_assum ‘ps3'.b = b2’ (fn th => rewrite_tac[th]) >> strip_tac
      >- (drule_all l1_flush_gone >> strip_tac >- simp[] >>
          qpat_x_assum ‘EXISTS _ fevs’ (fn th => qpat_x_assum ‘tevs = _’ SUBST1_TAC >> simp[th])) >>
      drule stall_drops_entry >> strip_tac
      >- (qpat_x_assum ‘∀f. MEM (FReset f) log ⇒ _’ drule >> strip_tac >>
          qpat_x_assum ‘EXISTS _ gevs’ (fn th => qpat_x_assum ‘tevs = _’ SUBST1_TAC >> simp[th])) >>
      gvs[] >> disj2_tac >> disj2_tac >> rpt conj_tac >>
      TRY (qexists_tac ‘n’ >> simp[] >> NO_TAC) >>
      qpat_x_assum ‘∀f. outbox_of _ f ≠ [] ∧ _ ⇒ _’ irule >> simp[])
  >- ((* stalls *)
      rpt gen_tac >> qpat_x_assum ‘es'.p.stalls = _’ SUBST1_TAC >> strip_tac >>
      qpat_x_assum ‘MEM _ ps3.stalls’ mp_tac >> simp[Abbr ‘ps3’] >> strip_tac >>
      drule stall_step_entry >> strip_tac >> gvs[] >>
      qpat_x_assum ‘∀f. outbox_of b2 f ≠ [] ∧ _ ⇒ _’ irule >> simp[]) >>
  (* RI *)
  rewrite_tac[RI_def] >> rpt conj_tac
  >- (gen_tac >>
      ‘gok f es'.p.b ⇔ gok f b4’ by (irule gok_fields >> simp[]) >> simp[] >>
      qpat_x_assum ‘l1_reap _ _ = _’ mp_tac >> simp[Abbr ‘ps3’] >> strip_tac >>
      irule stall_reap_gok >> first_assum (irule_at Any) >>
      qpat_assum ‘ps3'.b = b2’ (fn th => rewrite_tac[th]) >>
      drule l1_flush_gok >> disch_then irule >>
      qpat_x_assum ‘∀f. gok f es.p.b’ (qspec_then ‘f’ ACCEPT_TAC))
  >- (qpat_x_assum ‘es'.p.stalls = _’ SUBST1_TAC >> simp[Abbr ‘ps3’] >>
      ‘ALL_DISTINCT (MAP FST ps3'.stalls)’ by asm_rewrite_tac[] >>
      drule stall_step_distinct >> simp[]) >>
  rpt gen_tac >> qpat_x_assum ‘es'.p.stalls = _’ SUBST1_TAC >> strip_tac >>
  qpat_x_assum ‘l1_reap _ _ = _’ mp_tac >> qpat_x_assum ‘MEM _ ps3.stalls’ mp_tac >>
  simp[Abbr ‘ps3’] >> rpt strip_tac >>
  ‘gok f ps3'.b’
    by (qpat_assum ‘ps3'.b = b2’ (fn th => rewrite_tac[th]) >>
        drule l1_flush_gok >> disch_then irule >>
        qpat_x_assum ‘∀f. gok f es.p.b’ (qspec_then ‘f’ ACCEPT_TAC)) >>
  ‘ALL_DISTINCT (MAP FST ps3'.stalls)’ by asm_rewrite_tac[] >>
  drule_all stall_reap_kp >> strip_tac >>
  simp[kp_def, held_def, outbox_of_def] >> gvs[outbox_of_def]
QED

(* ------------------------------------------------------------------------
   A round
   ------------------------------------------------------------------------ *)


Theorem eacts_l0:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧
    l0_rely w ∧ fds_lt w ∧ l0owne lfd w es ∧
    (∀i rs0 evs0 wi esi.
       i < LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
       eown lfd esi) ⇒
    l0_rely w' ∧ fds_lt w' ∧ l0owne lfd w' es'
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  qspecl_then [‘lfd’, ‘pol’, ‘(w, es)’, ‘h’, ‘r1’, ‘(ws10, ws11)’, ‘evs1’, ‘acts’, ‘eown lfd’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ws’, ‘a’, ‘r1’, ‘ws1’, ‘evs1’, ‘acts’, ‘P’] eacts_prefix_tl) >>
  impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> rewrite_tac[LENGTH] >> first_assum ACCEPT_TAC) >>
  simp[] >> strip_tac >>
  drule_all edo_l0 >> strip_tac >>
  first_x_assum (qspecl_then [‘ws10’, ‘ws11’, ‘rs'’, ‘evs'’, ‘w'’, ‘es'’] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

Theorem pendc_ctbl:
  pendc es g ⇒ MEM g (MAP SND es.ctbl)
Proof
  rw[pendc_def, MEM_MAP] >> drule ALOOKUP_MEM >> strip_tac >>
  qexists_tac ‘(h, g)’ >> simp[]
QED

Theorem tstall_stalled:
  tstall f tevs ∧ EVERY (λe. ¬poll_ev e) aevs ∧ (full ⇒ ¬EXISTS (send_took f) aevs) ⇒
  stalled f full (aevs ++ tevs)
Proof
  rw[tstall_def, stalled_def] >> qexistsl [‘aevs’, ‘pev’, ‘Z’] >> simp[]
QED

Theorem eround_gone:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, R) ∧
  (∀i rs0 evs0 wi esi.
     i ≤ LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
     eown lfd esi) ∧
  l0_rely w ∧ fds_lt w ∧ l0owne lfd w es ∧ okeys es.p.b ∧ RI es ∧ pown lfd es'.p ⇒
  gstep es es' R ∧ RI es'
Proof
  strip_tac >>
  ‘∀i rs0 evs0 wi esi.
     i ≤ LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
     oown lfd esi’
    by (rpt strip_tac >> irule eown_oown >>
        qpat_x_assum ‘∀i rs0 evs0 wi esi. _ ⇒ eown lfd esi’ irule >>
        qexistsl [‘evs0’, ‘i’, ‘rs0’, ‘wi’] >> asm_rewrite_tac[]) >>
  drule_all eround_live >> strip_tac >>
  ‘∃rdy tevs. etail lfd pol hs (w1, es1) = SOME (rdy, (w', es'), log, tevs) ∧ R = aevs ++ tevs’
    by (qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >>
        qpat_x_assum ‘eacts _ _ _ _ = _’ (fn th => rewrite_tac[eround_def, th]) >>
        simp[AllCaseEqs(), PULL_EXISTS]) >>
  ‘∀i rs0 evs0 wi esi.
     i < LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
     eown lfd esi’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀i rs0 evs0 wi esi. _ ⇒ eown lfd esi’ irule >>
        qexistsl [‘evs0’, ‘i’, ‘rs0’, ‘wi’] >> asm_rewrite_tac[] >> simp[]) >>
  ‘eown lfd es1’
    by (qpat_x_assum ‘∀i rs0 evs0 wi esi. i ≤ _ ∧ _ ⇒ eown lfd esi’
          (qspecl_then [‘LENGTH acts’, ‘rs’, ‘aevs’, ‘w1’, ‘es1’] mp_tac) >>
        asm_rewrite_tac[TAKE_LENGTH_ID, LESS_EQ_REFL]) >>
  drule eacts_gone >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  drule eacts_l0 >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  ‘okeys es1.p.b’
    by (drule eacts_live >>
        impl_tac
        >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
            irule eown_oown >>
            qpat_x_assum ‘∀i rs0 evs0 wi esi. i < _ ∧ _ ⇒ eown lfd esi’ irule >>
            qexistsl [‘evs0’, ‘i’, ‘rs0’, ‘wi’] >> asm_rewrite_tac[]) >>
        strip_tac) >>
  ‘RI es’ by first_assum ACCEPT_TAC >>
  qpat_x_assum ‘RI es’ mp_tac >> rewrite_tac[RI_def] >> strip_tac >>
  ‘∀f. gok f es1.p.b’
    by (gen_tac >> qpat_x_assum ‘∀f. gok f es.p.b ⇒ gok f es1.p.b’ irule >> asm_rewrite_tac[]) >>
  ‘ALL_DISTINCT (MAP FST es1.p.stalls)’ by asm_rewrite_tac[] >>
  qpat_x_assum ‘etail _ _ _ _ = _’ mp_tac >> strip_tac >>
  drule etail_gone >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  ‘∀f. live es' f ∧ (outbox_of es'.p.b f ≠ [] ∨ MEM f es'.p.b.gone) ⇒
       ¬EXISTS (opens f) (aevs ++ tevs)’
    by (gen_tac >> disch_then (fn th => assume_tac (CONJUNCT1 th) >> assume_tac (CONJUNCT2 th)) >>
        rewrite_tac[EXISTS_APPEND] >>
        qpat_x_assum ‘∀f. (live es f ⇒ _) ∧ _’ (qspec_then ‘f’ strip_assume_tac) >>
        strip_tac
        >- (‘pendc es1 f’ by (qpat_x_assum ‘∀g. EXISTS (opens g) aevs ⇒ _’ irule >> asm_rewrite_tac[]) >>
            ‘MEM f (MAP SND es1.ctbl)’ by (irule pendc_ctbl >> first_assum ACCEPT_TAC) >>
            ‘¬live es1 f’ by (drule_all eown_ctbl_unlive >> rewrite_tac[]) >>
            ‘outbox_of es'.p.b f = [] ∧ ¬MEM f es'.p.b.gone’
              by (qpat_x_assum ‘live es' f ∧ _ ⇒ _’ irule >> asm_rewrite_tac[]) >>
            qpat_x_assum ‘outbox_of _ _ ≠ [] ∨ _’ mp_tac >> asm_rewrite_tac[]) >>
        ‘MEM (FConn f) log’ by (qpat_x_assum ‘∀g. EXISTS (opens g) tevs ⇒ _’ irule >> asm_rewrite_tac[]) >>
        ‘outbox_of es'.p.b f = [] ∧ ¬MEM f es'.p.b.gone’
          by (qpat_x_assum ‘live es' f ∧ _ ⇒ _’ irule >> asm_rewrite_tac[]) >>
        qpat_x_assum ‘outbox_of _ _ ≠ [] ∨ _’ mp_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum ‘RI es'’ mp_tac >> rewrite_tac[RI_def] >> strip_tac >>
  ‘RI es'’ by (rewrite_tac[RI_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[gstep_def] >> conj_tac
  >- (gen_tac >> strip_tac >> conj_tac
      >- (qpat_x_assum ‘∀f. live es' f ∧ _ ⇒ _’ irule >>
          qpat_x_assum ‘okeys es'.p.b’ mp_tac >> rewrite_tac[okeys_def] >>
          disch_then (qspec_then ‘f’ mp_tac) >> asm_rewrite_tac[live_def, held_def] >>
          strip_tac >> asm_rewrite_tac[]) >>
      qpat_x_assum ‘∀f. MEM f es'.p.b.gone ⇒ _ ∨ _’ (drule_then strip_assume_tac)
      >- (qpat_x_assum ‘∀f. MEM f es1.p.b.gone ⇒ _’ (drule_then strip_assume_tac) >>
          asm_rewrite_tac[EXISTS_APPEND])
      >- asm_rewrite_tac[EXISTS_APPEND] >>
      disj2_tac >> disj2_tac >>
      conj_tac >- (qexists_tac ‘n’ >> gvs[]) >>
      irule tstall_stalled >> asm_rewrite_tac[] >>
      ‘kp f es.p.b’
        by (qpat_x_assum ‘∀f c. MEM (f, c) es.p.stalls ∧ 0 < c ⇒ kp f es.p.b’ irule >>
            qexists_tac ‘n’ >> gvs[pf_sendwait_def]) >>
      qpat_x_assum ‘∀f. kp f es.p.b ⇒ _’ (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘∀f m. _ ⇒ tstall f tevs ∧ _’ (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  (conj_tac
   >- (qpat_x_assum ‘∀f. live es' f ∧ _ ⇒ _’ irule >>
       ‘kp f es'.p.b’ by (first_assum ACCEPT_TAC ORELSE qpat_x_assum ‘∀f c. MEM (f, c) es'.p.stalls ∧ 0 < c ⇒ kp f es'.p.b’ irule >>
                          qexists_tac ‘c’ >> asm_rewrite_tac[]) >>
       pop_assum mp_tac >> rewrite_tac[kp_def, live_def] >> strip_tac >> asm_rewrite_tac[])) >>
  Cases_on ‘c = 1’ >>
  TRY (disj1_tac >> asm_rewrite_tac[] >> irule tstall_stalled >> asm_rewrite_tac[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘¬(c = 1)’ mp_tac >> asm_rewrite_tac[] >> NO_TAC) >>
  disj2_tac >>
  ‘1 < c ∧ 0 < c − 1’ by (qpat_x_assum ‘0 < c’ mp_tac >> qpat_x_assum ‘¬(c = 1)’ mp_tac >> simp[]) >>
  ‘MEM (f, c − 1) es.p.stalls’
    by (qpat_x_assum ‘MEM (f, c − 1) es1.p.stalls’ mp_tac >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  irule tstall_stalled >> asm_rewrite_tac[] >>
  ‘kp f es.p.b’
    by (qpat_x_assum ‘∀f c. MEM (f, c) es.p.stalls ∧ 0 < c ⇒ kp f es.p.b’ irule >>
        qexists_tac ‘c − 1’ >> asm_rewrite_tac[]) >>
  qpat_x_assum ‘∀f. kp f es.p.b ⇒ _’ (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem RI_einit:
  RI einit
Proof
  simp[RI_def, einit_def, pinit_def, l1init_def, gok_def]
QED

Theorem ginv_einit:
  ginv tr einit
Proof
  simp[ginv_def, einit_def, pinit_def, l1init_def]
QED

Theorem erounds_ginv:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. SND (ecm lfd pol ifds m w0 n') + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    ginv (pre ++ evs) (SND ws) ∧ RI (SND ws)
Proof
  strip_tac >> Induct
  >- simp[erounds_def, ginv_einit, RI_einit] >>
  rpt gen_tac >> simp[erounds_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  rename1 ‘erounds _ _ _ _ _ n = SOME (h0, ws0, evs0, logs0)’ >>
  rename1 ‘eround _ _ _ _ _ = SOME (sn1, ws1, lg, rv1)’ >>
  qspecl_then [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘ARB’, ‘ARB’, ‘SUC n’] mp_tac
    (Q.GENL [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘a’, ‘calls’, ‘N’] l1ep_refines_ehl_upto_sent) >>
  impl_tac >- simp[] >> strip_tac >>
  first_assum (qspecl_then [‘n’, ‘h0’, ‘ws0’, ‘evs0’, ‘logs0’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  first_x_assum (qspecl_then [‘SUC n’, ‘h0 ++ [sn1]’, ‘ws1’, ‘evs0 ++ rv1’, ‘logs0 ++ [lg]’] mp_tac) >>
  impl_tac >- simp[erounds_def] >> strip_tac >>
  ‘eround_own lfd pol ifds m w0 n’
    by (qpat_x_assum ‘∀n'. n' < SUC n ⇒ eround_own _ _ _ _ _ n'’ irule >> simp[]) >>
  ‘okeys (SND ws0).p.b’
    by (qpat_x_assum ‘sent_inv _ _ (SND ws0) _’ mp_tac >> rewrite_tac[sent_inv_def] >>
        strip_tac) >>
  ‘pown lfd (SND ws1).p’
    by (qpat_x_assum ‘eown lfd (SND ws1)’ mp_tac >> rewrite_tac[eown_def] >> strip_tac) >>
  ‘∀i rs0 evs0 wi esi.
     i ≤ LENGTH (new_actions (log_of m) h0) ∧
     eacts lfd pol ws0 (TAKE i (new_actions (log_of m) h0)) = SOME (rs0, evs0, (wi, esi)) ⇒
     eown lfd esi’
    by (qpat_x_assum ‘eround_own _ _ _ _ _ n’ mp_tac >> rewrite_tac[eround_own_def] >>
        disch_then drule >> rewrite_tac[]) >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >>
  qpat_x_assum ‘RI (SND ws0)’ mp_tac >>
  qpat_x_assum ‘l0_rely (FST ws0)’ mp_tac >> qpat_x_assum ‘fds_lt (FST ws0)’ mp_tac >>
  qpat_x_assum ‘l0owne lfd (FST ws0) (SND ws0)’ mp_tac >>
  qpat_x_assum ‘okeys (SND ws0).p.b’ mp_tac >> qpat_x_assum ‘pown lfd (SND ws1).p’ mp_tac >>
  qpat_x_assum ‘∀i rs0 evs0 wi esi. _ ⇒ eown lfd esi’ mp_tac >>
  qpat_x_assum ‘ginv (pre ++ evs0) (SND ws0)’ mp_tac >>
  rpt (pop_assum kall_tac) >>
  PairCases_on ‘ws0’ >> PairCases_on ‘ws1’ >> rewrite_tac[FST, SND] >> rpt strip_tac >>
  drule_all eround_gone >> strip_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  ‘pre ++ evs0 ++ rv1 = (pre ++ evs0) ++ rv1’ by simp[] >>
  pop_assum SUBST1_TAC >> irule ginv_step >> qexists_tac ‘ws01’ >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* MAIN, generic: an fd gone at the end of n E1 rounds has every open
   episode excused, whatever came before the rounds *)
Theorem erounds_gone_excuse:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. SND (ecm lfd pol ifds m w0 n') + 1 < dimword (:64)) ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, E, logs) ∧
  MEM f (SND ws).p.b.gone ∧
  pos_open q (pre ++ E) ∧ pos_fd q (pre ++ E) = SOME f ⇒
  pos_hard_err q (fromList (pre ++ E)) ∨ pos_timed_out pf_sendwait q (fromList (pre ++ E))
Proof
  strip_tac >>
  ‘ginv (pre ++ E) (SND ws)’ by metis_tac[erounds_ginv] >>
  gvs[ginv_def, xc_def]
QED
