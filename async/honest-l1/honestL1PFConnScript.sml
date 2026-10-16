(*
  R1-live, the connection half (design/36 §6, live-conn under [F3]): a
  connection waiting in the listener's accept queue is eventually
  accepted by L1 (a Connect2 in psk) or dropped (it broke while pending:
  ECONNABORTED, or an EMFILE reset).

  L0 level first: a listener's accept queue grows only at the back (new
  connections), and only an accept on that listener takes from its front.
*)
Theory honestL1PFConn
Ancestors
  honestL1PFClient honestL1PFStream honestL1PFLive honestL1PFRound honestL1PFRefine
  honestL1PFModel honestL1Steps honestL1Inv honestL1Model honestL0WorldInv honestL0Rely
  honestL0World honestL0 asyncCore alist
Libs
  preamble

(* The accept queue of listener l *)
Definition qof_def:
  qof w l = case FILTER (λ(l', p, q). l' = l) w.listeners of
            | (_, _, q) :: _ => q
            | [] => []
End

Theorem FILTER_AFUPDKEY_other:
  ∀ls. k ≠ l ⇒
       FILTER (λ(l', p, q). l' = l) (AFUPDKEY k g ls) = FILTER (λ(l', p, q). l' = l) ls
Proof
  Induct >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem FILTER_AFUPDKEY_same:
  ∀ls. FILTER (λ(l', p, q). l' = l) ls = (l, p, q) :: t ⇒
       ∃t'. FILTER (λ(l', p, q). l' = l) (AFUPDKEY l g ls) = (l, g (p, q)) :: t'
Proof
  Induct >- simp[] >> simp[FORALL_PROD] >> rpt gen_tac >>
  rename1 ‘(a, b, c) :: ls’ >> simp[AFUPDKEY_def] >>
  Cases_on ‘a = l’ >> simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

(* Deliveries only append to a queue *)
Theorem qof_deliver:
  ∃t. qof (l0_deliver w a) l = qof w l ++ t
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >>
  TRY (qexists_tac ‘[]’ >> simp[qof_def, upd_lchan_def] >> NO_TAC) >>
  CASE_TAC >- (qexists_tac ‘[]’ >> simp[]) >>
  PairCases_on ‘h’ >> simp[] >>
  Cases_on ‘h0 = l’
  >- (pop_assum SUBST_ALL_TAC >>
      ‘MEM (l, h1, h2) w.listeners’
        by (‘MEM (l, h1, h2) (FILTER (λ(l,p',q). p' = n) w.listeners)’ by simp[] >>
            fs[MEM_FILTER]) >>
      Cases_on ‘FILTER (λ(l', p, q). l' = l) w.listeners’
      >- (fs[FILTER_EQ_NIL, EVERY_MEM] >> res_tac >> fs[]) >>
      PairCases_on ‘h’ >>
      ‘h0 = l’ by (‘MEM (h0, h1', h2') (FILTER (λ(l', p, q). l' = l) w.listeners)’
                    by simp[] >> fs[MEM_FILTER]) >>
      gvs[] >> drule FILTER_AFUPDKEY_same >>
      disch_then (qspec_then ‘λ(p, q). (p, q ++ [LENGTH w.chans])’ strip_assume_tac) >>
      simp[qof_def])
  >> qexists_tac ‘[]’ >> simp[qof_def, FILTER_AFUPDKEY_other]
QED

Theorem qof_simple[simp]:
  qof (w with hist := h) l = qof w l ∧ qof (w with clock := c) l = qof w l ∧
  qof (w with chans := cs) l = qof w l ∧ qof (w with open_fds := ofs) l = qof w l ∧
  qof (w with reserved := rs) l = qof w l ∧ qof (upd_lchan j g w) l = qof w l ∧
  qof (w with <| listeners := ls; open_fds := ofs |>) l = qof (w with listeners := ls) l
Proof
  simp[qof_def, upd_lchan_def]
QED

Theorem qof_tick:
  ∃t. qof (l0_tick nm w) l = qof w l ++ t
Proof
  simp[l0_tick_def] >>
  ‘∀as w'. ∃t. qof (FOLDL l0_deliver w' as) l = qof w' l ++ t’
    by (Induct >- simp[] >> rpt gen_tac >> simp[] >>
        qspecl_then [‘w'’, ‘h’] strip_assume_tac (Q.GENL [‘w’, ‘a’] qof_deliver) >>
        first_x_assum (qspec_then ‘l0_deliver w' h’ strip_assume_tac) >> simp[]) >>
  first_x_assum (qspecl_then [‘w.env w.clock w.hist nm’, ‘w with clock := w.clock + 1’]
                  strip_assume_tac) >> gvs[] >> metis_tac[]
QED

Theorem qof_ticks:
  ∀k w. ∃t. qof (l0_ticks nm k w) l = qof w l ++ t
Proof
  Induct >- simp[l0_ticks_def] >> rpt gen_tac >> simp[l0_ticks_def] >>
  qspecl_then [‘w’] strip_assume_tac (Q.GEN ‘w’ qof_tick) >>
  first_x_assum (qspec_then ‘l0_tick nm w’ strip_assume_tac) >> simp[]
QED

Theorem qof_FOLDL_upd[simp]:
  ∀q w. qof (FOLDL (λw j. upd_lchan j g w) w q) l = qof w l
Proof
  Induct >> simp[]
QED

Theorem qof_ops:
  (l0_listen p w = (x, w') ⇒ qof w' l = qof w l) ∧
  (l0_send g bs w = (r, w') ⇒ qof w' l = qof w l) ∧
  (l0_recv g n w = (r, d, w') ⇒ qof w' l = qof w l) ∧
  (l0_shutdown g w = (r, w') ⇒ qof w' l = qof w l) ∧
  (l0_connerr g w = (y, w') ⇒ qof w' l = qof w l) ∧
  (g ≠ l ∧ l0_close g w = (r, w') ⇒ qof w' l = qof w l) ∧
  (g ≠ l ∧ l0_accept g w = (r, w') ⇒ qof w' l = qof w l)
Proof
  rpt conj_tac >> strip_tac
  >- (gvs[l0_listen_def, AllCaseEqs()] >> simp[qof_def, FILTER_APPEND] >>
      Cases_on ‘FILTER (λ(l',p,q). l' = l) w.listeners’ >> simp[] >>
      TRY (PairCases_on ‘h’ >> simp[]) >> rw[])
  >- (gvs[l0_send_def, AllCaseEqs()])
  >- (gvs[l0_recv_def, AllCaseEqs()])
  >- (gvs[l0_shutdown_def, AllCaseEqs()])
  >- (gvs[l0_connerr_def, AllCaseEqs()])
  >- (gvs[l0_close_def, close_fd_def, AllCaseEqs()] >>
      simp[qof_def] >>
      ‘FILTER (λ(l',p,q). l' = l) (FILTER (λ(l,p,q). l ≠ g) w.listeners) =
       FILTER (λ(l',p,q). l' = l) w.listeners’
        by (qspec_tac (‘w.listeners’, ‘ls’) >> Induct >> simp[FORALL_PROD] >>
            rw[] >> gvs[]) >>
      simp[])
  >> gvs[l0_accept_def, AllCaseEqs()] >> simp[qof_def, FILTER_AFUPDKEY_other]
QED

(* An accept on the listener: the queue is unchanged, or its head is popped
   and either accepted (opened under the new fd) or dropped (it is broken) *)
Theorem accept_queue:
  l0_accept l w = (r, w') ⇒
  (qof w' l = qof w l ∧ ∀k. r ≠ Ok k) ∨
  ∃j q'. qof w l = j :: q' ∧ qof w' l = q' ∧
         ((∃k. r = Ok (w2n k) ∧ ALOOKUP w'.open_fds k = SOME j) ∨
          ((∀k. r ≠ Ok k) ∧ (j < LENGTH w.chans ⇒ (EL j w'.chans).broken)))
Proof
  rw[l0_accept_def] >>
  Cases_on ‘FILTER (λ(l',p,q). l' = l) w.listeners’ >> gvs[fail_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  ‘h0 = l’ by (‘MEM (h0, h1, h2) (FILTER (λ(l',p,q). l' = l) w.listeners)’ by simp[] >>
               fs[MEM_FILTER]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘∀g. qof (w with listeners := AFUPDKEY l (K (h1, g)) w.listeners) l = g’
    by (gen_tac >> drule FILTER_AFUPDKEY_same >>
        disch_then (qspec_then ‘K (h1, g)’ strip_assume_tac) >> simp[qof_def]) >>
  ‘qof w l = h2’ by simp[qof_def] >>
  gvs[AllCaseEqs(), l0_alloc_def, fail_def] >>
  simp[upd_lchan_def, EL_LUPDATE, break_lchan_def] >> rw[] >> gvs[]
QED

(* An L0 call that is neither an accept nor a close on l only appends to
   l's queue *)
Theorem qof_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_connect» ∧
  ¬((n = «sys_accept» ∨ n = «sys_close») ∧ bytes_fd conf = l) ⇒
  ∃t. qof w' l = qof w l ++ t
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac qof_ops >> gvs[] >>
  TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC) >>
  metis_tac[qof_ticks]
QED

(* An accept on l *)
Theorem qof_call_accept:
  l0_call «sys_accept» conf bytes w = SOME (FFIreturn bytes' w') ∧ bytes_fd conf = l ⇒
  ∃r. l0_accept l w = (r, w') ∧ bytes' = enc_res r
Proof
  rw[l0_call_def] >> pairarg_tac >> gvs[]
QED

Theorem qof_do:
  n ≠ «sys_connect» ∧ ¬((n = «sys_accept» ∨ n = «sys_close») ∧ bytes_fd conf = l) ∧
  l0_do n conf alen w = SOME (out, w', ev) ⇒
  ∃t. qof w' l = qof w l ++ t
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qspecl_then [‘w’] strip_assume_tac (Q.GEN ‘w’ (Q.SPECL [‘l’, ‘n’] (Q.GENL [‘l’, ‘nm’] qof_tick))) >>
  drule qof_call >> simp[] >> disch_then (qspec_then ‘l’ mp_tac) >> simp[] >>
  strip_tac >> simp[]
QED

Theorem accept_chans_len:
  l0_accept l w = (r, w') ⇒ LENGTH w'.chans = LENGTH w.chans
Proof
  rw[l0_accept_def, AllCaseEqs()] >> simp[upd_lchan_def]
QED

Theorem qof_lt:
  l0wf w ∧ MEM j (qof w l) ⇒ j < LENGTH w.chans
Proof
  rw[qof_def] >>
  Cases_on ‘FILTER (λ(l', p, q). l' = l) w.listeners’ >> gvs[] >>
  PairCases_on ‘h’ >> gvs[] >> rename1 ‘(l', p, q) :: _’ >>
  ‘MEM (l', p, q) w.listeners’
    by (‘MEM (l', p, q) (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
        fs[MEM_FILTER]) >>
  gvs[l0wf_def, used_chans_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  first_x_assum irule >> disj2_tac >> qexists_tac ‘(l', p, q)’ >> simp[]
QED

(* L1's accept on the listener l *)
Theorem sys_accept_queue:
  winv w ∧ sys_accept l w = SOME (out, w', ev) ⇒
  ∃t. (qof w' l = qof w l ++ t ∧ ∀k. l0_res_of out ≠ Ok k) ∨
      ∃j q'. qof w l ++ t = j :: q' ∧ qof w' l = q' ∧
             ((∃k. l0_res_of out = Ok k ∧ ALOOKUP w'.open_fds (n2w k) = SOME j) ∨
              ((∀k. l0_res_of out ≠ Ok k) ∧
               j < LENGTH w'.chans ∧ (EL j w'.chans).broken))
Proof
  rw[sys_accept_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  drule qof_call_accept >> simp[] >> strip_tac >> gvs[] >>
  qspecl_then [‘w’] strip_assume_tac (Q.GEN ‘w’ (Q.SPECL [‘l’, ‘«sys_accept»’] (Q.GENL [‘l’, ‘nm’] qof_tick))) >>
  ‘l0_rely (l0_tick «sys_accept» w)’
    by (gvs[winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_all l0_accept_res >> strip_tac >>
  ‘l0_res_of (enc_res r) = r’ by (irule l0_res_of_enc >> simp[]) >>
  drule accept_chans_len >> strip_tac >>
  ‘l0wf (l0_tick «sys_accept» w)’ by gvs[winv_def, l0wf_tick] >>
  drule accept_queue >> strip_tac >> qexists_tac ‘t’ >> gvs[] >>
  ‘j < LENGTH (l0_tick «sys_accept» w).chans’
    by (‘MEM j (qof (l0_tick «sys_accept» w) l)’
          by (qpat_x_assum ‘qof (l0_tick _ _) _ = _’ SUBST1_TAC >>
              qpat_x_assum ‘_ :: _ = _’ (SUBST1_TAC o SYM) >> simp[]) >>
        metis_tac[qof_lt]) >>
  disj2_tac >> qexists_tac ‘j’ >> gvs[] >>
  TRY (qexists_tac ‘w2n k’ >> simp[] >> NO_TAC)
QED

(* ------------------------------------------------------------------------
   L1's round and the listener's queue: only the fetch's accepts take from
   it (L1 never closes the listener)
   ------------------------------------------------------------------------ *)

Theorem sys_qof:
  (sys_send g bs w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t) ∧
  (g ≠ l ∧ sys_close g w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t) ∧
  (sys_recv g k w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t) ∧
  (g ≠ l ∧ sys_accept g w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t) ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t)
Proof
  rw[sys_close_def, sys_send_def, sys_recv_def, sys_accept_def, sys_poll_def] >>
  drule_at (Pos last) qof_do >> simp[]
QED

Theorem l1_close_qof:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ g ≠ l ⇒ ∃t. qof w' l = qof w l ++ t
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_qof]
QED

Theorem pdo_qof:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ⇒
  ∃t. qof w' lfd = qof w lfd ++ t
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC) >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY (rename1 ‘l1_close g _ = _’ >>
       ‘g ≠ lfd’ by (imp_res_tac ALOOKUP_MEM >> gvs[pown_def, MEM_MAP] >>
                     strip_tac >> gvs[] >> metis_tac[SND]) >>
       drule_all l1_close_qof >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >> TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC) >>
  metis_tac[sys_qof]
QED

Theorem pacts_qof:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ pv_rel lfd cm ps s ∧ pown lfd ps ⇒
    ∃t. qof w' lfd = qof w lfd ++ t
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all pdo_qof >> strip_tac >>
  drule_all pdo_hdo >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem l1_polls_qof:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒ ∃t. qof w' l = qof w l ++ t
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule (el 5 (CONJUNCTS sys_qof)) >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem l1_flush_qof:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒
                       ∃t. qof w' l = qof w l ++ t
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >>
  drule (el 1 (CONJUNCTS sys_qof)) >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem l1_reap_qof:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ ¬MEM l fs ⇒
                       ∃t. qof w' l = qof w l ++ t
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >>
      ‘h ≠ l’ by (strip_tac >> gvs[]) >>
      drule_all l1_close_qof >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

(* ------------------------------------------------------------------------
   The fetch and the listener's queue
   ------------------------------------------------------------------------ *)

(* Open fds stay open, channels are only added, and a broken channel stays
   broken *)
Definition wmono_def:
  wmono w w' ⇔
    (∀g j. ALOOKUP w.open_fds g = SOME j ⇒ ALOOKUP w'.open_fds g = SOME j) ∧
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀j. j < LENGTH w.chans ∧ (EL j w.chans).broken ⇒ (EL j w'.chans).broken)
End

Theorem wmono_refl[simp]:
  wmono w w
Proof
  simp[wmono_def]
QED

Theorem wmono_trans:
  wmono w1 w2 ∧ wmono w2 w3 ⇒ wmono w1 w3
Proof
  rw[wmono_def] >> res_tac >> gvs[] >>
  first_x_assum irule >> simp[] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem wmono_upd:
  ((EL j w.chans).broken ⇒ (g (EL j w.chans)).broken) ⇒ wmono w (upd_lchan j g w)
Proof
  rw[wmono_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem wmono_deliver:
  wmono w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >>
  TRY (irule wmono_upd >> rw[break_lchan_def] >> NO_TAC) >>
  every_case_tac >> simp[wmono_def, EL_APPEND1]
QED

Theorem wmono_tick:
  wmono w (l0_tick nm w)
Proof
  rw[l0_tick_def] >>
  ‘∀as w'. wmono w' (FOLDL l0_deliver w' as)’
    by (Induct >> rw[] >> metis_tac[wmono_trans, wmono_deliver]) >>
  irule wmono_trans >> qexists_tac ‘w with clock := w.clock + 1’ >>
  simp[] >> simp[wmono_def]
QED

Theorem wmono_ticks:
  ∀k w. wmono w (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[wmono_trans, wmono_tick]
QED

Theorem wmono_accept:
  fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧ l0_accept l w = (r, w') ⇒ wmono w w'
Proof
  rw[l0_accept_def] >> gvs[AllCaseEqs(), fail_def] >>
  TRY (irule wmono_upd >> simp[break_lchan_def] >> rw[] >> NO_TAC) >>
  TRY (simp[wmono_def] >> NO_TAC) >>
  TRY (simp[wmono_def, upd_lchan_def, EL_LUPDATE, break_lchan_def] >> rw[] >> NO_TAC) >>
  gvs[l0_alloc_def] >>
  ‘¬MEM (lowest_fd w) (l0_used w)’
    by (irule lowest_fd_free_lim >> gvs[fds_lt_def]) >>
  rw[wmono_def] >> rw[] >> gvs[l0_used_def] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem wmono_recv:
  l0_recv f n w = (r, d, w') ⇒ wmono w w'
Proof
  rw[l0_recv_def] >> gvs[AllCaseEqs()] >>
  TRY (irule wmono_upd >> simp[] >> NO_TAC) >> simp[]
QED

Theorem wmono_hist[simp]:
  wmono w (w' with hist := h) ⇔ wmono w w'
Proof
  simp[wmono_def]
QED

Theorem sys_wmono:
  (winv w ∧ sys_accept g w = SOME (out, w', ev) ⇒ wmono w w') ∧
  (sys_recv g k w = SOME (out, w', ev) ⇒ wmono w w')
Proof
  rw[sys_accept_def, sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  gvs[l0_call_def] >> pairarg_tac >> gvs[]
  >- (‘fds_lt (l0_tick «sys_accept» w) ∧ l0_rely (l0_tick «sys_accept» w)’
        by (gvs[winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
      drule_at (Pos last) wmono_accept >> gvs[l0_rely_def] >> strip_tac >>
      metis_tac[wmono_trans, wmono_tick])
  >> drule wmono_recv >> metis_tac[wmono_trans, wmono_tick]
QED

(* A queued channel is resolved: accepted under an fd the log names, or
   broken *)
Definition resolved_def:
  resolved w log j ⇔
    (∃g. MEM (FConn g) log ∧ ALOOKUP w.open_fds g = SOME j) ∨
    (j < LENGTH w.chans ∧ (EL j w.chans).broken)
End

Theorem resolved_mono:
  resolved w log j ∧ wmono w w' ∧ (∀x. MEM x log ⇒ MEM x log') ⇒ resolved w' log' j
Proof
  rw[resolved_def, wmono_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

(* The queue after a step that only appended, then the rest of the fetch *)
Theorem queue_app:
  qof w1 l = qof w l ++ t1 ∧ wmono w1 w' ∧ log_conns lg = [] ∧
  k ≤ LENGTH t2 + LENGTH (qof w1 l) ∧ qw = DROP k (qof w1 l ++ t2) ∧
  (∀j. MEM j (TAKE k (qof w1 l ++ t2)) ⇒ resolved w' log j) ∧
  LENGTH (log_conns log) ≤ k ∧ LENGTH (log_conns lg) ≤ 1 ⇒
  ∃t k. k ≤ LENGTH t + LENGTH (qof w l) ∧ qw = DROP k (qof w l ++ t) ∧
        (∀j. MEM j (TAKE k (qof w l ++ t)) ⇒ resolved w' (lg ++ log) j) ∧
        LENGTH (log_conns lg) + LENGTH (log_conns log) ≤ k
Proof
  rw[] >> qexistsl_tac [‘t1 ++ t2’, ‘k’] >> gvs[] >> rw[] >>
  irule resolved_mono >> qexistsl_tac [‘log’, ‘w'’] >> simp[]
QED

(* The queue after a step that popped its head j (resolved by then) *)
Theorem queue_pop:
  qof w l ++ t1 = j :: qof w1 l ∧ resolved w1 lg j ∧ wmono w1 w' ∧
  k ≤ LENGTH t2 + LENGTH (qof w1 l) ∧ qw = DROP k (qof w1 l ++ t2) ∧
  (∀j. MEM j (TAKE k (qof w1 l ++ t2)) ⇒ resolved w' log j) ∧
  LENGTH (log_conns log) ≤ k ∧ LENGTH (log_conns lg) ≤ 1 ⇒
  ∃t k. k ≤ LENGTH t + LENGTH (qof w l) ∧ qw = DROP k (qof w l ++ t) ∧
        (∀j. MEM j (TAKE k (qof w l ++ t)) ⇒ resolved w' (lg ++ log) j) ∧
        LENGTH (log_conns lg) + LENGTH (log_conns log) ≤ k
Proof
  rw[] >> qexistsl_tac [‘t1 ++ t2’, ‘SUC k’] >>
  ‘qof w l ++ (t1 ++ t2) = j :: (qof w1 l ++ t2)’
    by metis_tac[APPEND_ASSOC, APPEND] >>
  simp[] >> rw[] >>
  TRY (irule resolved_mono >> qexistsl_tac [‘lg’, ‘w1’] >> simp[] >> NO_TAC) >>
  TRY (irule resolved_mono >> qexistsl_tac [‘log’, ‘w'’] >> simp[] >> NO_TAC) >>
  ‘LENGTH (qof w l ++ t1) = SUC (LENGTH (qof w1 l))’ by metis_tac[LENGTH] >>
  gvs[]
QED

(* The fetch: the listener's queue loses a prefix of (the old queue plus
   arrivals), each popped channel accepted (FConn in the log) or broken *)
Theorem pf_fetch_queue:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ⇒
    wmono w w' ∧
    ∃t k. k ≤ LENGTH t + LENGTH (qof w lfd) ∧ qof w' lfd = DROP k (qof w lfd ++ t) ∧
          (∀j. MEM j (TAKE k (qof w lfd ++ t)) ⇒ resolved w' log j) ∧
          LENGTH (log_conns log) ≤ k
Proof
  Induct >- (simp[pf_fetch_def] >> rpt strip_tac >> qexistsl_tac [‘[]’, ‘0’] >> simp[]) >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> gvs[] >>
      qpat_x_assum ‘option_CASE (pf_fetch _ _ _ _) _ _ = _’
        (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
      ‘winv w1 ∧ wmono w w1’ by metis_tac[sys_winv, sys_wmono] >>
      first_x_assum drule_all >> strip_tac >>
      ‘wmono w w'’ by metis_tac[wmono_trans] >>
  qpat_x_assum ‘wmono w w'’ (fn th => REWRITE_TAC [th]) >>
      drule_all sys_accept_queue >> strip_tac
      >- (‘fl' = []’ by (Cases_on ‘l0_res_of out’ >> gvs[]) >>
          irule queue_app >> simp[] >> metis_tac[])
      >- (irule queue_pop >> gvs[] >>
          qexistsl_tac [‘j’, ‘k’, ‘t'’, ‘t’, ‘w1’] >> gvs[] >>
          simp[resolved_def] >> disj1_tac >> qexists_tac ‘n2w k'’ >> gvs[])
      >> ‘fl' = []’ by (Cases_on ‘l0_res_of out’ >> gvs[]) >>
      irule queue_pop >> gvs[] >>
      qexistsl_tac [‘j’, ‘k’, ‘t'’, ‘t’, ‘w1’] >> gvs[] >>
      simp[resolved_def])
  >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum ‘option_CASE (pf_fetch _ _ _ _) _ _ = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
  ‘winv w1 ∧ wmono w w1’ by metis_tac[sys_winv, sys_wmono] >>
  first_x_assum drule_all >> strip_tac >>
  ‘wmono w w'’ by metis_tac[wmono_trans] >>
  qpat_x_assum ‘wmono w w'’ (fn th => REWRITE_TAC [th]) >>
  drule (el 3 (CONJUNCTS sys_qof)) >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  ‘log_conns fl' = []’ by (Cases_on ‘l0_res_of out’ >> gvs[] >> every_case_tac >> gvs[]) >>
  irule queue_app >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The round and the listener's queue
   ------------------------------------------------------------------------ *)

(* As wmono, except for the fds X (closed) *)
Definition wkeep_def:
  wkeep X w w' ⇔
    (∀g j. ¬MEM g X ∧ ALOOKUP w.open_fds g = SOME j ⇒ ALOOKUP w'.open_fds g = SOME j) ∧
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀j. j < LENGTH w.chans ∧ (EL j w.chans).broken ⇒ (EL j w'.chans).broken)
End

Theorem wmono_wkeep:
  wmono w w' ⇒ wkeep X w w'
Proof
  simp[wmono_def, wkeep_def]
QED

Theorem wkeep_trans:
  wkeep X w1 w2 ∧ wkeep Y w2 w3 ⇒ wkeep (X ++ Y) w1 w3
Proof
  rw[wkeep_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem wkeep_hist[simp]:
  wkeep X w (w' with hist := h) ⇔ wkeep X w w'
Proof
  simp[wkeep_def]
QED

Theorem FOLDL_break_chans:
  ∀e q w. let w' = FOLDL (λw j. w with chans := LUPDATE (break_lchan e F (EL j w.chans)) j w.chans)
                   w q in
        LENGTH w'.chans = LENGTH w.chans ∧ w'.open_fds = w.open_fds ∧
        ∀j. j < LENGTH w.chans ∧ (EL j w.chans).broken ⇒ (EL j w'.chans).broken
Proof
  gen_tac >> Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘w with chans := LUPDATE (break_lchan e F (EL h w.chans)) h w.chans’
                   mp_tac) >>
  simp[] >> rw[] >> first_x_assum irule >>
  simp[EL_LUPDATE] >> rw[break_lchan_def]
QED

Theorem wkeep_close:
  l0_close g w = (r, w') ⇒ wkeep [g] w w'
Proof
  rw[l0_close_def, AllCaseEqs()] >> simp[wkeep_def] >>
  TRY (rw[close_fd_def] >> NO_TAC) >>
  simp[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (PURE_REWRITE_TAC [upd_lchan_def] >>
       qmatch_goalsub_abbrev_tac ‘FOLDL _ w1 qq’ >>
       qspecl_then [‘E_CONNRESET’, ‘qq’, ‘w1’] mp_tac FOLDL_break_chans >>
       simp[Abbr ‘w1’] >> NO_TAC) >>
  simp[upd_lchan_def, EL_LUPDATE, ALOOKUP_ADELKEY] >> rw[] >> gvs[]
QED

Theorem sys_close_wkeep:
  sys_close g w = SOME (out, w', ev) ⇒ wkeep [g] w w'
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[l0_call_def] >>
  pairarg_tac >> gvs[] >>
  ‘[g] = [] ++ [g]’ by simp[] >> pop_assum SUBST1_TAC >>
  irule wkeep_trans >> qexists_tac ‘l0_tick «sys_close» w’ >>
  simp[wmono_wkeep, wmono_tick] >>
  gvs[] >> metis_tac[wkeep_close]
QED

Theorem l1_reap_wkeep:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ wkeep fs w w'
Proof
  Induct >> simp[l1_reap_def] >- simp[wkeep_def] >>
  rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs(), l1_close_def] >>
      first_x_assum drule >> strip_tac >> drule sys_close_wkeep >> strip_tac >>
      ‘h :: fs = [h] ++ fs’ by simp[] >> pop_assum SUBST1_TAC >>
      metis_tac[wkeep_trans]) >>
  first_x_assum drule >> rw[wkeep_def] >> metis_tac[]
QED

Theorem resolved_keep:
  resolved w log j ∧ wkeep X w w' ∧ (∀g. MEM (FConn g) log ⇒ ¬MEM g X) ⇒
  resolved w' log j
Proof
  rw[resolved_def, wkeep_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem pf_fetch_closing:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ ps'.b.closing = ps.b.closing
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> rw[] >> gvs[AllCaseEqs()] >> rw[] >> gvs[set_inb_def]
QED

(* A round: the listener's queue loses a prefix of (the old queue plus
   arrivals), each popped channel accepted under an fd the round's fetch
   log names (FConn), or broken *)
Theorem pround_queue:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ pv_rel lfd cm ps s ∧ pown lfd ps ∧ l0own lfd w ps ⇒
  ∃t k. k ≤ LENGTH t + LENGTH (qof w lfd) ∧ qof w' lfd = DROP k (qof w lfd ++ t) ∧
        (∀j. MEM j (TAKE k (qof w lfd ++ t)) ⇒ resolved w' log j) ∧
        LENGTH (log_conns log) ≤ k
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule_all pacts_qof >> disch_then (qx_choose_then ‘t1’ assume_tac) >>
  drule_all pacts_hacts >> strip_tac >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[winv_def] >>
  drule_all pacts_l0 >> strip_tac >>
  drule_all pacts_winv >> strip_tac >>
  rename1 ‘l1_polls _ wa = SOME (rv, w1, pevs)’ >>
  drule l1_polls_qof >> disch_then (qspec_then ‘lfd’ (qx_choose_then ‘t2’ assume_tac)) >>
  drule_all l1_polls_winv >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >>
  rename1 ‘l1_flush _ (w1, pa.b) = SOME ((w2, b2), fevs)’ >>
  drule l1_flush_qof >> disch_then (qspec_then ‘lfd’ (qx_choose_then ‘t3’ assume_tac)) >>
  drule_all l1_flush_winv >> strip_tac >>
  ‘l0_rely w1’ by gvs[winv_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3), log, gevs)’ >>
  drule_all pf_fetch_queue >> strip_tac >>
  drule pf_fetch_closing >> strip_tac >>
  drule_all pf_fetch_winv >> strip_tac >>
  ‘∀g. MEM (FConn g) log ⇒ ¬MEM g ps3.b.closing’
    by (rpt strip_tac >>
        ‘MEM g (l0_used w2)’ by gvs[l0own_def] >>
        drule_all pf_fetch_conns >>
        simp[log_conns_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        qexists_tac ‘FConn g’ >> simp[]) >>
  rename1 ‘l1_reap _ (w3, ps3.b) = SOME ((w4, b4), cevs)’ >>
  ‘¬MEM lfd ps3.b.closing’ by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  drule_all l1_reap_qof >> disch_then (qx_choose_then ‘t5’ assume_tac) >>
  drule l1_reap_wkeep >> strip_tac >>
  qexistsl_tac [‘t1 ++ t2 ++ t3 ++ t ++ t5’, ‘k’] >> gvs[] >>
  ‘k ≤ LENGTH (qof w lfd ++ t1 ++ t2 ++ t3 ++ t)’ by simp[] >>
  simp[DROP_APPEND1, TAKE_APPEND1] >>
  rpt strip_tac >> irule resolved_keep >> simp[] >>
  qexistsl_tac [‘ps3.b.closing’, ‘w3’] >> simp[]
QED

(* ------------------------------------------------------------------------
   The fetch and the listener: accepts, the pause, the accepted fds
   ------------------------------------------------------------------------ *)

(* Event ev's result is a failure *)
Definition failed_def:
  failed (IO_event n conf bs) ⇔ ∃e x. l0_res_of (MAP SND bs) = Fail e x
End

Theorem ev_failed:
  l0_rely w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒
  (failed ev ⇔ ∃e x. l0_res_of out = Fail e x)
Proof
  strip_tac >>
  ‘LENGTH out = alen’
    by (gvs[l0_do_def, AllCaseEqs()] >> drule_all honestL0WorldPropsTheory.l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[failed_def, MAP_SND_ZIP_REPLICATE]
QED

Theorem pf_fetch_lfd:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ⇒
    ps'.acq = ps.acq ++ log_conns log ∧
    (0 < ps.pause ⇒ ps'.pause = ps.pause ∧ ¬EXISTS (ev_on «sys_accept» lfd) evs) ∧
    (MEM lfd fs ∧ wants_input lfd hw ps lfd ⇒ EXISTS (ev_on «sys_accept» lfd) evs) ∧
    (∀ev. MEM ev evs ∧ ev_on «sys_accept» lfd ev ∧ ¬failed ev ⇒ log_conns log ≠ [])
Proof
  Induct >- simp[pf_fetch_def, log_conns_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule_all >> strip_tac >> simp[] >>
      rpt strip_tac >> gvs[] >> gvs[wants_input_def] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (gvs[] >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> gvs[AllCaseEqs()] >>
      ‘winv w1’ by metis_tac[sys_winv] >>
      first_x_assum drule_all >> strip_tac >>
      ‘l0_rely w’ by gvs[winv_def] >>
      qpat_assum ‘sys_accept _ _ = _’ (strip_assume_tac o REWRITE_RULE [sys_accept_def]) >>
      drule_all ev_do >> drule_all ev_failed >> rpt strip_tac >>
      ‘ev_on «sys_accept» g ev’ by simp[call_fds_def] >>
      ‘ps.pause = 0’ by gvs[wants_input_def] >>
      Cases_on ‘l0_res_of out’ >> gvs[log_conns_def] >> rw[] >> gvs[EXISTS_MEM] >>
      metis_tac[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  ‘l0_rely w’ by gvs[winv_def] >>
  qpat_assum ‘sys_recv _ _ _ = _’ (strip_assume_tac o REWRITE_RULE [sys_recv_def]) >>
  drule_all ev_do >> strip_tac >>
  ‘¬ev_on «sys_accept» lfd ev’ by simp[] >>
  first_x_assum drule_all >> strip_tac >> gvs[log_conns_def, wants_input_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The listener stays a listener, and is no connection's fd
   ------------------------------------------------------------------------ *)

Definition linv_def:
  linv l w ⇔ MEM l (MAP FST w.listeners) ∧ ALOOKUP w.open_fds l = NONE
End

Theorem MAP_FST_AFUPDKEY[simp]:
  ∀ls. MAP FST (AFUPDKEY k g ls) = MAP FST ls
Proof
  Induct >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[]
QED

Theorem linv_simple[simp]:
  (linv l (w with hist := h) ⇔ linv l w) ∧ (linv l (w with clock := c) ⇔ linv l w) ∧
  (linv l (w with chans := cs) ⇔ linv l w) ∧ (linv l (upd_lchan j g w) ⇔ linv l w)
Proof
  simp[linv_def, upd_lchan_def]
QED

Theorem linv_deliver:
  linv l w ⇒ linv l (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[linv_def]
QED

Theorem linv_tick:
  linv l w ⇒ linv l (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. linv l w ⇒ linv l (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[linv_deliver]) >>
  rw[] >> first_x_assum irule >> simp[]
QED

Theorem linv_ticks:
  ∀k w. linv l w ⇒ linv l (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[linv_tick]
QED

Theorem FOLDL_break_fields:
  ∀q w. (FOLDL (λw j. w with chans := LUPDATE (break_lchan e F (EL j w.chans)) j w.chans)
           w q).listeners = w.listeners ∧
        (FOLDL (λw j. w with chans := LUPDATE (break_lchan e F (EL j w.chans)) j w.chans)
           w q).open_fds = w.open_fds
Proof
  Induct >> simp[]
QED

Theorem linv_ops:
  (linv l w ∧ l0_listen p w = (x, w') ⇒ linv l w') ∧
  (linv l w ∧ l0_send g bs w = (r, w') ⇒ linv l w') ∧
  (linv l w ∧ l0_recv g n w = (r, d, w') ⇒ linv l w') ∧
  (linv l w ∧ l0_shutdown g w = (r, w') ⇒ linv l w') ∧
  (linv l w ∧ l0_connerr g w = (y, w') ⇒ linv l w') ∧
  (linv l w ∧ g ≠ l ∧ l0_close g w = (r, w') ⇒ linv l w') ∧
  (linv l w ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧ l0_accept g w = (r, w') ⇒ linv l w')
Proof
  rpt conj_tac >> strip_tac
  >- gvs[l0_listen_def, AllCaseEqs(), linv_def]
  >- gvs[l0_send_def, AllCaseEqs()]
  >- gvs[l0_recv_def, AllCaseEqs()]
  >- gvs[l0_shutdown_def, AllCaseEqs()]
  >- gvs[l0_connerr_def, AllCaseEqs()]
  >- (gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >>
      gvs[linv_def, ALOOKUP_ADELKEY, upd_lchan_def, FOLDL_break_fields] >>
      gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[])
  >> gvs[l0_accept_def, AllCaseEqs(), fail_def, linv_def, l0_alloc_def] >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free_lim >> gvs[fds_lt_def]) >>
  gvs[l0_used_def] >> rw[] >> gvs[] >> strip_tac >> gvs[]
QED

Theorem linv_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_connect» ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = l) ∧ linv l w ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ⇒
  linv l w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac linv_ops >> gvs[] >>
  metis_tac[linv_ticks, linv_ops]
QED

Theorem linv_do:
  l0_do n conf alen w = SOME (out, w', ev) ∧ n ≠ «sys_connect» ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = l) ∧ linv l w ∧ winv w ⇒ linv l w'
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  drule linv_call >> simp[] >> disch_then irule >>
  gvs[winv_def, linv_tick, l0_rely_def]
QED

Theorem sys_linv:
  (linv l w ∧ winv w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ winv w ∧ g ≠ l ∧ sys_close g w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ winv w ∧ sys_recv g k w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ winv w ∧ sys_accept g w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ winv w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ linv l w')
Proof
  rw[sys_close_def, sys_send_def, sys_recv_def, sys_accept_def, sys_poll_def] >>
  drule_at (Pos (el 1)) linv_do >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll and the listener: a listener with a non-empty queue is
   readable
   ------------------------------------------------------------------------ *)

Theorem listen_revents_in:
  linv l w ∧ qof w l ≠ [] ∧ ODD ev ⇒ (byte_revents (fd_revents w (l, ev))).rin
Proof
  rw[linv_def, fd_revents_def, l0_chan_of_def, qof_def] >>
  every_case_tac >> gvs[byte_revents_revents_byte]
QED

Theorem qof_ne_ticks:
  qof w l ≠ [] ⇒ qof (l0_ticks nm k w) l ≠ [] ∧ qof (l0_tick nm w) l ≠ []
Proof
  strip_tac >> metis_tac[qof_ticks, qof_tick, APPEND_eq_NIL]
QED

Theorem sys_poll_l:
  sys_poll fes w = SOME (out, w', ev) ∧ winv w ∧ linv l w ∧ qof w l ≠ [] ∧
  EVERY (λ(g, e). e < 256 ∧ (g = l ⇒ ODD e)) fes ⇒
  winv w' ∧ linv l w' ∧ qof w' l ≠ [] ∧ ev_name ev = ExtCall «sys_poll» ∧
  (MEM l (MAP FST fes) ⇒ ev_on «sys_poll» l ev) ∧
  (ev_on «sys_poll» l ev ∧ ¬retried ev ⇒ MEM l (readable_fds (poll_revents fes out)))
Proof
  strip_tac >> ‘l0_rely w’ by gvs[winv_def] >>
  ‘EVERY (λ(g, e). e < 256) fes’
    by (qpat_x_assum ‘EVERY _ fes’ mp_tac >> match_mp_tac EVERY_MONOTONIC >>
        simp[FORALL_PROD]) >>
  drule_all call_fds_poll >> strip_tac >>
  ‘winv w' ∧ linv l w' ∧ ∃t. qof w' l = qof w l ++ t’
    by (rpt conj_tac
        >- metis_tac[sys_winv]
        >- metis_tac[sys_linv]
        >> metis_tac[sys_qof]) >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  drule_all ev_do >> strip_tac >>
  drule l0_do_cases >> strip_tac >> gvs[ev_name_def] >>
  rw[] >> gvs[] >>
  ‘poll_entries (DROP 1 (poll_conf fes)) = fes ∧ HD (poll_conf fes) = 0w’
    by simp[poll_conf_def, poll_entries_conf] >>
  qabbrev_tac ‘wt = l0_tick «sys_poll» w’ >>
  ‘linv l wt ∧ qof wt l ≠ [] ∧ LENGTH (wt.ch.errno_of wt.hist) = 4’
    by gvs[Abbr ‘wt’, linv_tick, qof_ne_ticks, l0_rely_def] >>
  ‘∀k. linv l (l0_ticks «sys_poll» k wt) ∧ qof (l0_ticks «sys_poll» k wt) l ≠ []’
    by simp[linv_ticks, qof_ne_ticks] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (gvs[res_of_fail] >> NO_TAC) >>
  gvs[MEM_MAP] >> rename1 ‘MEM y fes’ >> PairCases_on ‘y’ >> gvs[] >>
  ‘ODD y1’ by (qpat_x_assum ‘EVERY (λ(g, e). _ ∧ _) fes’ mp_tac >>
                simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  simp[poll_revents_def] >> CASE_TAC >> gvs[] >>
  simp[DROP_poll_out] >>
  qmatch_goalsub_abbrev_tac ‘MAP (fd_revents w1) fes’ >>
  ‘TAKE (LENGTH fes) (MAP (fd_revents w1) fes) = MAP (fd_revents w1) fes’
    by metis_tac[LENGTH_MAP, TAKE_LENGTH_ID] >>
  simp[MAP_MAP_o] >> irule readable_zip >> qexists_tac ‘y1’ >>
  simp[Abbr ‘w1’] >> irule listen_revents_in >> simp[]
QED

Theorem l1_polls_l:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ linv l w ∧ qof w l ≠ [] ∧
    (∀c. MEM c chs ⇒ EVERY (λ(g, e). e < 256 ∧ (g = l ⇒ ODD e)) c) ⇒
    winv w' ∧ linv l w' ∧ qof w' l ≠ [] ∧
    (∀c. MEM c chs ∧ MEM l (MAP FST c) ⇒ EXISTS (ev_on «sys_poll» l) evs) ∧
    (∀ev. MEM ev evs ∧ ev_on «sys_poll» l ev ∧ ¬retried ev ⇒ MEM l (readable_fds rv))
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all sys_poll_l >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[readable_fds_def, FILTER_APPEND] >> gvs[readable_fds_def] >>
  rw[] >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The round and the listener
   ------------------------------------------------------------------------ *)

Theorem l1_close_linv:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ g ≠ l ∧ linv l w ∧ winv w ⇒ linv l w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_linv]
QED

Theorem pdo_linv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ∧ linv lfd w ∧ winv w ⇒
  linv lfd w'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY (rename1 ‘l1_close g _ = _’ >>
       ‘g ≠ lfd’ by (imp_res_tac ALOOKUP_MEM >> gvs[pown_def, MEM_MAP] >>
                     strip_tac >> gvs[] >> metis_tac[SND]) >>
       drule_all l1_close_linv >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >> metis_tac[sys_linv]
QED

Theorem pacts_linv:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ pv_rel lfd cm ps s ∧
    pown lfd ps ∧ linv lfd w ∧ winv w ⇒
    linv lfd w'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all pdo_linv >> strip_tac >>
  drule_all pdo_winv >> strip_tac >>
  drule_all pdo_hdo >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* The actions: the pause is kept, accepted fds are only handed out (from
   the front), and an Accept with fds queued hands one out *)
Theorem pdo_lfd:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  ps'.pause = ps.pause ∧ ∃d. ps'.acq = DROP d ps.acq ∧ (a = Accept lfd ∧ ps.acq ≠ [] ⇒ 0 < d)
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[set_inb_def] >> gvs[l1do_def, AllCaseEqs()] >>
  TRY (qexists_tac ‘0’ >> simp[] >> NO_TAC) >>
  qexists_tac ‘1’ >> simp[]
QED

Theorem pacts_lfd:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    ps'.pause = ps.pause ∧
    ∃d. ps'.acq = DROP d ps.acq ∧ (MEM (Accept lfd) acts ∧ ps.acq ≠ [] ⇒ 0 < d)
Proof
  Induct >> simp[pacts_def] >- (rpt strip_tac >> qexists_tac ‘0’ >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule pdo_lfd >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  qexists_tac ‘d + d'’ >> simp[DROP_DROP_T] >> rw[] >> gvs[] >>
  Cases_on ‘d = 0’ >> gvs[] >>
  Cases_on ‘ps.acq’ >> gvs[]
QED

Theorem l1_polls_linv:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ linv l w ⇒
                    linv l w' ∧ EVERY (λev. ev_name ev = ExtCall «sys_poll») evs
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  ‘winv w1 ∧ linv l w1’ by metis_tac[sys_winv, sys_linv] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  gvs[sys_poll_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem l1_flush_linv:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ linv l w ⇒
                       linv l w' ∧ EVERY (λev. ev_name ev = ExtCall «sys_send») evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘winv w'' ∧ linv l w''’ by metis_tac[sys_winv, sys_linv] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  gvs[sys_send_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem pf_fetch_linv:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ linv l w ⇒ linv l w'
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum irule >> metis_tac[sys_winv, sys_linv]
QED

Theorem l1_reap_linv:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ ¬MEM l fs ∧
                       winv w ∧ linv l w ⇒ linv l w'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >>
      ‘h ≠ l’ by (strip_tac >> gvs[]) >>
      drule_all l1_close_linv >> strip_tac >>
      drule_all l1_close_winv >> strip_tac >>
      first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem pdo_names:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs ∧
  ps'.b.nxt ≤ ps.b.nxt + 1
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[set_inb_def] >>
  gvs[l1_close_def, l1do_def, AllCaseEqs(), forget_def, set_outbox_def] >>
  gvs[sys_close_def, sys_send_def] >>
  TRY (drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
  rw[after_send_def] >> every_case_tac >> simp[set_outbox_def]
QED

Theorem pacts_names:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs ∧
    ps'.b.nxt ≤ ps.b.nxt + LENGTH acts
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule pdo_names >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem l1hdl_not_lfd:
  l1hdln (w2n lfd) j < dimword (:64) ⇒ l1hdl lfd j ≠ lfd
Proof
  Cases_on ‘lfd’ >> simp[l1hdl_def, l1hdln_def] >> rw[] >> gvs[dimword_def, n2w_11]
QED

(* The listener's handle is no connection's handle *)
Theorem tbl_lfd:
  pown lfd ps ∧ l1hdln (w2n lfd) ps.b.nxt < dimword (:64) ⇒ ALOOKUP ps.b.tbl lfd = NONE
Proof
  rw[pown_def] >> Cases_on ‘ALOOKUP ps.b.tbl lfd’ >> simp[] >>
  first_x_assum drule >> strip_tac >>
  ‘l1hdln (w2n lfd) i < dimword (:64)’
    by (irule LESS_EQ_LESS_TRANS >> qexists_tac ‘l1hdln (w2n lfd) ps.b.nxt’ >>
        simp[l1hdln_mono]) >>
  drule l1hdl_not_lfd >> simp[]
QED

(* The listener in the interest, L1 wanting its input: the poll set lists it,
   always for input *)
Theorem pf_poll_set_lfd:
  ALOOKUP ps.b.tbl lfd = NONE ∧ (∀h. ALOOKUP ps.b.tbl h ≠ SOME lfd) ∧
  MEM lfd hs ∧ wants_input lfd hw ps lfd ⇒
  (∃e. MEM (lfd, e) (pf_poll_set lfd hw ps hs)) ∧
  (∀e. MEM (lfd, e) (pf_poll_set lfd hw ps hs) ⇒ ODD e) ∧
  EVERY (λ(g, e). e < 256) (pf_poll_set lfd hw ps hs)
Proof
  strip_tac >> simp[pf_poll_set_def] >> rpt conj_tac
  >- (qexists_tac ‘1’ >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> disj1_tac >>
      qexists_tac ‘lfd’ >> simp[])
  >- (rw[MEM_FLAT, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[AllCaseEqs()] >>
      every_case_tac >> gvs[] >> res_tac >> gvs[] >>
      first_x_assum (qspecl_then [‘1’, ‘[(lfd, 1)]’] mp_tac) >>
      simp[] >> qexists_tac ‘lfd’ >> simp[])
  >> simp[EVERY_MEM, FORALL_PROD, MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  rw[] >> every_case_tac >> gvs[] >> rw[]
QED

(* A round, seen from the listener: it stays a listener; the accepted fds
   are handed out from the front (one at least, on an Accept) and the
   round's FConn fds join them; while paused, the pause counts down and
   nothing is accepted; an accept that does not fail logs an FConn; and
   unpaused, with no accepted fd held, the listener in the interest and its
   queue not empty: the round polls the listener, and a poll on it that is
   not retried leads to an accept on it *)
Theorem pround_lfd:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ linv lfd w ∧ pv_rel lfd cm ps s ∧ pown lfd ps ∧
  l1hdln (w2n lfd) (ps.b.nxt + LENGTH acts) < dimword (:64) ⇒
  linv lfd w' ∧
  (∃d. ps'.acq = DROP d ps.acq ++ log_conns log ∧
       (MEM (Accept lfd) acts ∧ ps.acq ≠ [] ⇒ 0 < d)) ∧
  (0 < ps.pause ⇒ ps'.pause = ps.pause − 1 ∧ ¬EXISTS (ev_on «sys_accept» lfd) evs) ∧
  (∀ev. MEM ev evs ∧ ev_on «sys_accept» lfd ev ∧ ¬failed ev ⇒ log_conns log ≠ []) ∧
  (ps.pause = 0 ∧ ps.acq = [] ∧ MEM lfd hs ∧ qof w lfd ≠ [] ⇒
   EXISTS (ev_on «sys_poll» lfd) evs ∧
   ∀ev. MEM ev evs ∧ ev_on «sys_poll» lfd ev ∧ ¬retried ev ⇒
        EXISTS (ev_on «sys_accept» lfd) evs)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule pacts_lfd >> strip_tac >>
  drule pacts_names >> strip_tac >>
  drule_all pacts_linv >> strip_tac >>
  drule_all pacts_winv >> strip_tac >>
  drule_all pacts_qof >> disch_then (qx_choose_then ‘t1’ assume_tac) >>
  drule_all pacts_hacts >> strip_tac >>
  ‘l1hdln (w2n lfd) pa.b.nxt < dimword (:64)’
    by (irule LESS_EQ_LESS_TRANS >>
        qexists_tac ‘l1hdln (w2n lfd) (ps.b.nxt + LENGTH acts)’ >> simp[l1hdln_mono]) >>
  ‘ALOOKUP pa.b.tbl lfd = NONE’ by metis_tac[tbl_lfd] >>
  ‘∀h. ALOOKUP pa.b.tbl h ≠ SOME lfd’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
        gvs[pown_def, MEM_MAP] >> metis_tac[SND]) >>
  rename1 ‘l1_polls _ wa = SOME (rv, w1, pevs)’ >>
  drule_all l1_polls_linv >> strip_tac >>
  drule_all l1_polls_winv >> strip_tac >>
  rename1 ‘l1_flush _ (w1, pa.b) = SOME ((w2, b2), fevs)’ >>
  drule_all l1_flush_linv >> strip_tac >>
  drule_all l1_flush_winv >> strip_tac >>
  ‘l0_rely w1’ by gvs[winv_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3), log, gevs)’ >>
  drule_all pf_fetch_lfd >> strip_tac >>
  drule_all pf_fetch_linv >> strip_tac >>
  drule_all pf_fetch_winv >> strip_tac >>
  drule pf_fetch_closing >> strip_tac >>
  drule pf_fetch_names >> strip_tac >>
  rename1 ‘l1_reap _ (w3, ps3.b) = SOME ((w4, b4), cevs)’ >>
  drule l1_reap_names >> strip_tac >>
  ‘¬MEM lfd ps3.b.closing’ by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  drule_all l1_reap_linv >> strip_tac >>
  (* the round's accepts are the fetch's *)
  ‘∀ev. MEM ev (aevs ++ pevs ++ fevs ++ cevs) ⇒ ¬ev_on «sys_accept» lfd ev’
    by (rpt strip_tac >> imp_res_tac ev_on_name >> gvs[EVERY_MEM] >> res_tac >> gvs[]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qexists_tac ‘d’ >> gvs[])
  >- (strip_tac >> gvs[EVERY_MEM] >> rpt strip_tac >> gvs[] >>
      metis_tac[MEM_APPEND])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘∀ev. MEM ev (_ ++ _ ++ _ ++ _) ⇒ _’ (qspec_then ‘ev’ mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum ‘∀ev. MEM ev gevs ∧ _ ⇒ _’ (qspec_then ‘ev’ mp_tac) >> metis_tac[])
  >> strip_tac >> gvs[] >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw pa hs’ >>
  ‘wants_input lfd hw pa lfd’ by gvs[wants_input_def] >>
  ‘(∃e. MEM (lfd, e) fes) ∧ (∀e. MEM (lfd, e) fes ⇒ ODD e) ∧ EVERY (λ(g, e). e < 256) fes’
    by (qunabbrev_tac ‘fes’ >> match_mp_tac pf_poll_set_lfd >> simp[]) >>
  ‘∀c. MEM c (poll_chunks fes) ⇒ EVERY (λ(g, e). e < 256 ∧ (g = lfd ⇒ ODD e)) c’
    by (‘EVERY (λ(g, e). e < 256 ∧ (g = lfd ⇒ ODD e)) fes’
          by (gvs[EVERY_MEM, FORALL_PROD] >> rw[] >> res_tac) >>
        drule poll_chunks_ok >> simp[EVERY_MEM] >> metis_tac[]) >>
  ‘qof wa lfd ≠ []’ by gvs[] >>
  drule_all l1_polls_l >> strip_tac >>
  ‘MEM (lfd, e) (FLAT (poll_chunks fes))’ by simp[FLAT_poll_chunks] >>
  ‘EXISTS (ev_on «sys_poll» lfd) pevs’
    by (gvs[MEM_FLAT] >> first_x_assum irule >> qexists_tac ‘l’ >>
        simp[MEM_MAP] >> qexists_tac ‘(lfd, e)’ >> simp[]) >>
  ‘MEM lfd (in_fds fes)’
    by (simp[in_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]) >>
  ‘wants_input lfd hw (pa with b := b2) lfd’ by gvs[wants_input_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[] >>
  TRY (imp_res_tac ev_on_name >> gvs[EVERY_MEM] >> res_tac >> gvs[] >> NO_TAC) >>
  ‘MEM lfd (readable_fds rv)’ by metis_tac[] >>
  ‘MEM lfd (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))’ by simp[MEM_FILTER] >>
  gvs[EXISTS_MEM] >> metis_tac[]
QED
