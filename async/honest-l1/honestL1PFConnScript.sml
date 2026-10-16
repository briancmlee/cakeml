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
  qof w1 l = qof w l ++ t1 ∧ wmono w1 w' ∧
  k ≤ LENGTH t2 + LENGTH (qof w1 l) ∧ qw = DROP k (qof w1 l ++ t2) ∧
  (∀j. MEM j (TAKE k (qof w1 l ++ t2)) ⇒ resolved w' log j) ⇒
  ∃t k. k ≤ LENGTH t + LENGTH (qof w l) ∧ qw = DROP k (qof w l ++ t) ∧
        ∀j. MEM j (TAKE k (qof w l ++ t)) ⇒ resolved w' (lg ++ log) j
Proof
  rw[] >> qexistsl_tac [‘t1 ++ t2’, ‘k’] >> gvs[] >> rw[] >>
  irule resolved_mono >> qexistsl_tac [‘log’, ‘w'’] >> simp[]
QED

(* The queue after a step that popped its head j (resolved by then) *)
Theorem queue_pop:
  qof w l ++ t1 = j :: qof w1 l ∧ resolved w1 lg j ∧ wmono w1 w' ∧
  k ≤ LENGTH t2 + LENGTH (qof w1 l) ∧ qw = DROP k (qof w1 l ++ t2) ∧
  (∀j. MEM j (TAKE k (qof w1 l ++ t2)) ⇒ resolved w' log j) ⇒
  ∃t k. k ≤ LENGTH t + LENGTH (qof w l) ∧ qw = DROP k (qof w l ++ t) ∧
        ∀j. MEM j (TAKE k (qof w l ++ t)) ⇒ resolved w' (lg ++ log) j
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
          ∀j. MEM j (TAKE k (qof w lfd ++ t)) ⇒ resolved w' log j
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
      ‘wmono w w'’ by metis_tac[wmono_trans] >> simp[] >>
      drule_all sys_accept_queue >> strip_tac
      >- (irule queue_app >> metis_tac[])
      >- (irule queue_pop >> gvs[] >>
          qexistsl_tac [‘j’, ‘k’, ‘t'’, ‘t’, ‘w1’] >> gvs[] >>
          simp[resolved_def] >> disj1_tac >> qexists_tac ‘n2w k'’ >> gvs[])
      >> irule queue_pop >> gvs[] >>
      qexistsl_tac [‘j’, ‘k’, ‘t'’, ‘t’, ‘w1’] >> gvs[] >>
      simp[resolved_def])
  >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum ‘option_CASE (pf_fetch _ _ _ _) _ _ = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
  ‘winv w1 ∧ wmono w w1’ by metis_tac[sys_winv, sys_wmono] >>
  first_x_assum drule_all >> strip_tac >>
  ‘wmono w w'’ by metis_tac[wmono_trans] >> simp[] >>
  drule (el 3 (CONJUNCTS sys_qof)) >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  irule queue_app >> metis_tac[]
QED
