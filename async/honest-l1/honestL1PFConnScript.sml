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
  honestL1PFModel honestL1Model honestL0WorldInv honestL0World honestL0 asyncCore alist
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
  qof (w with reserved := rs) l = qof w l ∧ qof (upd_lchan j g w) l = qof w l
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
