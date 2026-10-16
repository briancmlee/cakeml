(*
  An invariant of the L0 world (proved, not trusted): every channel is in
  at most one place, either open under one fd or pending in one listener's
  queue, and every such channel index is in range.  The real kernel keeps
  this by construction; the model's operations preserve it.  Used by
  R1-live: a channel's pending input survives every call but a recv on its
  own fd.
*)
Theory honestL0WorldInv
Ancestors
  honestL0World honestL0WorldProps honestL0Rely honestL0 alist
Libs
  preamble

(* The channels in use: open ones, then the queues *)
Definition used_chans_def:
  used_chans w = MAP SND w.open_fds ++ FLAT (MAP (SND o SND) w.listeners)
End

Definition l0wf_def:
  l0wf w ⇔ ALL_DISTINCT (used_chans w) ∧ EVERY (λj. j < LENGTH w.chans) (used_chans w)
End

Theorem l0wf_upd_lchan[simp]:
  l0wf (upd_lchan j g w) ⇔ l0wf w
Proof
  simp[l0wf_def, used_chans_def, upd_lchan_def]
QED

Theorem l0wf_clock_hist[simp]:
  (l0wf (w with clock := c) ⇔ l0wf w) ∧ (l0wf (w with hist := hh) ⇔ l0wf w)
Proof
  simp[l0wf_def, used_chans_def]
QED

(* Appending x to the queue of listener l *)
Theorem AFUPDKEY_queue_PERM:
  ∀ls. MEM l (MAP FST ls) ⇒
       PERM (FLAT (MAP (SND o SND) (AFUPDKEY l (λ(p, q). (p, q ++ [x])) ls)))
            (FLAT (MAP (SND o SND) ls) ++ [x])
Proof
  Induct >> simp[FORALL_PROD, AFUPDKEY_def] >> rw[] >> gvs[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, PERM_APPEND_IFF] >>
  FIRST [first_assum ACCEPT_TAC, MATCH_ACCEPT_TAC PERM_APPEND]
QED

Theorem l0wf_deliver:
  l0wf w ⇒ l0wf (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> TRY (simp[] >> NO_TAC) >>
  every_case_tac >> gvs[] >>
  rename1 ‘FILTER _ w.listeners = (l, rr) :: rest’ >> PairCases_on ‘rr’ >>
  rename1 ‘FILTER _ w.listeners = (l, pp, qq) :: rest’ >>
  ‘MEM (l, pp, qq) w.listeners’
    by (‘MEM (l, pp, qq) (FILTER (λ(l', p', q). p' = n) w.listeners)’ by simp[] >>
        gvs[MEM_FILTER]) >>
  ‘MEM l (MAP FST w.listeners)’ by (simp[MEM_MAP] >> qexists_tac ‘(l, pp, qq)’ >> simp[]) >>
  drule AFUPDKEY_queue_PERM >>
  disch_then (qspec_then ‘LENGTH w.chans’ assume_tac) >>
  gvs[l0wf_def, used_chans_def] >>
  ‘¬MEM (LENGTH w.chans) (MAP SND w.open_fds ++ FLAT (MAP (SND o SND) w.listeners))’
    by (strip_tac >> gvs[EVERY_MEM] >> res_tac >> gvs[] >>
        ‘LENGTH w.chans < LENGTH w.chans’ by metis_tac[MEM_APPEND] >> gvs[]) >>
  ‘PERM (MAP SND w.open_fds ++
         FLAT (MAP (SND o SND) (AFUPDKEY l (λ(p,q). (p,q ++ [LENGTH w.chans])) w.listeners)))
        (MAP SND w.open_fds ++ FLAT (MAP (SND o SND) w.listeners) ++ [LENGTH w.chans])’
    by (REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[PERM_APPEND_IFF]) >>
  conj_tac
  >- (drule ALL_DISTINCT_PERM >> simp[ALL_DISTINCT_APPEND] >> gvs[ALL_DISTINCT_APPEND])
  >> gvs[EVERY_MEM] >> rw[] >>
  drule PERM_MEM_EQ >> disch_then (qspec_then ‘j’ assume_tac) >> gvs[] >>
  res_tac >> simp[]
QED

Theorem l0wf_tick:
  l0wf w ⇒ l0wf (l0_tick n w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. l0wf w ⇒ l0wf (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[l0wf_deliver]) >>
  rw[] >> first_x_assum irule >> simp[]
QED

Theorem l0wf_ticks:
  ∀k w. l0wf w ⇒ l0wf (l0_ticks n k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[l0wf_tick]
QED

(* Popping the head j of listener l's queue *)
Theorem AFUPDKEY_pop_PERM:
  ∀ls. FILTER (λ(l', p, q). l' = l) ls = (l, p, j :: q') :: rest ⇒
       PERM (j :: FLAT (MAP (SND o SND) (AFUPDKEY l (K (p, q')) ls)))
            (FLAT (MAP (SND o SND) ls))
Proof
  Induct >- simp[] >>
  simp[FORALL_PROD] >> rpt gen_tac >>
  rename1 ‘(k, pk, qk) :: ls’ >>
  Cases_on ‘k = l’ >> simp[AFUPDKEY_def] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘PERM _ _’ mp_tac >> simp[PERM_CONS_EQ_APPEND] >> strip_tac >>
  qexistsl_tac [‘qk ++ M’, ‘N’] >> simp[PERM_APPEND_IFF] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, PERM_APPEND_IFF] >> first_assum ACCEPT_TAC
QED

Theorem FLAT_FILTER_sub:
  ∀ls. (ALL_DISTINCT (FLAT (MAP g ls)) ⇒ ALL_DISTINCT (FLAT (MAP g (FILTER Q ls)))) ∧
       (MEM x (FLAT (MAP g (FILTER Q ls))) ⇒ MEM x (FLAT (MAP g ls)))
Proof
  Induct >> rw[ALL_DISTINCT_APPEND] >> gvs[MEM_FLAT, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

(* used_chans shrinks to a sub-list: the invariant is kept *)
Theorem l0wf_sub:
  l0wf w ∧ (∀j. MEM j (used_chans w') ⇒ MEM j (used_chans w)) ∧
  LENGTH w.chans ≤ LENGTH w'.chans ∧ ALL_DISTINCT (used_chans w') ⇒ l0wf w'
Proof
  rw[l0wf_def, EVERY_MEM] >> res_tac >> res_tac >> simp[]
QED

Theorem used_FOLDL_upd[simp]:
  ∀q w. used_chans (FOLDL (λw j. upd_lchan j g w) w q) = used_chans w ∧
        LENGTH (FOLDL (λw j. upd_lchan j g w) w q).chans = LENGTH w.chans
Proof
  Induct >> simp[] >> simp[used_chans_def, upd_lchan_def]
QED

Theorem l0wf_listen:
  l0wf w ∧ l0_listen p w = (x, w') ⇒ l0wf w'
Proof
  rw[l0_listen_def, AllCaseEqs()] >> gvs[l0wf_def, used_chans_def]
QED

Theorem l0wf_simple_ops:
  (l0wf w ∧ l0_recv f n w = (r, d, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_send f bs w = (r, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_shutdown f w = (r, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_connerr f w = (y, w') ⇒ l0wf w')
Proof
  rpt conj_tac >>
  rw[l0_recv_def, l0_send_def, l0_shutdown_def, l0_connerr_def, AllCaseEqs()] >> gvs[]
QED

Theorem pop_used_PERM:
  FILTER (λ(l', p, q). l' = l) w.listeners = (v, p, j :: q') :: rest ⇒
  PERM (j :: used_chans (w with listeners := AFUPDKEY l (K (p, q')) w.listeners))
       (used_chans w)
Proof
  strip_tac >>
  ‘v = l’ by (‘MEM (v, p, j :: q') (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
              gvs[MEM_FILTER]) >>
  gvs[] >> drule AFUPDKEY_pop_PERM >> strip_tac >>
  simp[used_chans_def] >>
  irule PERM_TRANS >>
  qexists_tac ‘MAP SND w.open_fds ++ (j :: FLAT (MAP (SND o SND) (AFUPDKEY l (K (p,q')) w.listeners)))’ >>
  simp[PERM_APPEND_IFF] >> simp[PERM_CONS_EQ_APPEND] >>
  qexistsl_tac [‘MAP SND w.open_fds’, ‘FLAT (MAP (SND o SND) (AFUPDKEY l (K (p,q')) w.listeners))’] >>
  simp[]
QED

Theorem l0wf_accept:
  l0wf w ∧ l0_accept l w = (r, w') ⇒ l0wf w'
Proof
  simp[l0_accept_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule pop_used_PERM >> strip_tac >> gvs[l0wf_def] >>
  drule_all ALL_DISTINCT_PERM >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘PERM (j :: U) _’ >>
  ‘ALL_DISTINCT (j :: U)’ by gvs[] >>
  ‘∀x. MEM x (j :: U) ⇒ x < LENGTH w.chans’
    by (rpt strip_tac >> imp_res_tac PERM_MEM_EQ >> gvs[EVERY_MEM]) >>
  gvs[Abbr ‘U’, used_chans_def, EVERY_MEM] >> metis_tac[]
QED

Theorem MAP_SND_FILTER_sub:
  ∀l. (ALL_DISTINCT (MAP SND l) ⇒ ALL_DISTINCT (MAP SND (FILTER P l))) ∧
      (MEM x (MAP SND (FILTER P l)) ⇒ MEM x (MAP SND l))
Proof
  Induct >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem l0wf_FOLDL_upd[simp]:
  ∀q w. l0wf (FOLDL (λw j. upd_lchan j g w) w q) ⇔ l0wf w
Proof
  Induct >> simp[]
QED

Theorem l0wf_close_fd:
  l0wf w ⇒ l0wf (close_fd f w)
Proof
  strip_tac >> simp[close_fd_def] >> every_case_tac >> simp[] >>
  gvs[l0wf_def, used_chans_def, ADELKEY_def, ALL_DISTINCT_APPEND, EVERY_MEM] >>
  rw[] >> metis_tac[MAP_SND_FILTER_sub, FLAT_FILTER_sub]
QED

Theorem l0wf_close:
  l0wf w ∧ l0_close f w = (r, w') ⇒ l0wf w'
Proof
  rw[l0_close_def, AllCaseEqs()] >> gvs[l0wf_close_fd]
QED

Theorem l0wf_connect:
  l0wf w ∧ l0_connect p w = (r, v, w') ⇒ l0wf w'
Proof
  rw[l0_connect_def, AllCaseEqs()] >> gvs[] >>
  gvs[l0wf_def, used_chans_def, EVERY_MEM] >> rw[] >> res_tac >> simp[] >>
  strip_tac >> res_tac >> gvs[]
QED

Theorem l0wf_ops:
  (l0wf w ∧ l0_listen p w = (x, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_accept l w = (r, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_recv f n w = (r, d, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_send f bs w = (r, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_shutdown f w = (r, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_close f w = (r, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_connect p w = (r, v, w') ⇒ l0wf w') ∧
  (l0wf w ∧ l0_connerr f w = (y, w') ⇒ l0wf w')
Proof
  rpt conj_tac >> rpt strip_tac >>
  metis_tac[l0wf_listen, l0wf_simple_ops, l0wf_accept, l0wf_close, l0wf_connect]
QED

Theorem l0wf_call:
  l0wf w ∧ l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ l0wf w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac l0wf_ops >>
  TRY (drule_then irule l0wf_ticks) >> gvs[]
QED

Theorem l0wf_ffi_fn:
  l0wf w ∧ l0_ffi_fn n conf bytes w = SOME (FFIreturn bytes' w') ⇒ l0wf w'
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> simp[] >>
  irule l0wf_call >> metis_tac[l0wf_tick]
QED

(* ------------------------------------------------------------------------
   Pending input persists: fd f's channel has unread data, EOF or a break
   until a recv on f (or a close of f)
   ------------------------------------------------------------------------ *)

Definition pend_def:
  pend w f ⇔
    ∃j. l0_chan_of w f = SOME j ∧
        ((EL j w.chans).inbox ≠ [] ∨ (EL j w.chans).peer_eof ∨ (EL j w.chans).broken)
End

Theorem pend_deliver:
  pend w f ⇒ pend (l0_deliver w a) f
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >>
  gvs[pend_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, EL_APPEND1, AllCaseEqs()] >>
  rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem pend_tick:
  pend w f ⇒ pend (l0_tick n w) f
Proof
  simp[l0_tick_def] >>
  ‘∀as w. pend w f ⇒ pend (FOLDL l0_deliver w as) f’
    by (Induct >> simp[] >> metis_tac[pend_deliver]) >>
  rw[] >> first_x_assum irule >> gvs[pend_def, l0_chan_of_def]
QED

Theorem pend_ticks:
  ∀k w. pend w f ⇒ pend (l0_ticks n k w) f
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[pend_tick]
QED

(* Distinct fds have distinct channels *)
Theorem open_chan_ne:
  l0wf w ∧ ALOOKUP w.open_fds f = SOME j ∧ ALOOKUP w.open_fds g = SOME k ∧ f ≠ g ⇒ j ≠ k
Proof
  rw[l0wf_def, used_chans_def, ALL_DISTINCT_APPEND] >>
  imp_res_tac ALOOKUP_MEM >> strip_tac >> gvs[] >>
  ‘∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (f, j) l ∧ MEM (g, j) l ⇒ f = g’
    by (Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP] >> metis_tac[SND]) >>
  metis_tac[]
QED

(* The lowest fd is free when every used fd is below a limit ≤ 2^31 *)
Theorem lowest_fd_free_lim:
  (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧ w.fd_limit ≤ 2 ** 31 ⇒
  ¬MEM (lowest_fd w) (l0_used w)
Proof
  rw[lowest_fd_def] >> numLib.LEAST_ELIM_TAC >> conj_tac
  >- (qexists_tac ‘2 ** 31’ >> strip_tac >> first_x_assum drule >> simp[]) >>
  rw[]
QED

Theorem pend_simple_ops:
  (pend w f ∧ l0_listen p w = (x, w') ⇒ pend w' f) ∧
  (pend w f ∧ l0_send g bs w = (r, w') ⇒ pend w' f) ∧
  (pend w f ∧ l0_shutdown g w = (r, w') ⇒ pend w' f) ∧
  (pend w f ∧ l0_connerr g w = (y, w') ⇒ pend w' f)
Proof
  rpt conj_tac >>
  rw[l0_listen_def, l0_send_def, l0_shutdown_def, l0_connerr_def, AllCaseEqs()] >>
  gvs[pend_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem pend_recv_other:
  pend w f ∧ l0wf w ∧ g ≠ f ∧ l0_recv g n w = (r, d, w') ⇒ pend w' f
Proof
  rw[l0_recv_def] >> every_case_tac >> gvs[] >>
  rename1 ‘l0_chan_of w g = SOME k’ >>
  ‘∃j. l0_chan_of w f = SOME j’ by gvs[pend_def] >>
  ‘j ≠ k’ by (gvs[l0_chan_of_def, AllCaseEqs()] >> metis_tac[open_chan_ne]) >>
  gvs[pend_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, AllCaseEqs()]
QED

Theorem pend_FOLDL_break:
  ∀q w. pend w f ⇒ pend (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q) f
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[pend_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, AllCaseEqs()] >>
  rw[break_lchan_def] >> rw[]
QED

Theorem pend_close_other:
  pend w f ∧ g ≠ f ∧ l0_close g w = (r, w') ⇒ pend w' f
Proof
  rw[l0_close_def, AllCaseEqs()] >> gvs[] >>
  simp[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule pend_FOLDL_break >> gvs[pend_def, l0_chan_of_def] >> NO_TAC) >>
  gvs[pend_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, ALOOKUP_ADELKEY,
      AllCaseEqs()] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem pend_accept:
  pend w f ∧ l0wf w ∧ (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧ w.fd_limit ≤ 2 ** 31 ∧
  l0_accept l w = (r, w') ⇒ pend w' f
Proof
  strip_tac >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free_lim >> simp[]) >>
  ‘MEM f (l0_used w)’
    by (gvs[pend_def, l0_chan_of_def, AllCaseEqs(), l0_used_def] >>
        imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[FST]) >>
  ‘lowest_fd w ≠ f’ by (strip_tac >> gvs[]) >>
  gvs[l0_accept_def, AllCaseEqs(), l0_alloc_def] >>
  gvs[pend_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, AllCaseEqs()] >>
  rw[break_lchan_def] >> rw[]
QED

Theorem pend_connect:
  pend w f ∧ (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧ w.fd_limit ≤ 2 ** 31 ∧
  l0_connect p w = (r, v, w') ⇒ pend w' f
Proof
  strip_tac >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free_lim >> simp[]) >>
  ‘MEM f (l0_used w)’
    by (gvs[pend_def, l0_chan_of_def, AllCaseEqs(), l0_used_def] >>
        imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[FST]) >>
  ‘lowest_fd w ≠ f’ by (strip_tac >> gvs[]) >>
  gvs[l0_connect_def, AllCaseEqs(), l0_alloc_def] >>
  gvs[pend_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, EL_APPEND1, AllCaseEqs()] >>
  rw[] >> gvs[EL_APPEND1]
QED

(* ------------------------------------------------------------------------
   No channel is connecting (true of every run without sys_connect)
   ------------------------------------------------------------------------ *)

(* Pending input on f survives every call but a recv or close on f *)
Theorem pend_call:
  pend w f ∧ l0wf w ∧ (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧
  w.fd_limit ≤ 2 ** 31 ∧
  ¬((n = «sys_recv» ∨ n = «sys_close») ∧ bytes_fd conf = f) ∧
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ pend w' f
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac pend_simple_ops >>
  TRY (drule_then irule pend_ticks) >>
  TRY (irule pend_recv_other >> metis_tac[]) >>
  TRY (irule pend_close_other >> metis_tac[]) >>
  TRY (qpat_x_assum ‘l0_accept _ _ = _’ mp_tac >> rpt strip_tac >>
       drule_at (Pos last) pend_accept >> simp[] >> NO_TAC) >>
  qpat_x_assum ‘l0_connect _ _ = _’ mp_tac >> rpt strip_tac >>
  drule_at (Pos last) pend_connect >> simp[]
QED

Definition noconn_def:
  noconn w ⇔ ∀j. j < LENGTH w.chans ⇒ ¬(EL j w.chans).connecting
End

Theorem noconn_deliver:
  noconn w ⇒ noconn (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >>
  gvs[noconn_def, upd_lchan_def, EL_LUPDATE] >> rw[] >>
  gvs[EL_APPEND_EQN, fresh_lchan_def] >> rw[] >> gvs[break_lchan_def] >> rw[] >>
  TRY (Cases_on ‘j < LENGTH w.chans’ >> gvs[EL_APPEND1, EL_APPEND2, fresh_lchan_def] >>
       ‘j = LENGTH w.chans’ by simp[] >> gvs[EL_APPEND2, fresh_lchan_def] >> NO_TAC) >>
  rw[break_lchan_def]
QED

Theorem noconn_tick:
  noconn w ⇒ noconn (l0_tick n w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. noconn w ⇒ noconn (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[noconn_deliver]) >>
  rw[] >> first_x_assum irule >> gvs[noconn_def]
QED

Theorem noconn_ticks:
  ∀k w. noconn w ⇒ noconn (l0_ticks n k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[noconn_tick]
QED

Theorem noconn_FOLDL_break:
  ∀q w. noconn w ⇒ noconn (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[noconn_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> rw[break_lchan_def]
QED

Theorem noconn_close_fd:
  noconn w ⇒ noconn (close_fd f w)
Proof
  rw[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule noconn_FOLDL_break >> gvs[noconn_def] >> NO_TAC) >>
  gvs[noconn_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem noconn_ops:
  (noconn w ∧ l0_listen p w = (x, w') ⇒ noconn w') ∧
  (noconn w ∧ l0_accept l w = (r, w') ⇒ noconn w') ∧
  (noconn w ∧ l0_recv f n w = (r, d, w') ⇒ noconn w') ∧
  (noconn w ∧ l0_send f bs w = (r, w') ⇒ noconn w') ∧
  (noconn w ∧ l0_shutdown f w = (r, w') ⇒ noconn w') ∧
  (noconn w ∧ l0_close f w = (r, w') ⇒ noconn w') ∧
  (noconn w ∧ l0_connerr f w = (y, w') ⇒ noconn w')
Proof
  rpt conj_tac >>
  rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
     l0_close_def, l0_connerr_def, AllCaseEqs()] >> gvs[] >>
  TRY (simp[close_fd_def] >> every_case_tac >> simp[] >>
       TRY (irule noconn_FOLDL_break) >> gvs[noconn_def] >> NO_TAC) >>
  TRY (irule noconn_close_fd >> simp[] >> NO_TAC) >>
  gvs[noconn_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> rw[break_lchan_def]
QED

Theorem noconn_call:
  noconn w ∧ n ≠ «sys_connect» ∧ l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  noconn w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac noconn_ops >>
  TRY (drule_then irule noconn_ticks) >> gvs[]
QED

(* A pending fd polled for input reports IN *)
Theorem pend_revents_in:
  noconn w ∧ pend w f ∧ ODD ev ⇒ (byte_revents (fd_revents w (f, ev))).rin
Proof
  rw[pend_def, fd_revents_def] >> simp[byte_revents_revents_byte] >>
  gvs[noconn_def, chan_revents_def] >>
  ‘j < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >> gvs[]
QED
