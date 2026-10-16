(*
  The stream half of R1-live's live-data (design/36 §6, D16), part (A):
  the bytes in an fd's kernel inbox at some round are eventually fetched by
  L1, in order, unless the episode ends (L1 logs EOF or a reset on the fd;
  a break that flushed the inbox is the only way bytes are lost).

  L0 level: a byte string R at the front of f's kernel inbox stays there
  (more may be appended) under every call but a recv on f, unless a break
  flushes the inbox; a recv on f takes its bytes from the front.
*)
Theory honestL1PFStream
Ancestors
  honestL1PFLive honestL1PFRound honestL1PFInv honestL1PFRefine honestL1PFModel
  honestL1Steps honestL1Props honestL1Inv honestL1Model
  honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World honestL0
  asyncCore asyncLevel1 asyncM3World ffi alist
Libs
  preamble

(* R is at the front of f's kernel inbox *)
Definition front_def:
  front w f R ⇔ ∃j. l0_chan_of w f = SOME j ∧ R ≼ (EL j w.chans).inbox
End

(* f's channel broke and its inbox was flushed: nothing more arrives *)
Definition flushed_def:
  flushed w f ⇔
    ∃j. l0_chan_of w f = SOME j ∧ (EL j w.chans).broken ∧ (EL j w.chans).inbox = []
End

Theorem front_simple[simp]:
  (front (w with hist := h) f R ⇔ front w f R) ∧
  (front (w with clock := c) f R ⇔ front w f R) ∧
  (flushed (w with hist := h) f ⇔ flushed w f) ∧
  (flushed (w with clock := c) f ⇔ flushed w f)
Proof
  simp[front_def, flushed_def, l0_chan_of_def]
QED

Theorem front_deliver:
  front w f R ⇒ front (l0_deliver w a) f R ∨ flushed (l0_deliver w a) f
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> gvs[] >>
  gvs[front_def, flushed_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, AllCaseEqs()] >>
  every_case_tac >> gvs[] >> rw[] >> gvs[break_lchan_def] >> rw[] >> gvs[] >>
  TRY (simp[EL_APPEND1] >> NO_TAC) >> gvs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem flushed_deliver:
  flushed w f ⇒ flushed (l0_deliver w a) f
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> gvs[] >>
  gvs[flushed_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE, AllCaseEqs()] >>
  every_case_tac >> gvs[] >> rw[] >> gvs[break_lchan_def] >> rw[] >> gvs[] >>
  simp[EL_APPEND1]
QED

Theorem front_tick:
  front w f R ⇒ front (l0_tick nm w) f R ∨ flushed (l0_tick nm w) f
Proof
  rw[l0_tick_def] >>
  ‘∀as w'. (front w' f R ∨ flushed w' f) ⇒
           front (FOLDL l0_deliver w' as) f R ∨ flushed (FOLDL l0_deliver w' as) f’
    by (Induct >> rw[] >> first_x_assum irule >>
        metis_tac[front_deliver, flushed_deliver]) >>
  first_x_assum irule >> simp[]
QED

Theorem flushed_tick:
  flushed w f ⇒ flushed (l0_tick nm w) f
Proof
  rw[l0_tick_def] >>
  ‘∀as w'. flushed w' f ⇒ flushed (FOLDL l0_deliver w' as) f’
    by (Induct >> rw[] >> metis_tac[flushed_deliver]) >>
  first_x_assum irule >> simp[]
QED

Theorem front_ticks:
  ∀k w. front w f R ∨ flushed w f ⇒
        front (l0_ticks nm k w) f R ∨ flushed (l0_ticks nm k w) f
Proof
  Induct >> rw[l0_ticks_def] >> metis_tac[front_tick, flushed_tick]
QED

Definition fl_def:
  fl w f R ⇔ front w f R ∨ flushed w f
End

(* fl only looks at f's channel *)
Theorem fl_same:
  fl w f R ∧
  (∀j. l0_chan_of w f = SOME j ⇒
       l0_chan_of w' f = SOME j ∧ (EL j w'.chans).inbox = (EL j w.chans).inbox ∧
       (EL j w'.chans).broken = (EL j w.chans).broken) ⇒
  fl w' f R
Proof
  rw[fl_def, front_def, flushed_def] >> res_tac >> gvs[]
QED

Theorem open_not_queued:
  l0wf w ∧ ALOOKUP w.open_fds f = SOME j ∧ MEM (l, p, q) w.listeners ⇒ ¬MEM j q
Proof
  rw[l0wf_def, used_chans_def, ALL_DISTINCT_APPEND] >> strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[MEM_MAP, MEM_FLAT, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem FOLDL_upd_other:
  ∀q w. ¬MEM j q ⇒
        EL j (FOLDL (λw k. upd_lchan k g w) w q).chans = EL j w.chans ∧
        (FOLDL (λw k. upd_lchan k g w) w q).open_fds = w.open_fds ∧
        LENGTH (FOLDL (λw k. upd_lchan k g w) w q).chans = LENGTH w.chans
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then ‘upd_lchan h g w’ mp_tac) >> simp[upd_lchan_def, EL_LUPDATE]
QED

Theorem fl_simple_ops:
  (fl w f R ∧ l0_listen p w = (x, w') ⇒ fl w' f R) ∧
  (fl w f R ∧ l0_send g bs w = (r, w') ⇒ fl w' f R) ∧
  (fl w f R ∧ l0_shutdown g w = (r, w') ⇒ fl w' f R) ∧
  (fl w f R ∧ l0_connerr g w = (y, w') ⇒ fl w' f R)
Proof
  rpt conj_tac >> strip_tac >> irule fl_same >> qexists_tac ‘w’ >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[l0_listen_def, l0_send_def, l0_shutdown_def, l0_connerr_def, l0_chan_of_def,
      AllCaseEqs(), upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem fl_recv_other:
  fl w f R ∧ l0wf w ∧ g ≠ f ∧ l0_recv g n w = (r, d, w') ⇒ fl w' f R
Proof
  strip_tac >> irule fl_same >> qexists_tac ‘w’ >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[l0_recv_def, l0_chan_of_def, AllCaseEqs(), upd_lchan_def, EL_LUPDATE] >>
  rw[] >> gvs[] >> metis_tac[open_chan_ne]
QED

Theorem fl_close_other:
  fl w f R ∧ l0wf w ∧ g ≠ f ∧ l0_close g w = (r, w') ⇒ fl w' f R
Proof
  strip_tac >> irule fl_same >> qexists_tac ‘w’ >> simp[] >>
  rpt gen_tac >> strip_tac >>
  ‘ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans’
    by gvs[l0_chan_of_def, AllCaseEqs()] >>
  gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >>
  Cases_on ‘l0_chan_of w g’ >> simp[] >>
  TRY (rename1 ‘l0_chan_of w g = SOME k’ >>
       ‘j ≠ k’ by (gvs[l0_chan_of_def, AllCaseEqs()] >> metis_tac[open_chan_ne]) >>
       simp[l0_chan_of_def, upd_lchan_def, EL_LUPDATE, ALOOKUP_ADELKEY] >> NO_TAC) >>
  Cases_on ‘FILTER (λ(l,p,q). l = g) w.listeners’ >> simp[l0_chan_of_def] >>
  PairCases_on ‘h’ >> simp[] >>
  ‘MEM (h0, h1, h2) w.listeners’
    by (‘MEM (h0, h1, h2) (FILTER (λ(l,p,q). l = g) w.listeners)’ by simp[] >>
        fs[MEM_FILTER]) >>
  ‘¬MEM j h2’ by metis_tac[open_not_queued] >>
  drule FOLDL_upd_other >> simp[]
QED

Theorem fl_accept:
  fl w f R ∧ l0wf w ∧ (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧
  w.fd_limit ≤ 2 ** 31 ∧ l0_accept l w = (r, w') ⇒ fl w' f R
Proof
  strip_tac >> irule fl_same >> qexists_tac ‘w’ >> simp[] >>
  rpt gen_tac >> strip_tac >>
  ‘ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans’
    by gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free_lim >> simp[]) >>
  ‘MEM f (l0_used w)’
    by (simp[l0_used_def] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >>
        metis_tac[]) >>
  ‘lowest_fd w ≠ f’ by (strip_tac >> gvs[]) >>
  qpat_x_assum ‘l0_accept _ _ = _’ mp_tac >> simp[l0_accept_def] >>
  Cases_on ‘FILTER (λ(l',p,q). l' = l) w.listeners’ >- (rw[] >> simp[]) >>
  PairCases_on ‘h’ >> simp[] >>
  ‘MEM (h0, h1, h2) w.listeners’
    by (‘MEM (h0, h1, h2) (FILTER (λ(l',p,q). l' = l) w.listeners)’ by simp[] >>
        fs[MEM_FILTER]) >>
  ‘¬MEM j h2’ by metis_tac[open_not_queued] >>
  strip_tac >>
  Cases_on ‘w.ch.transient w.hist’ >> gvs[] >>
  Cases_on ‘h2’ >> gvs[] >>
  gvs[AllCaseEqs(), l0_alloc_def] >>
  simp[l0_chan_of_def, upd_lchan_def, EL_LUPDATE] >> gvs[l0_chan_of_def]
QED

Theorem prefix_take:
  R ≼ l ⇒ R ≼ TAKE k l ∨ ∃R'. R = TAKE k l ++ R' ∧ R' ≼ DROP k l
Proof
  rw[IS_PREFIX_APPEND] >> Cases_on ‘LENGTH R ≤ k’
  >- (disj1_tac >> qexists_tac ‘TAKE (k - LENGTH R) l'’ >> simp[TAKE_APPEND])
  >> disj2_tac >> qexists_tac ‘DROP k R’ >> simp[TAKE_APPEND, DROP_APPEND] >>
  ‘k − LENGTH R = 0’ by simp[] >> simp[]
QED

(* A recv on f takes its bytes from the front of f's kernel inbox: a
   recv with data returns a prefix of R or all of R and a further part of
   it remains at the front; any other recv leaves fl as it was *)
Theorem recv_fl:
  fl w f R ∧ noconn w ∧ l0_rely w ∧ 0 < n ∧ l0_recv f n w = (r, d, w') ⇒
  (fl w' f R ∧ ∀k. r = Ok k ⇒ k = 0) ∨
  (∃k. r = Ok k ∧ 0 < k ∧ LENGTH d = k ∧ (R ≼ d ∨ ∃R'. R = d ++ R' ∧ fl w' f R'))
Proof
  rw[fl_def, front_def, flushed_def] >>
  gvs[l0_recv_def, AllCaseEqs(), noconn_def] >>
  TRY (‘j < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >> gvs[]) >>
  TRY (simp[fail_def] >> NO_TAC) >>
  TRY (disj1_tac >> simp[fail_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE] >>
       gvs[l0_chan_of_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (disj1_tac >> gvs[fail_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE,
                        AllCaseEqs()] >> NO_TAC) >>
  TRY (simp[fail_def] >>
       ‘l0_chan_of (upd_lchan j (λc. c with err := NONE) w) f = SOME j ∧
        (EL j (upd_lchan j (λc. c with err := NONE) w).chans).inbox = (EL j w.chans).inbox ∧
        (EL j (upd_lchan j (λc. c with err := NONE) w).chans).broken = (EL j w.chans).broken’
         by gvs[l0_chan_of_def, upd_lchan_def, EL_LUPDATE, AllCaseEqs()] >>
       gvs[] >> NO_TAC) >>
  rename1 ‘l0_chan_of w f = SOME j’ >>
  ‘0 < w.ch.short j w.hist (LENGTH (EL j w.chans).inbox) ∧
   w.ch.short j w.hist (LENGTH (EL j w.chans).inbox) ≤ LENGTH (EL j w.chans).inbox’
    by (‘0 < LENGTH (EL j w.chans).inbox’
          by (Cases_on ‘(EL j w.chans).inbox’ >> fs[]) >>
        qpat_x_assum ‘l0_rely _’ (strip_assume_tac o REWRITE_RULE [l0_rely_def]) >>
        first_x_assum (qspecl_then [‘j’, ‘w.hist’, ‘LENGTH (EL j w.chans).inbox’] mp_tac) >>
        simp[]) >>
  disj2_tac >> simp[LENGTH_TAKE_EQ] >>
  drule prefix_take >>
  disch_then (qspec_then ‘MIN n (w.ch.short j w.hist (LENGTH (EL j w.chans).inbox))’
              strip_assume_tac) >> simp[] >>
  gvs[l0_chan_of_def, upd_lchan_def, EL_LUPDATE, AllCaseEqs()]
QED

(* ------------------------------------------------------------------------
   L1's calls
   ------------------------------------------------------------------------ *)

Theorem fl_simple[simp]:
  fl (w with hist := h) f R = fl w f R
Proof
  simp[fl_def]
QED

Theorem fl_tick:
  fl w f R ⇒ fl (l0_tick nm w) f R
Proof
  rw[fl_def] >> metis_tac[front_tick, flushed_tick]
QED

Theorem fl_ticks:
  fl w f R ⇒ fl (l0_ticks nm k w) f R
Proof
  rw[fl_def] >> metis_tac[front_ticks]
QED

Theorem fl_call:
  fl w f R ∧ l0wf w ∧ (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧
  w.fd_limit ≤ 2 ** 31 ∧ n ≠ «sys_connect» ∧
  ¬((n = «sys_recv» ∨ n = «sys_close») ∧ bytes_fd conf = f) ∧
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ fl w' f R
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac fl_simple_ops >>
  TRY (drule_then irule fl_ticks) >>
  TRY (irule fl_recv_other >> metis_tac[]) >>
  TRY (irule fl_close_other >> metis_tac[]) >>
  TRY (qpat_x_assum ‘l0_accept _ _ = _’ mp_tac >> rpt strip_tac >>
       drule_at (Pos last) fl_accept >> simp[] >> NO_TAC) >>
  gvs[]
QED

Theorem fl_do:
  winv w ∧ fl w f R ∧ n ≠ «sys_connect» ∧
  ¬((n = «sys_recv» ∨ n = «sys_close») ∧ bytes_fd conf = f) ∧
  l0_do n conf alen w = SOME (out, w', ev) ⇒ fl w' f R
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  irule fl_call >> qexistsl_tac [‘REPLICATE alen 0w’, ‘out’, ‘conf’, ‘n’] >>
  simp[] >> qexists_tac ‘l0_tick n w’ >>
  gvs[winv_def, l0wf_tick, fl_tick] >>
  ‘fds_lt (l0_tick n w)’ by simp[] >> gvs[fds_lt_def, l0_rely_def]
QED

Theorem recv_res_ok:
  l0_rely w ∧ l0_recv f n w = (r, d, w') ∧ n < 256 ** 8 ⇒ l0_res_ok r
Proof
  rw[l0_recv_def, AllCaseEqs()] >> gvs[not_chan_def] >> rw[] >>
  gvs[fail_ok, l0_res_ok_def]
QED

(* L1's recv on f: its data (as L1 decodes it) comes from the front *)
Theorem sys_recv_fl:
  winv w ∧ fl w f R ∧ 0 < k ∧ k < 256 ** 8 ∧ sys_recv f k w = SOME (out, w', ev) ⇒
  (fl w' f R ∧ ∀m. l0_res_of out = Ok m ⇒ m = 0) ∨
  (∃m. l0_res_of out = Ok m ∧ 0 < m ∧
       (R ≼ TAKE m (DROP 13 out) ∨ ∃R'. R = TAKE m (DROP 13 out) ++ R' ∧ fl w' f R'))
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_recv» w’ >>
  ‘fl wt f R ∧ noconn wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, fl_tick, noconn_tick] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_res_ok r’
    by (qspecl_then [‘wt’, ‘f’, ‘k’, ‘r’, ‘d’, ‘w'’] mp_tac
          (Q.GENL [‘w’, ‘f’, ‘n’, ‘r’, ‘d’, ‘w'’] recv_res_ok) >> simp[]) >>
  ‘l0_res_of (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) = r’
    by (REWRITE_TAC [GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >> simp[]) >>
  ‘DROP 13 (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) =
   d ++ REPLICATE (k − LENGTH d) 0w’
    by (‘LENGTH (enc_res r) = 13’ by (irule LENGTH_enc_res >> simp[]) >>
        REWRITE_TAC [GSYM APPEND_ASSOC] >>
        qpat_x_assum ‘LENGTH _ = 13’ (SUBST1_TAC o SYM) >> simp[DROP_APPEND, DROP_LENGTH_NIL] >>
        ‘LENGTH (enc_res r) − (LENGTH d + LENGTH (enc_res r)) = 0’ by decide_tac >>
        simp[]) >>
  drule_at (Pos last) recv_fl >> simp[] >> disch_then (qspec_then ‘R’ mp_tac) >>
  simp[] >> strip_tac >> simp[TAKE_LENGTH_APPEND]
QED

(* ------------------------------------------------------------------------
   The round's stages
   ------------------------------------------------------------------------ *)

Theorem sys_fl:
  (winv w ∧ fl w f R ∧ sys_send g bs w = SOME (out, w', ev) ⇒ fl w' f R) ∧
  (winv w ∧ fl w f R ∧ g ≠ f ∧ sys_close g w = SOME (out, w', ev) ⇒ fl w' f R) ∧
  (winv w ∧ fl w f R ∧ g ≠ f ∧ sys_recv g k w = SOME (out, w', ev) ⇒ fl w' f R) ∧
  (winv w ∧ fl w f R ∧ sys_accept g w = SOME (out, w', ev) ⇒ fl w' f R) ∧
  (winv w ∧ fl w f R ∧ sys_poll fes w = SOME (out, w', ev) ⇒ fl w' f R)
Proof
  rw[sys_close_def, sys_send_def, sys_recv_def, sys_accept_def, sys_poll_def] >>
  drule_at (Pos last) fl_do >> simp[]
QED

Theorem l1_close_fl:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ fl w f R ∧ g ≠ f ⇒ fl w' f R
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_fl]
QED

Theorem pdo_fl:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ fl w f R ∧
  fkeep lfd h f ps ⇒ fl w' f R
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY (drule_all l1_close_fl >> simp[] >> NO_TAC) >>
  TRY (rename1 ‘l1_close g _ = _’ >>
       ‘g ≠ f’ by (strip_tac >> gvs[fkeep_def]) >>
       drule_all l1_close_fl >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >> metis_tac[sys_fl]
QED

Theorem pacts_fl:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ fl w f R ∧
    fkeep lfd h f ps ⇒ fl w' f R
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all pdo_fl >> strip_tac >> drule_all pdo_f >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_polls_fl:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ fl w f R ⇒ fl w' f R
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_fl:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ fl w f R ⇒
                       fl w' f R
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send _ _ _ = SOME (out, w1, ev)’ >>
  ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_reap_fl:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ fl w f R ∧
                       ¬MEM f fs ⇒ fl w' f R
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >>
      ‘winv q ∧ fl q f R’ by metis_tac[l1_close_fl, l1_close_winv] >>
      first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

(* The bytes a fetch log fetched on f, in order; and whether it ended f's
   episode (EOF or a reset) *)
Definition fdata_def:
  fdata f log =
    FLAT (MAP (λx. case x of FData g bs => if g = f then bs else [] | _ => []) log)
End

Definition fend_def:
  fend f log ⇔ EXISTS (λx. x = FEof f ∨ x = FReset f) log
End

Theorem fdata_simps[simp]:
  fdata f [] = [] ∧
  fdata f (FData g bs :: l) = (if g = f then bs else []) ++ fdata f l ∧
  fdata f (FConn g :: l) = fdata f l ∧
  fdata f (FEof g :: l) = fdata f l ∧
  fdata f (FReset g :: l) = fdata f l ∧
  (fend f [] ⇔ F) ∧
  (fend f (FData g bs :: l) ⇔ fend f l) ∧
  (fend f (FConn g :: l) ⇔ fend f l) ∧
  (fend f (FEof g :: l) ⇔ g = f ∨ fend f l) ∧
  (fend f (FReset g :: l) ⇔ g = f ∨ fend f l)
Proof
  rw[fdata_def, fend_def] >> metis_tac[]
QED

Theorem fdata_append[simp]:
  fdata f (l1 ++ l2) = fdata f l1 ++ fdata f l2 ∧
  (fend f (l1 ++ l2) ⇔ fend f l1 ∨ fend f l2)
Proof
  simp[fdata_def, fend_def]
QED

Theorem prefix_cancel[simp]:
  ∀d. d ++ a ≼ d ++ b ⇔ a ≼ b
Proof
  Induct >> simp[]
QED

Theorem prefix_app:
  R ≼ d ⇒ R ≼ d ++ x
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem fl_used:
  fl w f R ⇒ MEM f (l0_used w)
Proof
  rw[fl_def, front_def, flushed_def, l0_chan_of_def, AllCaseEqs(), l0_used_def] >>
  imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* One recv on f in the fetch: the episode ends, or nothing changes, or a
   prefix of R (or all of it) is logged as data *)
Theorem fetch_step_f:
  winv w ∧ fl w f R ∧ fkeep lfd h f ps ∧ sys_recv f pf_chunk w = SOME (out, w1, ev) ∧
  (case l0_res_of out of
   | Ok k =>
       if 0 < k then (set_inb f (TAKE k (DROP 13 out)) ps, [FData f (TAKE k (DROP 13 out))])
       else (ps with eof := f :: ps.eof, [FEof f])
   | Fail e _ =>
       if l1_transient e then (ps, []) else (ps with eof := f :: ps.eof, [FReset f])) =
  (ps1, lg) ⇒
  winv w1 ∧
  (fend f lg ∨ (lg = [] ∧ ps1 = ps ∧ fl w1 f R) ∨
   ∃d. lg = [FData f d] ∧ fkeep lfd h f ps1 ∧ (R ≼ d ∨ ∃R'. R = d ++ R' ∧ fl w1 f R'))
Proof
  strip_tac >> ‘winv w1’ by metis_tac[sys_winv] >> simp[] >>
  ‘0 < pf_chunk ∧ pf_chunk < 256 ** 8’ by EVAL_TAC >>
  drule_all sys_recv_fl >> strip_tac
  >- (Cases_on ‘l0_res_of out’ >> gvs[] >>
      TRY (rename1 ‘Ok n’ >> Cases_on ‘0 < n’) >> gvs[AllCaseEqs()] >> rw[] >> gvs[])
  >> gvs[] >> qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def]
QED

(* The fetch, seen from f's kernel inbox: R (at the front) is fetched in
   order, or the episode ends *)
Theorem pf_fetch_stream:
  ∀fs w ps w' ps' log evs R.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ fl w f R ∧
    fkeep lfd h f ps ⇒
    fend f log ∨ R ≼ fdata f log ∨
    ∃R'. R = fdata f log ++ R' ∧ fl w' f R' ∧ fkeep lfd h f ps'
Proof
  Induct >- (simp[pf_fetch_def] >> rw[] >> simp[]) >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  ‘¬MEM f ps.eof ∧ f ≠ lfd ∧ ¬MEM f ps.acq’
    by (qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def]) >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- ((* accept on the listener *)
      ‘g ≠ f’ by (strip_tac >> fs[]) >>
      simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
      ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
      gvs[AllCaseEqs()] >>
      first_x_assum drule >> disch_then (qspec_then ‘R’ mp_tac) >> impl_tac >>
      TRY (simp[] >> NO_TAC) >>
      TRY (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           ‘¬MEM (n2w k) (l0_used w)’
             by (irule sys_accept_fresh >> gvs[winv_def] >> metis_tac[]) >>
           ‘n2w k ≠ f’ by metis_tac[fl_used] >>
           qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def] >> NO_TAC) >>
      simp[])
  >> Cases_on ‘g = f’
  >- ((* recv on f *)
      gvs[] >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> gvs[CaseEq "option", CaseEq "prod"] >>
      drule_all fetch_step_f >> strip_tac >> gvs[] >>
      TRY (first_x_assum drule >> disch_then (qspec_then ‘R’ mp_tac) >> simp[] >> NO_TAC) >>
      TRY (simp[prefix_app] >> NO_TAC) >>
      first_x_assum drule >> disch_then (qspec_then ‘R'’ mp_tac) >> simp[] >>
      strip_tac >> simp[])
  >> (* recv on another fd *)
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
  ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> disch_then (qspec_then ‘R’ mp_tac) >> impl_tac >>
  TRY (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def] >> NO_TAC) >>
  simp[]
QED

(* One round, seen from f's kernel inbox: R (at the front) is fetched in
   order, or the episode ends, or a prefix of it is fetched and the rest
   stays at the front *)
Theorem pround_stream:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ fl w f R ∧ fkeep lfd h f ps ⇒
  fend f log ∨ R ≼ fdata f log ∨
  ∃R'. R = fdata f log ++ R' ∧ fl w' f R' ∧ fkeep lfd h f ps'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule_all pacts_fl >> strip_tac >>
  drule_all pacts_f >> strip_tac >>
  drule_all pacts_winv >> strip_tac >>
  drule_all l1_polls_fl >> strip_tac >>
  drule_all l1_polls_winv >> strip_tac >>
  drule_all l1_flush_fl >> strip_tac >>
  drule_all l1_flush_f >> strip_tac >>
  drule_all l1_flush_winv >> strip_tac >>
  ‘fkeep lfd h f (pa with b := b2)’ by (irule fkeep_b_same >> fs[]) >>
  drule_all pf_fetch_winv >> strip_tac >>
  drule_all pf_fetch_stream >> strip_tac >> simp[] >>
  ‘¬MEM f ps3.b.closing’ by (qpat_x_assum ‘fkeep _ _ _ ps3’ mp_tac >> simp[fkeep_def]) >>
  drule_all l1_reap_fl >> strip_tac >>
  drule_all l1_reap_f >> strip_tac >>
  disj2_tac >> disj2_tac >> simp[] >>
  irule fkeep_b_same >> fs[]
QED

(* ------------------------------------------------------------------------
   Every data entry of a fetch log is non-empty
   ------------------------------------------------------------------------ *)

Theorem sys_recv_len:
  l0_rely w ∧ sys_recv f n w = SOME (out, w', ev) ⇒ LENGTH out = n + 13
Proof
  rw[sys_recv_def, l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]
QED

Theorem pf_fetch_data:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ⇒
    ∀g. ¬MEM (FData g []) log
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  first_x_assum drule_all >> strip_tac >>
  ‘l0_rely w’ by fs[winv_def] >>
  TRY (drule_all sys_recv_len >> strip_tac) >>
  ‘0 < pf_chunk’ by EVAL_TAC >> CCONTR_TAC >> gvs[] >> res_tac >> gvs[]
QED

Theorem pround_data:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ⇒
  ∀g. ¬MEM (FData g []) log
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all pacts_winv >> strip_tac >>
  drule_all l1_polls_winv >> strip_tac >>
  drule_all l1_flush_winv >> strip_tac >>
  drule_all pf_fetch_data >> simp[]
QED

(* ------------------------------------------------------------------------
   Along the run
   ------------------------------------------------------------------------ *)

Theorem fl_pend:
  fl w f R ∧ R ≠ [] ⇒ pend w f
Proof
  rw[fl_def, front_def, flushed_def, pend_def] >> gvs[] >>
  Cases_on ‘(EL j w.chans).inbox’ >> gvs[]
QED

Theorem fetched_fend:
  fetched f log ⇔ fend f log ∨ ∃bs. MEM (FData f bs) log
Proof
  simp[fetched_def, fend_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem fdata_nil:
  (∀bs. ¬MEM (FData f bs) log) ⇒ fdata f log = []
Proof
  Induct_on ‘log’ >> simp[] >> Cases >> simp[] >> rw[] >> metis_tac[]
QED

Theorem fdata_nonnil:
  MEM (FData f bs) log ∧ bs ≠ [] ⇒ fdata f log ≠ []
Proof
  Induct_on ‘log’ >> simp[] >> Cases >> rw[] >> gvs[]
QED

(* The fetch logs of the d rounds from n0 *)
Definition rlogs_def:
  rlogs lfd hw ifds m w0 n0 d = FLAT (GENLIST (λi. rlog lfd hw ifds m w0 (n0 + i)) d)
End

Theorem rlogs_add:
  ∀b a. rlogs lfd hw ifds m w0 n0 (a + b) =
        rlogs lfd hw ifds m w0 n0 a ++ rlogs lfd hw ifds m w0 (n0 + a) b
Proof
  rpt gen_tac >> ‘a + b = b + a’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC [rlogs_def, GENLIST_APPEND, FLAT_APPEND] >>
  AP_TERM_TAC >> AP_TERM_TAC >> simp[GENLIST_FUN_EQ]
QED
