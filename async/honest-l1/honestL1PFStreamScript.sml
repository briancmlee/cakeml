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
