(*
  Route (d), stage S3 (design/46): L1's ownership of the spec's episodes,
  and the input half of the transfer.

  own_ok lfd (k, opn) ps: L1's fds are the open episodes' fds -- the
  pending accepted fds (acq) are episodes nxt, nxt+1, ...; a handle
  l1hdl lfd j in the table holds episode j's fd; a closing fd belongs to
  an episode whose handle is gone; and only the table's fds have input.

  The input half: per episode j, what the spec says j received is what the
  server read through handle l1hdl lfd j, then the input L1 holds for it
  (inbp).  Each step below shows how one of L1's operations extends both
  sides by the same bytes.
*)
Theory honestEchoL0Inv
Ancestors
  alist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1Inv honestL1PFModel honestL1PFInv
  asyncM3World honestL1PFRefine honestL1PFRound honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model
Libs
  preamble

(* The input L1 holds for episode j: the inbox of its handle's fd *)
Definition inbp_def:
  inbp lfd ps j = case ALOOKUP ps.b.tbl (l1hdl lfd j) of
                  | SOME f => inb_of ps f
                  | NONE => []
End

Definition own_ok_def:
  own_ok lfd ((k : num), (opn : (word64 # num) list)) ps ⇔
    ep_ok (k, opn) ∧ k = ps.b.nxt + LENGTH ps.acq ∧
    (∀i. i < LENGTH ps.acq ⇒ ALOOKUP opn (EL i ps.acq) = SOME (ps.b.nxt + i)) ∧
    (∀h f. MEM (h, f) ps.b.tbl ⇒
           ∃j. j < ps.b.nxt ∧ h = l1hdl lfd j ∧ ALOOKUP opn f = SOME j) ∧
    (∀f. MEM f ps.b.closing ⇒
         ∃j. j < ps.b.nxt ∧ ALOOKUP opn f = SOME j ∧ ALOOKUP ps.b.tbl (l1hdl lfd j) = NONE) ∧
    (∀f. inb_of ps f ≠ [] ⇒ MEM f (MAP SND ps.b.tbl))
End

(* The server's reads through handle hd in one action's answer *)
Definition hrd_def:
  hrd hd (a : sact) (r : sresp) = hread hd [(a, SOME r)]
End

(* Handles below the bound are distinct (simp turns l1hdl into hdl) *)
Theorem hdl_eq_iff:
  hdln (w2n lfd) i < dimword (:64) ∧ hdln (w2n lfd) j < dimword (:64) ⇒
  (hdl lfd i = hdl lfd j ⇔ i = j)
Proof
  rw[] >> eq_tac >> rw[] >>
  irule honestL1StepsTheory.l1hdl_11 >> simp[] >> metis_tac[]
QED

Theorem hdln_mono:
  i ≤ j ∧ hdln n j < d ⇒ hdln n i < d
Proof
  rw[hdln_def] >> rw[] >> fs[]
QED

(* An fd's episode is unique: two fds of one episode are equal *)
Theorem own_fd_unique:
  ep_ok (k, opn) ∧ ALOOKUP opn f = SOME j ∧ ALOOKUP opn g = SOME j ⇒ f = g
Proof
  rw[ep_ok_def] >> imp_res_tac ALOOKUP_MEM >>
  ‘∀l : (word64 # num) list. ALL_DISTINCT (MAP SND l) ∧ MEM (f, j) l ∧ MEM (g, j) l ⇒ f = g’
    by (Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem set_outbox_fields[local,simp]:
  (set_outbox f bs st).tbl = st.tbl ∧ (set_outbox f bs st).nxt = st.nxt ∧
  (set_outbox f bs st).closing = st.closing
Proof
  simp[set_outbox_def]
QED

Theorem after_send_fields[local,simp]:
  (after_send f r st).tbl = st.tbl ∧ (after_send f r st).nxt = st.nxt ∧
  (after_send f r st).closing = st.closing
Proof
  rw[after_send_def] >> every_case_tac >> simp[]
QED

(* A Write changes no input, no table and no episode; its send (if any)
   receives nothing *)
Theorem pdo_write_in:
  l0_rely w ∧ pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs) ⇒
  ps'.b.tbl = ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ∧ ps'.b.closing = ps.b.closing ∧
  ps'.acq = ps.acq ∧ ps'.inb = ps.inb ∧ r = Wrote ∧
  l0_ep_st es evs = es ∧ (∀j. ep_rd j es evs = [])
Proof
  rw[pdo_def, l1do_def] >> gvs[AllCaseEqs()] >> PairCases_on ‘es’ >>
  simp[ep_fold_def] >>
  drule_all sys_send_event >> strip_tac >> simp[l0_ep_step_def, ep_fold_def]
QED

(* Accept: the first pending fd becomes handle nxt's *)
Theorem pdo_accept_in:
  pdo lfd (w, ps) (Accept l) = SOME (r, (w', ps'), evs) ⇒
  w' = w ∧ evs = [] ∧ ps'.inb = ps.inb ∧ ps'.b.closing = ps.b.closing ∧
  ((ps' = ps ∧ ps.acq = [] ∧ r = Accepted NONE) ∨
   ∃f q. ps.acq = f :: q ∧ l1hdln (w2n lfd) ps.b.nxt < dimword (:64) ∧
         r = Accepted (SOME (l1hdl lfd ps.b.nxt)) ∧
         ps'.b.tbl = (l1hdl lfd ps.b.nxt, f) :: ps.b.tbl ∧
         ps'.b.nxt = ps.b.nxt + 1 ∧ ps'.acq = q)
Proof
  rw[pdo_def] >> gvs[AllCaseEqs()]
QED

Theorem inb_of_set_inb[simp]:
  inb_of (set_inb f bs ps) g = if g = f then bs else inb_of ps g
Proof
  rw[inb_of_def, set_inb_def, ALOOKUP_ADELKEY] >> rw[]
QED

Theorem set_inb_fields[local,simp]:
  (set_inb f bs ps).b = ps.b ∧ (set_inb f bs ps).acq = ps.acq
Proof
  simp[set_inb_def]
QED

(* own_ok's table fact, by lookup *)
Theorem own_tbl_lookup:
  own_ok lfd (k, opn) ps ∧ ALOOKUP ps.b.tbl h = SOME f ⇒
  ∃j. j < ps.b.nxt ∧ h = l1hdl lfd j ∧ ALOOKUP opn f = SOME j
Proof
  rw[own_ok_def] >> imp_res_tac ALOOKUP_MEM >> res_tac >> metis_tac[]
QED

(* Episode j's handle, in the table, holds j's fd *)
Theorem own_hdl_lookup:
  own_ok lfd (k, opn) ps ∧ l1hdln (w2n lfd) k < dimword (:64) ∧ j < k ∧
  ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f ⇒
  j < ps.b.nxt ∧ ALOOKUP opn f = SOME j
Proof
  strip_tac >> drule_all own_tbl_lookup >> strip_tac >>
  rename1 ‘l1hdl lfd j = l1hdl lfd i’ >>
  ‘hdln (w2n lfd) k < dimword (:64)’ by fs[] >>
  ‘j ≤ k ∧ i ≤ k’ by gvs[own_ok_def] >>
  ‘hdln (w2n lfd) j < dimword (:64) ∧ hdln (w2n lfd) i < dimword (:64)’
    by metis_tac[hdln_mono] >>
  ‘i = j’ by (qpat_x_assum ‘l1hdl _ _ = _’ mp_tac >> simp[hdl_eq_iff]) >> gvs[]
QED

(* A non-empty inbox belongs to a handed-out episode *)
Theorem own_inb:
  own_ok lfd (k, opn) ps ∧ inb_of ps f ≠ [] ⇒
  ∃j. j < ps.b.nxt ∧ ALOOKUP opn f = SOME j
Proof
  rw[own_ok_def] >> first_x_assum drule >> rw[MEM_MAP] >>
  rename1 ‘MEM yy ps.b.tbl’ >> PairCases_on ‘yy’ >> gvs[] >> res_tac >> metis_tac[]
QED

(* As own_hdl_lookup, with the handle as simp leaves it *)
Theorem own_hdl_lookup_h:
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < 18446744073709551616 ∧ j < k ∧
  ALOOKUP ps.b.tbl (hdl lfd j) = SOME f ⇒
  j < ps.b.nxt ∧ ALOOKUP opn f = SOME j
Proof
  strip_tac >> mp_tac own_hdl_lookup >> fs[]
QED

Theorem own_ok_cong:
  ps'.b.tbl = ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ∧ ps'.b.closing = ps.b.closing ∧
  ps'.acq = ps.acq ∧ ps'.inb = ps.inb ⇒
  (own_ok lfd es ps' ⇔ own_ok lfd es ps) ∧ inbp lfd ps' = inbp lfd ps
Proof
  PairCases_on ‘es’ >> simp[own_ok_def, inbp_def, inb_of_def, FUN_EQ_THM]
QED

Theorem hrd_simps[simp]:
  hrd hd (Accept l) r = [] ∧ hrd hd (Write h bs) r = [] ∧
  hrd hd a (Got NONE) = [] ∧ hrd hd a (Got (SOME [])) = [] ∧
  hrd hd a (Accepted x) = [] ∧ hrd hd a Wrote = [] ∧
  hrd hd (Read h n) (Got (SOME bs)) = if h = hd then bs else []
Proof
  rw[hrd_def, hread_def] >> Cases_on ‘a’ >> simp[]
QED

Theorem inb_of_updates[simp]:
  inb_of (ps with b := x) f = inb_of ps f ∧
  inb_of (ps with eof := y) f = inb_of ps f ∧
  inb_of (ps with <| b := x; eof := y |>) f = inb_of ps f ∧
  inb_of (ps with acq := z) f = inb_of ps f
Proof
  simp[inb_of_def]
QED

Theorem l1_close_shape:
  l1_close f (w, b) = SOME ((w', b'), evs) ⇒
  b' = forget f b ∧ ∃out ev. sys_close f w = SOME (out, w', ev) ∧ evs = [ev]
Proof
  rw[l1_close_def, AllCaseEqs()] >> PairCases_on ‘v’ >> gvs[]
QED

Theorem forget_fields[simp]:
  (forget f b).tbl = b.tbl ∧ (forget f b).nxt = b.nxt ∧
  (forget f b).closing = FILTER ($≠ f) b.closing
Proof
  simp[forget_def, set_outbox_def]
QED

(* inbp reads only the table and the inboxes *)
Theorem inbp_cong:
  ps'.b.tbl = ps.b.tbl ∧ ps'.inb = ps.inb ⇒ inbp lfd ps' = inbp lfd ps
Proof
  simp[inbp_def, inb_of_def, FUN_EQ_THM]
QED

(* Removing handle c, whose fd f has an empty inbox, keeps inbp *)
Theorem inbp_ADELKEY:
  ALOOKUP ps.b.tbl c = SOME f ∧ inb_of ps f = [] ∧
  ps'.b.tbl = ADELKEY c ps.b.tbl ∧ ps'.inb = ps.inb ⇒
  inbp lfd ps' j = inbp lfd ps j
Proof
  rw[inbp_def, ALOOKUP_ADELKEY, inb_of_def] >> rw[] >> gvs[inb_of_def]
QED

(* An entry of the table other than handle c's has another fd *)
Theorem own_other_fd:
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧
  ALOOKUP ps.b.tbl c = SOME f ∧ MEM (h, g) ps.b.tbl ∧ h ≠ c ⇒ g ≠ f
Proof
  rpt strip_tac >> gvs[] >>
  drule_all own_tbl_lookup >> strip_tac >>
  qpat_x_assum ‘own_ok _ _ _’ (strip_assume_tac o REWRITE_RULE [own_ok_def]) >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

(* Two entries of one handle hold one fd *)
Theorem own_tbl_entry_fd:
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧
  ALOOKUP ps.b.tbl c = SOME f ∧ MEM (c, g) ps.b.tbl ⇒ g = f
Proof
  strip_tac >> drule_all own_tbl_lookup >> strip_tac >>
  qpat_x_assum ‘own_ok _ _ _’ (fn th => assume_tac th >> strip_assume_tac (REWRITE_RULE [own_ok_def] th)) >>
  first_x_assum drule >> strip_tac >>
  ‘j' ≤ k ∧ j ≤ k’ by fs[] >>
  ‘hdln (w2n lfd) j' < dimword (:64) ∧ hdln (w2n lfd) j < dimword (:64)’
    by metis_tac[hdln_mono] >>
  ‘j' = j’ by (‘l1hdl lfd j' = l1hdl lfd j’ by fs[] >> pop_assum mp_tac >> simp[hdl_eq_iff]) >>
  metis_tac[own_fd_unique]
QED

(* Read at EOF: handle c goes; its fd f (with nothing to read) is closed, or
   left to flush.  L1 keeps owning the other episodes' fds, whether or not
   the spec saw f's episode end *)
Theorem own_drop_handle:
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧
  ALOOKUP ps.b.tbl c = SOME f ∧ inb_of ps f = [] ⇒
  own_ok lfd (k, opn)
    (ps with <| b := ps.b with <| tbl := ADELKEY c ps.b.tbl; closing := f :: ps.b.closing |>;
                eof := e |>) ∧
  own_ok lfd (k, opn)
    (ps with <| b := forget f (ps.b with tbl := ADELKEY c ps.b.tbl); eof := e |>) ∧
  own_ok lfd (k, ADELKEY f opn)
    (ps with <| b := forget f (ps.b with tbl := ADELKEY c ps.b.tbl); eof := e |>)
Proof
  strip_tac >> drule_all own_tbl_lookup >> strip_tac >> rename1 ‘ALOOKUP opn f = SOME i’ >>
  ‘∀h g. MEM (h, g) (ADELKEY c ps.b.tbl) ⇔ MEM (h, g) ps.b.tbl ∧ h ≠ c’
    by (rw[ADELKEY_def, MEM_FILTER] >> metis_tac[]) >>
  ‘∀h g. MEM (h, g) ps.b.tbl ∧ h ≠ c ⇒ g ≠ f’ by metis_tac[own_other_fd] >>
  ‘∀g. MEM (c, g) ps.b.tbl ⇒ g = f’ by metis_tac[own_tbl_entry_fd] >>
  qpat_x_assum ‘own_ok _ _ _’ (strip_assume_tac o REWRITE_RULE [own_ok_def]) >>
  ‘∀x. x < LENGTH ps.acq ⇒ EL x ps.acq ≠ f’
    by (rpt strip_tac >> res_tac >> gvs[]) >>
  ‘∀g. MEM g ps.b.closing ⇒ g ≠ f’
    by (rpt strip_tac >> res_tac >> gvs[] >> rfs[]) >>
  ‘ALOOKUP (ADELKEY c ps.b.tbl) c = NONE’ by simp[ALOOKUP_ADELKEY] >>
  ‘∀g. inb_of ps g ≠ [] ⇒ MEM g (MAP SND (ADELKEY c ps.b.tbl))’
    by (rpt strip_tac >> ‘MEM g (MAP SND ps.b.tbl)’ by metis_tac[] >>
        gvs[MEM_MAP, EXISTS_PROD] >>
        ‘∃p. MEM (p, g) ps.b.tbl’ by metis_tac[] >> qexists_tac ‘p’ >> simp[] >>
        strip_tac >> gvs[] >> res_tac >> gvs[]) >>
  simp[own_ok_def, ep_ok_ADELKEY, ALOOKUP_ADELKEY, MEM_FILTER] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >> res_tac >> gvs[ALOOKUP_ADELKEY] >>
  metis_tac[]
QED

(* One action: the input L1 holds and the episodes' received bytes stay
   in step with the server's reads *)
val close_tac =
  PairCases_on ‘z’ >> gvs[] >> drule l1_close_shape >> strip_tac >> gvs[] >>
          drule_all sys_close_event >> strip_tac >>
          ‘hdln (w2n lfd) k < dimword (:64)’ by simp[] >>
          drule_all own_drop_handle >>
          disch_then (qspec_then ‘FILTER (λy. f ≠ y) ps.eof’ strip_assume_tac) >>
          simp[ep_fold_def, l0_ep_step_def] >>
          ‘∀j. inbp lfd (ps with <|b := forget f (ps.b with tbl := ADELKEY c ps.b.tbl);
                                    eof := FILTER (λy. f ≠ y) ps.eof|>) j = inbp lfd ps j’
            by (gen_tac >> irule inbp_ADELKEY >> simp[] >> qexistsl [‘c’, ‘f’] >> simp[]) >>
          every_case_tac >> gvs[];

Theorem pdo_in:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧
  own_ok lfd (k, opn) ps ∧ l1hdln (w2n lfd) k < dimword (:64) ⇒
  FST (l0_ep_st (k, opn) evs) = k ∧ own_ok lfd (l0_ep_st (k, opn) evs) ps' ∧
  ∀j. j < k ⇒ inbp lfd ps j ++ ep_rd j (k, opn) evs = hrd (l1hdl lfd j) a r ++ inbp lfd ps' j
Proof
  Cases_on ‘a’
  >- ((* Accept *)
      strip_tac >> drule pdo_accept_in >> strip_tac >> gvs[ep_fold_def] >>
      ‘∀j. j ≤ k ⇒ hdln (w2n lfd) j < dimword (:64)’
        by (rw[] >> irule hdln_mono >> qexists_tac ‘k’ >> simp[]) >>
      ‘ps.b.nxt < k’ by gvs[own_ok_def] >>
      ‘∀j. j < k ⇒ (hdl lfd j = hdl lfd ps.b.nxt ⇔ j = ps.b.nxt)’
        by (rw[] >> irule hdl_eq_iff >> simp[]) >>
      ‘ALOOKUP opn f = SOME ps.b.nxt’
        by (gvs[own_ok_def] >>
            qpat_x_assum ‘∀i. i < SUC _ ⇒ _’ (qspec_then ‘0’ mp_tac) >> simp[]) >>
      ‘ALOOKUP ps.b.tbl (hdl lfd ps.b.nxt) = NONE’
        by (Cases_on ‘ALOOKUP ps.b.tbl (hdl lfd ps.b.nxt)’ >> simp[] >>
            drule own_tbl_lookup >> disch_then drule >> strip_tac >> gvs[] >>
            qpat_x_assum ‘∀j. j < k ⇒ (hdl _ _ = _ ⇔ _)’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
      ‘inb_of ps f = []’ by (CCONTR_TAC >> drule_all own_inb >> strip_tac >> gvs[]) >>
      conj_tac
      >- (qpat_x_assum ‘own_ok _ _ ps’ mp_tac >> simp[own_ok_def] >> strip_tac >>
          rpt conj_tac >> rpt strip_tac >> gvs[]
          >- (qpat_x_assum ‘∀i. i < SUC _ ⇒ _’ (qspec_then ‘SUC i’ mp_tac) >> simp[])
          >- (first_x_assum drule >> strip_tac >> qexists_tac ‘j’ >> simp[])
          >- (first_x_assum drule >> strip_tac >> qexists_tac ‘j’ >> simp[] >>
              qpat_x_assum ‘∀j. j < _ ⇒ (hdl _ _ = _ ⇔ _)’ (qspec_then ‘j’ mp_tac) >> simp[])
          >> gvs[inb_of_def] >> metis_tac[inb_of_def]) >>
      rw[inbp_def] >> gvs[] >>
      Cases_on ‘j = ps.b.nxt’ >> gvs[inb_of_def] >>
      qpat_x_assum ‘∀j. j < _ ⇒ (hdl _ _ = _ ⇔ _)’ (qspec_then ‘j’ mp_tac) >> simp[])
  >- ((* Read *)
      strip_tac >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
      gvs[AllCaseEqs()] >> TRY (simp[ep_fold_def] >> NO_TAC)
      >~ [‘set_inb’]
      >- (drule_all own_tbl_lookup >> strip_tac >> rename1 ‘ALOOKUP opn f = SOME i’ >>
          conj_tac
          >- (qpat_x_assum ‘own_ok _ _ _’ mp_tac >> simp[own_ok_def] >> strip_tac >>
              rw[] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >>
              metis_tac[]) >>
          rw[inbp_def, ep_fold_def] >> every_case_tac >> gvs[] >>
          rename1 ‘ALOOKUP ps.b.tbl (hdl lfd j) = SOME g’ >>
          drule_all own_hdl_lookup_h >> strip_tac >>
          rw[] >> gvs[])
      >~ [‘l1_close’] >- close_tac
      >~ [‘l1_close’] >- close_tac >>
      (* still flushing *)
      ‘hdln (w2n lfd) k < dimword (:64)’ by simp[] >>
      drule_all own_drop_handle >>
      disch_then (qspec_then ‘FILTER (λy. f ≠ y) ps.eof’ strip_assume_tac) >>
      simp[ep_fold_def] >> rw[] >> irule EQ_SYM >>
      irule inbp_ADELKEY >> simp[] >> qexistsl [‘c’, ‘f’] >> simp[])
  >> (* Write *)
  strip_tac >> drule_all pdo_write_in >>
  disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  drule own_ok_cong >> strip_tac >> gvs[]
QED

Theorem l0_do_rely:
  l0_do n conf alen w = SOME (out, w', ev) ∧ l0_rely w ⇒ l0_rely w'
Proof
  rw[l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]
QED

Theorem pdo_rely:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ⇒ l0_rely w'
Proof
  Cases_on ‘a’ >> rw[pdo_def, l1do_def, l1_close_def, AllCaseEqs()] >> gvs[] >>
  gvs[sys_close_def, sys_send_def] >> metis_tac[l0_do_rely]
QED

(* The round's actions: the input half moves by the server's reads *)
Theorem pacts_in:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ l1hdln (w2n lfd) k < dimword (:64) ⇒
    l0_rely w' ∧ LENGTH rs = LENGTH acts ∧
    FST (l0_ep_st (k, opn) evs) = k ∧ own_ok lfd (l0_ep_st (k, opn) evs) ps' ∧
    ∀j. j < k ⇒
        inbp lfd ps j ++ ep_rd j (k, opn) evs =
        hread (l1hdl lfd j) (ZIP (acts, MAP SOME rs)) ++ inbp lfd ps' j
Proof
  Induct >> simp[pacts_def, ep_fold_def, hread_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) h = SOME (r, (w1, ps1), evs1)’ >>
  ‘l1hdln (w2n lfd) k < dimword (:64)’ by simp[] >>
  drule_all pdo_in >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  simp[ep_fold_APPEND] >> rpt strip_tac >>
  qpat_x_assum ‘∀j. j < k ⇒ inbp lfd ps j ++ _ = _’ (qspec_then ‘j’ mp_tac) >>
  qpat_x_assum ‘∀j. j < k ⇒ inbp lfd ps1 j ++ _ = _’ (qspec_then ‘j’ mp_tac) >>
  simp[hrd_def, hread_def] >> rpt strip_tac >>
  rewrite_tac[APPEND_ASSOC] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The round's tail: poll, flush, fetch, hung-up drops, reap
   ------------------------------------------------------------------------ *)

(* A poll changes no state of L1's and no episode *)
Theorem l1_polls_in:
  ∀chunks w rv w' evs.
    l1_polls chunks w = SOME (rv, w', evs) ∧ l0_rely w ⇒
    l0_rely w' ∧ l0_ep_st es evs = es ∧ ∀j. ep_rd j es evs = []
Proof
  Induct >> simp[l1_polls_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all sys_poll_event >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  PairCases_on ‘es’ >> gvs[ep_fold_def, l0_ep_step_def]
QED

(* A flush sends (receiving nothing) and changes outboxes and gone only *)
Theorem l1_flush_in:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒
    l0_rely w' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧ b'.closing = b.closing ∧
    l0_ep_st es evs = es ∧ ∀j. ep_rd j es evs = []
Proof
  Induct >> simp[l1_flush_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  drule_all sys_send_event >> strip_tac >>
  ‘l0_rely w''’ by (gvs[sys_send_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> strip_tac >>
  PairCases_on ‘es’ >> gvs[ep_fold_def, l0_ep_step_def]
QED

(* D19's hung-up step drops outboxes only *)
Theorem hup_step_in:
  own_ok lfd es (hup_step hfs ob log ps) = own_ok lfd es ps ∧
  inbp lfd (hup_step hfs ob log ps) = inbp lfd ps
Proof
  ‘(hup_step hfs ob log ps).b.tbl = ps.b.tbl ∧ (hup_step hfs ob log ps).b.nxt = ps.b.nxt ∧
   (hup_step hfs ob log ps).b.closing = ps.b.closing ∧
   (hup_step hfs ob log ps).acq = ps.acq ∧ (hup_step hfs ob log ps).inb = ps.inb’
    by simp[hup_step_def, FOLDL_drop_out] >>
  drule own_ok_cong >> simp[]
QED

(* Forgetting an fd that is no handle's and not pending *)
Theorem own_forget:
  own_ok lfd (k, opn) (ps with b := b) ∧ ¬MEM f (MAP SND b.tbl) ∧ ¬MEM f ps.acq ⇒
  own_ok lfd (k, opn) (ps with b := forget f b) ∧
  own_ok lfd (k, ADELKEY f opn) (ps with b := forget f b)
Proof
  strip_tac >>
  ‘∀h x. MEM (h, x) b.tbl ⇒ x ≠ f’ by (rpt strip_tac >> gvs[MEM_MAP, EXISTS_PROD]) >>
  ‘∀i. i < LENGTH ps.acq ⇒ EL i ps.acq ≠ f’ by metis_tac[MEM_EL] >>
  gvs[own_ok_def, ep_ok_ADELKEY, ALOOKUP_ADELKEY, MEM_FILTER] >>
  rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED

(* The reap closes fds L1 no longer hands out (closing ones, or ones it
   has forgotten): the other episodes' fds stay owned *)
Theorem l1_reap_in:
  ∀fs w b w' b' evs opn.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧
    own_ok lfd (k, opn) (ps with b := b) ∧
    (∀f. MEM f fs ⇒ ¬MEM f (MAP SND b.tbl) ∧ ¬MEM f ps.acq) ⇒
    l0_rely w' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧
    FST (l0_ep_st (k, opn) evs) = k ∧ own_ok lfd (l0_ep_st (k, opn) evs) (ps with b := b') ∧
    ∀j. ep_rd j (k, opn) evs = []
Proof
  Induct >> simp[l1_reap_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (first_x_assum (qspecl_then [‘w’, ‘b’, ‘w'’, ‘b'’, ‘evs’, ‘opn’] mp_tac) >>
       impl_tac >- metis_tac[] >> simp[] >> NO_TAC) >>
  qmatch_asmsub_rename_tac ‘l1_close h (w, b) = SOME (wsx, _)’ >>
  PairCases_on ‘wsx’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  drule_all sys_close_event >> strip_tac >>
  ‘l0_rely wsx0’ by (gvs[sys_close_def] >> metis_tac[l0_do_rely]) >>
  ‘¬MEM h (MAP SND b.tbl) ∧ ¬MEM h ps.acq’ by metis_tac[] >>
  drule_all own_forget >> strip_tac >>
  simp[ep_fold_APPEND, ep_fold_def, l0_ep_step_def] >>
  Cases_on ‘l0_res_of out’ >> gvs[] >>
  ((first_assum (qspecl_then [‘wsx0’, ‘forget h b’, ‘w'’, ‘b'’, ‘evs''’, ‘ADELKEY h opn’] mp_tac) >>
    impl_tac >- (simp[] >> metis_tac[]) >> simp[] >> NO_TAC) ORELSE
   (first_assum (qspecl_then [‘wsx0’, ‘forget h b’, ‘w'’, ‘b'’, ‘evs''’, ‘opn’] mp_tac) >>
    impl_tac >- (simp[] >> metis_tac[]) >> simp[]))
QED

(* ------------------------------------------------------------------------
   The world's side: L1's fds are in use, within the limit
   ------------------------------------------------------------------------ *)

(* L1 owns fds f of the state ps *)
Definition owned_def:
  owned ps f ⇔ MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq
End

Definition wown_def:
  wown lfd w ps ⇔
    l0_rely w ∧ fds_lt w ∧ MEM lfd (l0_used w) ∧ ¬owned ps lfd ∧
    ∀f. owned ps f ⇒ MEM f (l0_used w)
End

Theorem owned_set_inb[simp]:
  owned (set_inb f bs ps) = owned ps
Proof
  simp[owned_def, FUN_EQ_THM]
QED

Theorem wown_l0own:
  wown lfd w ps ⇒ l0own lfd w ps
Proof
  rw[wown_def, l0own_def, owned_def] >> metis_tac[]
QED

Theorem l0_do_fds_lt:
  l0_do n conf alen w = SOME (out, w', ev) ∧ fds_lt w ∧ n ≠ «sys_connect» ⇒ fds_lt w'
Proof
  rw[l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  ‘fds_lt (l0_tick n w)’ by simp[] >>
  drule_all fds_lt_call >> simp[fds_lt_def, l0_used_def]
QED

Theorem l1_close_fds_lt:
  l1_close f (w, b) = SOME ((w', b'), evs) ∧ fds_lt w ⇒ fds_lt w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[sys_close_def] >>
  drule l0_do_fds_lt >> simp[]
QED

Theorem owned_drop:
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧
  ALOOKUP ps.b.tbl c = SOME f ⇒
  (∀g. owned (ps with <| b := forget f (ps.b with tbl := ADELKEY c ps.b.tbl); eof := e |>) g ⇒
       owned ps g ∧ g ≠ f) ∧
  (∀g. owned (ps with <| b := ps.b with <| tbl := ADELKEY c ps.b.tbl;
                                           closing := f :: ps.b.closing |>; eof := e |>) g ⇒
       owned ps g)
Proof
  strip_tac >> drule_all own_tbl_lookup >> strip_tac >>
  ‘∀h g. MEM (h, g) ps.b.tbl ∧ h ≠ c ⇒ g ≠ f’ by metis_tac[own_other_fd] >>
  ‘¬MEM f ps.acq’
    by (strip_tac >> gvs[own_ok_def, MEM_EL] >> res_tac >> gvs[]) >>
  ‘MEM f (MAP SND ps.b.tbl)’ by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  rw[owned_def, ADELKEY_def, MEM_FILTER, MEM_MAP, EXISTS_PROD] >>
  gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* Read at EOF, closed: the world frees f only, which L1 no longer owns *)
val wown_read_tac =
  TRY (qmatch_asmsub_rename_tac ‘l1_close f _ = SOME zz’ >>
       PairCases_on ‘zz’ >> gvs[] >> drule l1_close_shape >> strip_tac >> gvs[] >>
       ‘l0_rely w’ by gvs[wown_def] >>
       drule_all l1_close_l0 >> strip_tac >>
       ‘fds_lt w'’ by (drule l1_close_fds_lt >> gvs[wown_def]) >>
       simp[wown_def] >> rpt conj_tac
       >- (qpat_x_assum ‘∀g. g ≠ f ∧ _ ⇒ _’ irule >> gvs[wown_def])
       >- (strip_tac >>
           qpat_x_assum ‘∀g. owned (ps with <|b := forget _ _; eof := _|>) g ⇒ _’
             (drule_then strip_assume_tac) >> gvs[wown_def])
       >> rpt strip_tac >>
       qpat_x_assum ‘∀g. owned (ps with <|b := forget _ _; eof := _|>) g ⇒ _’
         (drule_then strip_assume_tac) >>
       qpat_x_assum ‘∀g. g ≠ f ∧ _ ⇒ _’ irule >> gvs[wown_def] >> NO_TAC);

Theorem pdo_wown:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ wown lfd w ps ∧
  own_ok lfd (k, opn) ps ∧ l1hdln (w2n lfd) k < dimword (:64) ⇒
  wown lfd w' ps'
Proof
  Cases_on ‘a’
  >- ((* Accept: the pending fd becomes a handle's *)
      strip_tac >> drule pdo_accept_in >> strip_tac >> gvs[wown_def, owned_def] >>
      metis_tac[])
  >- ((* Read *)
      strip_tac >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
      gvs[AllCaseEqs()]
      >~ [‘set_inb’] >- gvs[wown_def] >>
      ‘hdln (w2n lfd) k < dimword (:64)’ by simp[] >>
      drule_all owned_drop >>
      disch_then (qspec_then ‘FILTER (λy. f ≠ y) ps.eof’ strip_assume_tac) >>
      ‘owned ps f’ by (imp_res_tac ALOOKUP_MEM >> simp[owned_def, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      ‘lfd ≠ f’ by (strip_tac >> gvs[wown_def]) >>
      wown_read_tac >> wown_read_tac >>
      (* still flushing: nothing new owned, same world *)
      simp[wown_def] >> rpt conj_tac >> TRY (gvs[wown_def] >> NO_TAC) >>
      TRY (strip_tac >>
           qpat_x_assum ‘∀g. owned _ g ⇒ owned ps g’
             (drule_then strip_assume_tac) >> gvs[wown_def] >> NO_TAC) >>
      rpt strip_tac >>
      qpat_x_assum ‘∀g. owned _ g ⇒ owned ps g’
        (drule_then strip_assume_tac) >> gvs[wown_def])
  >> (* Write: sends only; the fds in use and the limit stay *)
  strip_tac >> ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pdo_write_in >> disch_then (qspec_then ‘(0, [])’ strip_assume_tac) >>
  ‘owned ps' = owned ps’ by simp[owned_def, FUN_EQ_THM] >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
  PairCases_on ‘z’ >> gvs[] >>
  drule_all l1do_write_l0 >> strip_tac >>
  gvs[wown_def, fds_lt_def]
QED

Theorem pacts_wown:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ wown lfd w ps ∧
    own_ok lfd (k, opn) ps ∧ l1hdln (w2n lfd) k < dimword (:64) ⇒
    wown lfd w' ps'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >>
  ‘l1hdln (w2n lfd) k < dimword (:64)’ by simp[] >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pdo_wown >> strip_tac >>
  drule_all pdo_in >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

(* fds_lt depends on the fds in use and the limit only *)
Theorem fds_lt_same:
  l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ⇒ (fds_lt w' ⇔ fds_lt w)
Proof
  simp[fds_lt_def]
QED

Theorem l1_polls_wown:
  l1_polls cs w = SOME (rv, w', evs) ∧ wown lfd w ps ⇒ wown lfd w' ps
Proof
  strip_tac >> ‘l0_rely w’ by gvs[wown_def] >>
  drule_all l1_polls_l0 >> strip_tac >> gvs[wown_def, fds_lt_def]
QED

Theorem l1_flush_wown:
  l1_flush fs (w, ps.b) = SOME ((w', b'), evs) ∧ wown lfd w ps ⇒
  wown lfd w' (ps with b := b')
Proof
  strip_tac >> ‘l0_rely w’ by gvs[wown_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  ‘owned (ps with b := b') = owned ps’ by simp[owned_def, FUN_EQ_THM] >>
  gvs[wown_def, fds_lt_def]
QED

Theorem l1_reap_wown:
  l1_reap fs (w, ps.b) = SOME ((w', b'), evs) ∧ wown lfd w ps ∧
  (∀f. MEM f fs ⇒ ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq ∧ f ≠ lfd) ⇒
  wown lfd w' (ps with b := b')
Proof
  strip_tac >> ‘l0_rely w’ by gvs[wown_def] >>
  drule_all l1_reap_l0 >> strip_tac >>
  ‘fds_lt w'’ by (gvs[wown_def, fds_lt_def] >> metis_tac[]) >>
  gvs[wown_def, owned_def] >> rw[] >> metis_tac[]
QED

(* The fetch's accept (only with no pending fd): a new episode on a fresh fd *)
Theorem fetch_acc_step:
  sys_accept lfd w = SOME (out, w1, ev) ∧ wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧
  ps.acq = [] ∧
  ps1 = (case l0_res_of out of
         | Ok k' => ps with acq := ps.acq ++ [n2w k']
         | Fail e _ => if e = E_MFILE then ps with pause := pf_backoff else ps) ⇒
  wown lfd w1 ps1 ∧ own_ok lfd (l0_ep_step (k, opn) ev) ps1 ∧
  (∀j. ep_rd j (k, opn) [ev] = []) ∧ inbp lfd ps1 = inbp lfd ps ∧
  ps1.b = ps.b ∧ ps1.inb = ps.inb
Proof
  strip_tac >> ‘l0_rely w ∧ fds_lt w’ by gvs[wown_def] >>
  drule_all sys_accept_event >> strip_tac >>
  ‘l0_rely w1 ∧ fds_lt w1’
    by (gvs[sys_accept_def] >> metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_accept» = «sys_connect»”]) >>
  ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)’
    by (gvs[sys_accept_def] >> drule l0_do_used >> simp[]) >>
  simp[ep_fold_def] >>
  Cases_on ‘l0_res_of out’ >> gvs[l0_ep_step_def]
  >- (rename1 ‘l0_res_of out = Ok kk’ >>
      drule_all sys_accept_fresh >> strip_tac >>
      drule_all sys_accept_adds >> strip_tac >>
      ‘¬owned ps (n2w kk)’ by (strip_tac >> gvs[wown_def] >> metis_tac[]) >>
      ‘n2w kk ≠ lfd’ by (strip_tac >> gvs[wown_def]) >>
      ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
      ‘ep_ok (k + 1, (n2w kk, k)::ADELKEY (n2w kk) opn)’
        by (‘ep_ok (l0_ep_step (k,opn) ev)’ by simp[ep_ok_step] >> gvs[l0_ep_step_def]) >>
      rpt conj_tac
      >- (gvs[wown_def, owned_def] >> rw[] >> gvs[] >> metis_tac[])
      >- (qpat_x_assum ‘own_ok _ _ _’ mp_tac >> simp[own_ok_def] >> strip_tac >>
          gvs[] >> rpt conj_tac >> rpt strip_tac >> gvs[ALOOKUP_ADELKEY] >>
          ‘n2w kk ≠ f’ by (strip_tac >> gvs[owned_def, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
          simp[] >> metis_tac[])
      >> simp[inbp_def, inb_of_def, FUN_EQ_THM]) >>
  rw[] >> gvs[wown_def, own_ok_def, owned_def, inbp_def, inb_of_def, FUN_EQ_THM] >>
  metis_tac[]
QED

(* As own_hdl_lookup_h, for any episode up to k (the one an accept is
   about to open included) *)
Theorem own_hdl_lookup_le:
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < 18446744073709551616 ∧ j ≤ k ∧
  ALOOKUP ps.b.tbl (hdl lfd j) = SOME f ⇒
  j < ps.b.nxt ∧ ALOOKUP opn f = SOME j
Proof
  strip_tac >> ‘ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f’ by simp[] >>
  drule_all own_tbl_lookup >> strip_tac >>
  rename1 ‘l1hdl lfd j = l1hdl lfd i’ >>
  ‘i ≤ k’ by gvs[own_ok_def] >>
  ‘hdln (w2n lfd) j < dimword (:64) ∧ hdln (w2n lfd) i < dimword (:64)’
    by (simp[] >> metis_tac[hdln_mono]) >>
  ‘i = j’ by (qpat_x_assum ‘l1hdl _ _ = _’ mp_tac >> simp[hdl_eq_iff]) >> gvs[]
QED

(* Recv on a table fd with an empty inbox: the bytes it returns become
   that fd's inbox, and are what the spec says its episode received *)
Theorem fetch_recv_step:
  sys_recv f pf_chunk w = SOME (out, w1, ev) ∧ wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧
  l1hdln (w2n lfd) k < dimword (:64) ∧
  MEM f (MAP SND ps.b.tbl) ∧ inb_of ps f = [] ∧
  ps1 = (case l0_res_of out of
         | Ok n => if 0 < n then set_inb f (TAKE n (DROP 13 out)) ps
                   else ps with eof := f :: ps.eof
         | Fail e _ => if l1_transient e then ps else ps with eof := f :: ps.eof) ⇒
  wown lfd w1 ps1 ∧ own_ok lfd (l0_ep_step (k, opn) ev) ps1 ∧
  (∀j. j ≤ k ⇒ inbp lfd ps1 j = inbp lfd ps j ++ ep_rd j (k, opn) [ev]) ∧
  ps1.b = ps.b ∧ ps1.acq = ps.acq
Proof
  strip_tac >> ‘l0_rely w ∧ fds_lt w’ by gvs[wown_def] >>
  drule_all sys_recv_event >> strip_tac >>
  ‘l0_rely w1 ∧ fds_lt w1 ∧ l0_used w1 = l0_used w’
    by (gvs[sys_recv_def] >> imp_res_tac l0_do_used >> gvs[] >>
        metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_recv» = «sys_connect»”]) >>
  ‘l0_ep_step (k, opn) ev = (k, opn)’ by simp[l0_ep_step_def] >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  ‘∃j0. j0 < ps.b.nxt ∧ ALOOKUP opn f = SOME j0 ∧
        ALOOKUP ps.b.tbl (l1hdl lfd j0) = SOME f’
    by (gvs[MEM_MAP, EXISTS_PROD] >> rename1 ‘MEM (h, f) ps.b.tbl’ >>
        ‘∃j. j < ps.b.nxt ∧ h = l1hdl lfd j ∧ ALOOKUP opn f = SOME j’
          by (gvs[own_ok_def] >> metis_tac[]) >>
        ‘∃g. ALOOKUP ps.b.tbl h = SOME g’
          by (Cases_on ‘ALOOKUP ps.b.tbl h’ >>
              gvs[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
        ‘j < k’ by gvs[own_ok_def] >>
        gvs[] >> drule_all own_hdl_lookup_h >> strip_tac >>
        ‘g = f’ by metis_tac[own_fd_unique] >> gvs[] >> metis_tac[]) >>
  ‘∀j g. j ≤ k ∧ ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME g ⇒
         (ALOOKUP opn f = SOME j ⇔ g = f)’
    by (rpt strip_tac >> fs[] >> drule_all own_hdl_lookup_le >> strip_tac >>
        metis_tac[own_fd_unique, SOME_11]) >>
  ‘∀j. j ≤ k ∧ ALOOKUP ps.b.tbl (l1hdl lfd j) = NONE ⇒ ALOOKUP opn f ≠ SOME j’
    by (rpt strip_tac >> gvs[]) >>
  ‘owned ps1 = owned ps ∧ ps1.b = ps.b ∧ ps1.acq = ps.acq’
    by (rw[] >> every_case_tac >> gvs[owned_def, FUN_EQ_THM]) >>
  rpt conj_tac
  >- gvs[wown_def]
  >- (qpat_x_assum ‘own_ok _ _ _’ mp_tac >> simp[own_ok_def] >> strip_tac >>
      rw[] >> every_case_tac >> gvs[] >> rw[] >> gvs[inb_of_def] >>
      rw[MEM_MAP, EXISTS_PROD] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[])
  >- (rpt strip_tac >> simp[inbp_def, ep_fold_def] >>
      Cases_on ‘ALOOKUP ps.b.tbl (l1hdl lfd j)’ >> gvs[]
      >- (every_case_tac >> gvs[]) >>
      rename1 ‘ALOOKUP ps.b.tbl _ = SOME g’ >>
      qpat_x_assum ‘∀j' g. _ ⇒ (_ ⇔ _)’ (qspecl_then [‘j’, ‘g’] mp_tac) >> simp[] >>
      Cases_on ‘g = f’ >> gvs[] >> every_case_tac >> gvs[])
  >> simp[]
QED

(* The fetch: the input fetched on a table fd is its episode's, and the
   invariants hold.  At most one accept is pending, so the handle counter
   needs room for nxt + 1 *)
Theorem pf_fetch_in:
  ∀fs w ps k opn w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
    l1hdln (w2n lfd) (ps.b.nxt + 1) < dimword (:64) ∧
    (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND ps.b.tbl)) ⇒
    wown lfd w' ps' ∧ own_ok lfd (l0_ep_st (k, opn) evs) ps' ∧ LENGTH ps'.acq ≤ 1 ∧
    (∀j. j ≤ k ⇒ inbp lfd ps' j = inbp lfd ps j ++ ep_rd j (k, opn) evs) ∧
    ps'.b = ps.b
Proof
  Induct >- (rw[pf_fetch_def] >> simp[ep_fold_def]) >>
  rpt gen_tac >> strip_tac >>
  ‘hdln (w2n lfd) k < dimword (:64)’
    by (‘k ≤ ps.b.nxt + 1’ by gvs[own_ok_def] >> fs[] >> metis_tac[hdln_mono]) >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once pf_fetch_def] >> IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      first_x_assum (qspecl_then [‘w’, ‘ps’, ‘k’, ‘opn’, ‘w'’, ‘ps'’, ‘log’, ‘evs’] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  IF_CASES_TAC >> simp[]
  >- (qpat_x_assum ‘h = lfd’ SUBST_ALL_TAC >>
      ‘ps.acq = [] ∧ ps.pause = 0’ by gvs[wants_input_def] >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, w1, ev)’ >>
      pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      ‘ps1 = case l0_res_of out of
             | Ok k' => ps with acq := ps.acq ++ [n2w k']
             | Fail e _ => if e = E_MFILE then ps with pause := pf_backoff else ps’
        by (every_case_tac >> gvs[]) >>
      drule_all fetch_acc_step >> strip_tac >>
      ‘∃k1 opn1. l0_ep_step (k, opn) ev = (k1, opn1)’ by metis_tac[PAIR] >>
      ‘k ≤ k1’ by (gvs[l0_ep_step_def] >> every_case_tac >> gvs[]) >>
      first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘k1’, ‘opn1’, ‘w'’, ‘ps'’, ‘log'’, ‘evs'’] mp_tac) >>
      impl_tac
      >- (gvs[] >> rpt conj_tac >> TRY (every_case_tac >> gvs[] >> NO_TAC) >> metis_tac[]) >>
      strip_tac >> gvs[] >> rpt strip_tac >>
      qpat_x_assum ‘∀j. ep_rd j _ [_] = []’ (qspec_then ‘j’ mp_tac) >>
      simp[ep_fold_def]) >>
  ‘inb_of ps h = [] ∧ MEM h (MAP SND ps.b.tbl)’ by (gvs[wants_input_def] >> metis_tac[]) >>
  Cases_on ‘sys_recv h pf_chunk w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
  rename1 ‘sys_recv h pf_chunk w = SOME (out, w1, ev)’ >>
  pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  ‘ps1 = case l0_res_of out of
         | Ok n => if 0 < n then set_inb h (TAKE n (DROP 13 out)) ps
                   else ps with eof := h :: ps.eof
         | Fail e _ => if l1_transient e then ps else ps with eof := h :: ps.eof’
    by (every_case_tac >> gvs[]) >>
  ‘l1hdln (w2n lfd) k < dimword (:64)’ by fs[] >>
  drule_all fetch_recv_step >> strip_tac >>
  ‘l0_ep_step (k, opn) ev = (k, opn)’ by (‘l0_rely w’ by gvs[wown_def] >> drule_all sys_recv_event >> simp[l0_ep_step_def]) >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘k’, ‘opn’, ‘w'’, ‘ps'’, ‘log'’, ‘evs'’] mp_tac) >>
  impl_tac
  >- (gvs[] >> rpt conj_tac >> TRY (every_case_tac >> gvs[] >> NO_TAC) >> metis_tac[]) >>
  strip_tac >> gvs[] >> rpt strip_tac >>
  qpat_x_assum ‘∀j. j ≤ k ⇒ inbp lfd ps1 j = _’ (qspec_then ‘j’ mp_tac) >>
  simp[ep_fold_def]
QED
