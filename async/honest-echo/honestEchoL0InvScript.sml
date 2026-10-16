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
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
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

Theorem own_ok_cong[local]:
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
