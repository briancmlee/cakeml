(*
  The proxy's state and the endpoint handle layer's: the relation prel,
  kept by every action of a round and by the poll.  From it: no misuse,
  fresh distinct handles, and the relay invariants (moonshotProxySafe).

  Per pair (pok): the front is open until it reads EOF, Up and not shut;
  the backend, once connected, is open until it reads EOF or is refused,
  never shut, Up once it has answered a read, and otherwise Up, Refused,
  or still Connecting (clean, and not reported ready); and the relay:
  what was written to each side, then what is pending for it, is what was
  read from the other.
*)
Theory moonshotProxyRel
Ancestors
  moonshotProxy moonshotClient proxyHLStmts moonshotClientSpec endpointHLModel
  endpointWorld honestL1Steps asyncLevel1 asyncCore asyncHLModel socketV2FFI
Libs
  preamble

(* Every handle a pair holds (open or not) *)
Definition phds_def:
  phds p = p.fh :: (case p.bh of SOME c => [c] | NONE => [])
End

Theorem popen_phds:
  MEM h (popen p) ⇒ MEM h (phds p)
Proof
  rw[popen_def, phds_def] >> every_case_tac >> gvs[]
QED

(* Handle h has fd f, open on channel j *)
Definition hch_def:
  hch (w : eworld) (hs : ehstate) h j ⇔
    ∃f. ALOOKUP hs.tbl h = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans
End

Definition pok_def:
  pok (w : eworld) (hs : ehstate) ps (rdy : word64 set) p ⇔
    ¬hl_refused p.fh ps ∧ (p.fo ⇔ ¬hl_eof p.fh ps) ∧
    (p.fo ⇒ ∃j. hch w hs p.fh j ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut) ∧
    (¬p.fo ⇒ ¬MEM p.fh (MAP FST hs.tbl)) ∧
    case p.bh of
    | NONE => hl_read p.fh ps = [] ∧ hl_sent p.fh ps = [] ∧ p.fq = [] ∧ p.bq = [] ∧
              ¬p.bo ∧ ¬p.bup
    | SOME c =>
        (p.bo ⇔ ¬hl_eof c ps ∧ ¬hl_refused c ps) ∧ (p.bup ⇔ hl_up c ps) ∧
        (¬p.bo ⇒ ¬MEM c (MAP FST hs.tbl)) ∧
        (p.bo ⇒ ∃j. hch w hs c j ∧ ¬(EL j w.chans).shut ∧
                    (p.bup ⇒ (EL j w.chans).status = Up) ∧
                    ((EL j w.chans).status = Up ∨ (EL j w.chans).status = Refused ∨
                     (EL j w.chans).status = Connecting ∧ (EL j w.chans).inbox = [] ∧
                     ¬(EL j w.chans).peer_eof ∧ c ∉ rdy)) ∧
        hl_sent c ps ++ p.fq = hl_read p.fh ps ∧
        hl_sent p.fh ps ++ p.bq = hl_read c ps ∧
        (hl_read p.fh ps ≠ [] ⇒ p.bup)
End

Definition prel_def:
  prel lfd st (rdy : word64 set) ps (w : eworld) (hs : ehstate) ⇔
    w.takes = (λj b n. n) ∧ alloc_ok w.alloc ∧ w.reserved = [] ∧
    (∃a q. w.listening = [(lfd, a, q)] ∧ ALL_DISTINCT q ∧
           EVERY (λj. j < LENGTH w.chans ∧ (EL j w.chans).status = Up ∧
                      ¬(EL j w.chans).shut ∧ ¬MEM j (MAP SND w.open_fds)) q) ∧
    ALL_DISTINCT (MAP FST hs.tbl) ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧
    ALL_DISTINCT (MAP FST w.open_fds) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
    EVERY (λj. j < LENGTH w.chans) (MAP SND w.open_fds) ∧
    ¬MEM lfd (MAP FST w.open_fds) ∧
    (∀f. MEM f (MAP FST w.open_fds) ⇔ MEM f (MAP SND hs.tbl)) ∧
    (* the handles: fresh, one per issue, two per pair at most *)
    ALL_DISTINCT (FLAT (MAP phds st.pc)) ∧ LENGTH (FLAT (MAP phds st.pc)) = hs.nxt ∧
    (∀h. MEM h (FLAT (MAP phds st.pc)) ⇒ ∃k. k < hs.nxt ∧ h = hdl lfd k) ∧
    2 * LENGTH st.pc ≤ cbound ∧
    (∀h. MEM h (MAP FST hs.tbl) ⇒ ∃p. MEM p st.pc ∧ MEM h (popen p)) ∧
    EVERY (pok w hs ps rdy) st.pc ∧
    (* the history mentions only the pairs' handles *)
    (∀h. hl_sent h ps ≠ [] ∨ hl_read h ps ≠ [] ∨ hl_eof h ps ∨ hl_refused h ps ∨
         hl_up h ps ⇒ MEM h (FLAT (MAP phds st.pc))) ∧
    (∀h. h ∈ rdy ⇒ h = lfd ∨ MEM h (FLAT (MAP phds st.pc))) ∧
    (∀hd. MEM hd (hl_acc_handles ps) ⇔ ∃p. MEM p st.pc ∧ p.fh = hd) ∧
    (∀c. MEM c (hl_conn_handles ps) ⇔ ∃p. MEM p st.pc ∧ p.bh = SOME c)
End

(* ------------------------------------------------------------------------
   The history, one more pair
   ------------------------------------------------------------------------ *)

Theorem hl_up_APPEND[simp]:
  (hl_up c (ps1 ++ ps2) ⇔ hl_up c ps1 ∨ hl_up c ps2) ∧ ¬hl_up c [] ∧
  (hl_up c [(x, r)] ⇔ ∃k r'. x = ERead c k ∧ r = EGot r')
Proof
  simp[hl_up_def] >> metis_tac[]
QED

Theorem hl_acc_APPEND[simp]:
  hl_acc_handles (ps1 ++ ps2) = hl_acc_handles ps1 ++ hl_acc_handles ps2 ∧
  hl_acc_handles [] = [] ∧
  hl_acc_handles [(x, r)] =
    (case (x, r) of (EAccept l, EAccepted (SOME hd)) => [hd] | _ => [])
Proof
  simp[hl_acc_handles_def]
QED

(* An action on handle h0 (or none) says nothing of another handle h *)
Theorem hl_other:
  (∀k. x ≠ ERead h k) ∧ (∀bs. x ≠ EWrite h bs) ⇒
  hl_sent h [(x, r)] = [] ∧ hl_read h [(x, r)] = [] ∧ ¬hl_eof h [(x, r)] ∧
  ¬hl_refused h [(x, r)] ∧ ¬hl_up h [(x, r)]
Proof
  Cases_on ‘x’ >> Cases_on ‘r’ >> simp[] >> rw[] >> every_case_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The frame: an action that keeps every other handle's fd and channel
   ------------------------------------------------------------------------ *)

(* The history of handle h, unchanged *)
Definition hsame_def:
  hsame h ps ps' ⇔
    hl_sent h ps' = hl_sent h ps ∧ hl_read h ps' = hl_read h ps ∧
    (hl_eof h ps' ⇔ hl_eof h ps) ∧ (hl_refused h ps' ⇔ hl_refused h ps) ∧
    (hl_up h ps' ⇔ hl_up h ps)
End

Theorem hsame_other:
  (∀k. x ≠ ERead h k) ∧ (∀bs. x ≠ EWrite h bs) ⇒ hsame h ps (ps ++ [(x, r)])
Proof
  strip_tac >> drule_all hl_other >> disch_then (qspec_then ‘r’ strip_assume_tac) >>
  simp[hsame_def]
QED

Theorem pok_frame:
  pok w hs ps rdy p ∧ (∀h. MEM h (phds p) ⇒ hsame h ps ps') ∧
  (∀h j. MEM h (phds p) ∧ hch w hs h j ⇒ hch w1 hs1 h j ∧ EL j w1.chans = EL j w.chans) ∧
  (∀h. MEM h (phds p) ∧ ¬MEM h (MAP FST hs.tbl) ⇒ ¬MEM h (MAP FST hs1.tbl)) ⇒
  pok w1 hs1 ps' rdy p
Proof
  simp[phds_def, hsame_def] >> strip_tac >>
  qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> Cases_on ‘p.bh’ >>
  simp[pok_def] >> strip_tac >> gvs[] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> strip_tac >> qexists_tac ‘j’ >> gvs[] >> NO_TAC) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   Handles
   ------------------------------------------------------------------------ *)

Theorem hdln_lt_cbound:
  k ≤ cbound ⇒ hdln (w2n (lfd : word64)) k < dimword (:64)
Proof
  rw[hdln_def, cbound_def, dimword_def] >> simp[]
QED

(* The next handle is new, and not the listener *)
Theorem prel_fresh:
  prel lfd st rdy ps w hs ∧ hs.nxt ≤ cbound ⇒
  ¬MEM (hdl lfd hs.nxt) (FLAT (MAP phds st.pc)) ∧ hdl lfd hs.nxt ≠ lfd ∧
  hdl lfd hs.nxt ∉ rdy ∧ ¬MEM (hdl lfd hs.nxt) (MAP FST hs.tbl) ∧
  hl_sent (hdl lfd hs.nxt) ps = [] ∧ hl_read (hdl lfd hs.nxt) ps = [] ∧
  ¬hl_eof (hdl lfd hs.nxt) ps ∧ ¬hl_refused (hdl lfd hs.nxt) ps ∧ ¬hl_up (hdl lfd hs.nxt) ps
Proof
  strip_tac >>
  ‘hdln (w2n lfd) hs.nxt < dimword (:64)’ by simp[hdln_lt_cbound] >>
  ‘¬MEM (hdl lfd hs.nxt) (FLAT (MAP phds st.pc))’
    by (strip_tac >> fs[prel_def] >> first_x_assum drule >> strip_tac >>
        ‘hdl lfd k ≠ hdl lfd hs.nxt’ by (irule hdl_fresh >> simp[]) >> fs[]) >>
  ‘hdl lfd hs.nxt ≠ lfd’ by simp[hdl_not_lfd] >>
  simp[] >> fs[prel_def] >> rpt conj_tac
  >- metis_tac[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      fs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[popen_phds])
  >> metis_tac[]
QED

Theorem LENGTH_phds_le:
  LENGTH (FLAT (MAP phds pc)) ≤ 2 * LENGTH pc
Proof
  Induct_on ‘pc’ >> simp[phds_def] >> rw[] >> every_case_tac >> simp[]
QED

Theorem pupd_one[simp]:
  pupd st [(i, x)] [r] =
    case (x, r) of
    | (ELevel h, ELvl l) => st with lv := (h, l) :: st.lv
    | (EAccept _, EAccepted (SOME hd)) => st with pc := st.pc ++ [pnew hd]
    | (EAccept _, _) => st
    | _ => st with pc := LUPDATE (pres (EL i st.pc) x r) i st.pc
Proof
  simp[pupd_def]
QED

(* ------------------------------------------------------------------------
   An action the history ignores, in an unchanged world
   ------------------------------------------------------------------------ *)

Theorem pok_quiet:
  pok w hs ps rdy p ∧ (∀h. hsame h ps ps') ⇒ pok w hs ps' rdy p
Proof
  strip_tac >> irule pok_frame >> simp[] >> metis_tac[]
QED

Theorem prel_quiet:
  prel lfd st rdy ps w hs ∧ (∀h. hsame h ps ps') ∧
  hl_acc_handles ps' = hl_acc_handles ps ∧ hl_conn_handles ps' = hl_conn_handles ps ⇒
  prel lfd st rdy ps' w hs
Proof
  simp[prel_def] >> strip_tac >> simp[] >> rpt conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >> irule pok_quiet >> metis_tac[])
  >> fs[hsame_def] >> metis_tac[]
QED

(* An action on no handle: the history of each is unchanged *)
Theorem hsame_quiet:
  (∀h k. x ≠ ERead h k) ∧ (∀h bs. x ≠ EWrite h bs) ⇒ ∀h. hsame h ps (ps ++ [(x, r)])
Proof
  rpt strip_tac >> irule hsame_other >> simp[]
QED

Theorem prel_nconnects[simp]:
  prel lfd st rdy ps (w with nconnects := n) hs ⇔ prel lfd st rdy ps w hs
Proof
  ‘pok (w with nconnects := n) hs ps rdy = pok w hs ps rdy’
    by simp[FUN_EQ_THM, pok_def, hch_def] >>
  simp[prel_def]
QED

Theorem prel_lv[simp]:
  prel lfd (st with lv := x) = prel lfd st ∧ prel lfd (st with last := y) = prel lfd st
Proof
  simp[FUN_EQ_THM, prel_def]
QED

(* ------------------------------------------------------------------------
   The accept
   ------------------------------------------------------------------------ *)

Theorem phds_pnew[simp]:
  phds (pnew hd) = [hd] ∧ popen (pnew hd) = [hd]
Proof
  simp[phds_def, popen_def, pnew_def]
QED

Theorem pok_pnew:
  hch w hs hd j ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧
  hl_sent hd ps = [] ∧ hl_read hd ps = [] ∧ ¬hl_eof hd ps ∧ ¬hl_refused hd ps ⇒
  pok w hs ps rdy (pnew hd)
Proof
  rw[pok_def, pnew_def] >> metis_tac[]
QED

Theorem prel_accept:
  prel lfd st rdy ps w hs ∧ 2 * LENGTH st.pc + 2 ≤ cbound ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) (EAccept lfd) = SOME (r, (w1, hs1)) ∧
    prel lfd (pupd st [(i, EAccept lfd)] [r]) rdy (ps ++ [(EAccept lfd, r)]) w1 hs1 ∧
    (pupd st [(i, EAccept lfd)] [r]).lv = st.lv ∧
    (pupd st [(i, EAccept lfd)] [r]).last = st.last ∧
    ∃new. (pupd st [(i, EAccept lfd)] [r]).pc = st.pc ++ new
Proof
  strip_tac >>
  ‘∃a q. w.listening = [(lfd, a, q)]’ by fs[prel_def] >>
  ‘hs.nxt + 2 ≤ cbound’
    by (fs[prel_def] >> mp_tac (Q.INST [‘pc’ |-> ‘st.pc’] LENGTH_phds_le) >> simp[]) >>
  simp[ehdo_def, ep_accept_def] >>
  Cases_on ‘q’ >> simp[]
  >- (irule prel_quiet >> simp[] >> qexists_tac ‘ps’ >> simp[hsame_quiet]) >>
  rename1 ‘(lfd, a, j :: q)’ >>
  Cases_on ‘ep_alloc w j’ >> simp[]
  >- (irule prel_quiet >> simp[] >> qexists_tac ‘ps’ >> simp[hsame_quiet]) >>
  rename1 ‘ep_alloc w j = SOME fw’ >> PairCases_on ‘fw’ >>
  qpat_x_assum ‘ep_alloc _ _ = _’ mp_tac >> simp[ep_alloc_def] >> strip_tac >> gvs[] >>
  simp[hdln_lt_cbound] >>
  qabbrev_tac ‘f = w.alloc j (ep_used w)’ >>
  qabbrev_tac ‘hd = hdl lfd hs.nxt’ >>
  ‘hs.nxt ≤ cbound’ by simp[] >>
  drule_all prel_fresh >> simp[] >> strip_tac >>
  ‘¬MEM f (ep_used w)’ by (fs[prel_def, alloc_ok_def, Abbr ‘f’]) >>
  ‘¬MEM f (MAP FST w.open_fds) ∧ f ≠ lfd’ by (qpat_x_assum ‘¬MEM f _’ mp_tac >> simp[ep_used_def] >> fs[prel_def]) >>
  ‘¬MEM f (MAP SND hs.tbl)’ by (fs[prel_def] >> metis_tac[]) >>
  qpat_x_assum ‘prel _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [prel_def]) >>
  ‘q' = j :: q’
    by (qpat_x_assum ‘w.listening = [(lfd, a, j :: q)]’ mp_tac >>
        qpat_x_assum ‘w.listening = [(lfd, a', q')]’ mp_tac >> simp_tac (srw_ss()) []) >>
  pop_assum SUBST_ALL_TAC >>
  ‘j < LENGTH w.chans ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧
   ¬MEM j (MAP SND w.open_fds) ∧ EVERY (λj'. j' < LENGTH w.chans ∧ (EL j' w.chans).status = Up ∧
     ¬(EL j' w.chans).shut ∧ ¬MEM j' (MAP SND w.open_fds)) q’
    by fs[] >>
  conj_tac >- (mp_tac (Q.INST [‘k’ |-> ‘hs.nxt’, ‘lfd’ |-> ‘lfd’] hdln_lt_cbound) >> simp[]) >>
  REWRITE_TAC [prel_def] >> simp_tac (srw_ss()) [eh_new_def, AFUPDKEY_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (asm_simp_tac (srw_ss()) [] >> NO_TAC) >>
  TRY (qpat_x_assum ‘ALL_DISTINCT (j::q)’ mp_tac >> simp_tac (srw_ss()) [] >> NO_TAC) >>
  TRY (qpat_x_assum ‘ALL_DISTINCT (j::q)’ mp_tac >> qpat_x_assum ‘EVERY _ q’ mp_tac >>
       simp_tac (srw_ss()) [EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘¬MEM hd (MAP FST _)’ mp_tac >> simp[Abbr ‘hd’] >> NO_TAC) >>
  TRY (strip_tac >> qpat_x_assum ‘f ≠ lfd’ mp_tac >> asm_rewrite_tac [] >> NO_TAC) >>
  TRY (gen_tac >> qpat_x_assum ‘∀f. MEM f (MAP FST _) ⇔ _’ (qspec_then ‘f'’ SUBST1_TAC) >>
       simp[] >> NO_TAC) >>
  TRY (simp[ALL_DISTINCT_APPEND] >> NO_TAC)
  >~ [‘hs.nxt + 1’]
  >- (rpt strip_tac
      >- (qpat_x_assum ‘∀h. MEM h (FLAT _) ⇒ ∃k. _’ drule >> strip_tac >>
          qexists_tac ‘k’ >> simp[])
      >> qexists_tac ‘hs.nxt’ >> simp[Abbr ‘hd’])
  >~ [‘pok _ _ _ _ (pnew _)’]
  >- (irule pok_pnew >> simp[hch_def, Abbr ‘hd’] >> TRY (qexists_tac ‘j’) >> simp[])
  >~ [‘EVERY (pok _ _ (_ ++ _) _) _’]
  >- (simp[EVERY_MEM] >> rpt strip_tac >> rename1 ‘MEM p st.pc’ >> irule pok_frame >>
      qexistsl_tac [‘hs’, ‘ps’, ‘w’] >>
      ‘∀h. MEM h (phds p) ⇒ h ≠ hd’
        by (rpt strip_tac >> qpat_x_assum ‘¬MEM hd (FLAT _)’ mp_tac >>
            simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘p’ >> gvs[]) >>
      rpt conj_tac >>
      TRY (qpat_x_assum ‘EVERY (pok _ _ _ _) _’ mp_tac >> simp[EVERY_MEM] >> NO_TAC) >>
      TRY (rpt strip_tac >> irule hsame_other >> simp[] >> NO_TAC) >>
      TRY (rpt strip_tac >> first_x_assum drule >> simp[Abbr ‘hd’] >> NO_TAC) >>
      rpt strip_tac >> qpat_x_assum ‘hch _ _ _ _’ mp_tac >> simp[hch_def] >>
      strip_tac >>
      ‘h ≠ hd’ by (first_x_assum drule >> simp[]) >>
      ‘f' ≠ f’ by (strip_tac >> rveq >> imp_res_tac ALOOKUP_MEM >>
                   qpat_x_assum ‘¬MEM f (MAP SND hs.tbl)’ mp_tac >>
                   simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘h’ >> simp[]) >>
      simp[])
  >~ [‘_ = hdl lfd hs.nxt ∨ _’]
  >- (rpt strip_tac
      >- (qexists_tac ‘pnew hd’ >> simp[Abbr ‘hd’])
      >> qpat_x_assum ‘∀h. MEM h (MAP FST hs.tbl) ⇒ _’ drule >> strip_tac >>
      qexists_tac ‘p’ >> simp[])
  >~ [‘(MEM _ (hl_acc_handles _) ∨ _) ⇔ _’]
  >- (gen_tac >>
      qpat_x_assum ‘∀hd. MEM hd (hl_acc_handles ps) ⇔ _’ (qspec_then ‘hd'’ SUBST1_TAC) >>
      rpt (pop_assum kall_tac) >> eq_tac >> rw[] >>
      TRY (qexists_tac ‘p’ >> simp[] >> NO_TAC) >>
      TRY (qexists_tac ‘pnew hd’ >> simp[pnew_def] >> NO_TAC) >>
      gvs[pnew_def] >> metis_tac[]) >>
  gen_tac >>
  qpat_x_assum ‘∀c. MEM c (hl_conn_handles ps) ⇔ _’ (qspec_then ‘c’ SUBST1_TAC) >>
  rpt (pop_assum kall_tac) >> eq_tac >> rw[] >>
  TRY (qexists_tac ‘p’ >> simp[] >> NO_TAC) >> gvs[pnew_def]
QED

(* ------------------------------------------------------------------------
   An action on one pair's handle h0 (channel j0): the world changes only
   at j0, and h0 is kept or closed
   ------------------------------------------------------------------------ *)

Definition wstep_def:
  wstep h0 j0 (w : eworld) (hs : ehstate) (w1 : eworld) (hs1 : ehstate) ⇔
    w1.takes = w.takes ∧ w1.alloc = w.alloc ∧ w1.reserved = w.reserved ∧
    w1.listening = w.listening ∧ LENGTH w1.chans = LENGTH w.chans ∧
    (∀j. j ≠ j0 ⇒ EL j w1.chans = EL j w.chans) ∧ hs1.nxt = hs.nxt ∧
    (w1.open_fds = w.open_fds ∧ hs1.tbl = hs.tbl ∨
     ∃f0. ALOOKUP hs.tbl h0 = SOME f0 ∧ w1.open_fds = ADELKEY f0 w.open_fds ∧
          hs1.tbl = ADELKEY h0 hs.tbl)
End

Theorem ALOOKUP_ADELKEY_other:
  k ≠ k0 ⇒ ALOOKUP (ADELKEY k0 l) k = ALOOKUP l k
Proof
  simp[ALOOKUP_ADELKEY]
QED

Theorem wstep_hch:
  wstep h0 j0 w hs w1 hs1 ∧ hch w hs h0 j0 ∧ hch w hs h j ∧ h ≠ h0 ∧
  ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds) ⇒
  hch w1 hs1 h j ∧ j ≠ j0 ∧ EL j w1.chans = EL j w.chans
Proof
  simp[hch_def, wstep_def] >> strip_tac >>
  ‘f ≠ f'’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  ‘j ≠ j0’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SND_inj]) >>
  gvs[ALOOKUP_ADELKEY_other]
QED

Theorem wstep_tbl:
  wstep h0 j0 w hs w1 hs1 ⇒
  (∀h. h ≠ h0 ⇒ (MEM h (MAP FST hs1.tbl) ⇔ MEM h (MAP FST hs.tbl))) ∧
  (MEM h0 (MAP FST hs1.tbl) ⇒ MEM h0 (MAP FST hs.tbl))
Proof
  simp[wstep_def] >> strip_tac >> gvs[MAP_FST_ADELKEY, MEM_FILTER]
QED

Theorem phds_disjoint:
  ALL_DISTINCT (FLAT (MAP phds pc)) ∧ i < LENGTH pc ∧ i' < LENGTH pc ∧ i ≠ i' ∧
  MEM h (phds (EL i pc)) ⇒ ¬MEM h (phds (EL i' pc))
Proof
  rw[] >> fs[ALL_DISTINCT_FLAT, EL_MAP] >>
  Cases_on ‘i < i'’
  >- (first_x_assum (qspecl_then [‘i’, ‘i'’] mp_tac) >> simp[EL_MAP] >> metis_tac[])
  >> first_x_assum (qspecl_then [‘i'’, ‘i’] mp_tac) >> simp[EL_MAP] >> metis_tac[]
QED

Theorem wstep_fds:
  wstep h0 j0 w hs w1 hs1 ∧ ALL_DISTINCT (MAP FST hs.tbl) ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧
  ALL_DISTINCT (MAP FST w.open_fds) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
  (∀f. MEM f (MAP FST w.open_fds) ⇔ MEM f (MAP SND hs.tbl)) ⇒
  (∀f. MEM f (MAP FST w1.open_fds) ⇒ MEM f (MAP FST w.open_fds)) ∧
  (∀j. MEM j (MAP SND w1.open_fds) ⇒ MEM j (MAP SND w.open_fds)) ∧
  ALL_DISTINCT (MAP FST w1.open_fds) ∧ ALL_DISTINCT (MAP SND w1.open_fds) ∧
  ALL_DISTINCT (MAP FST hs1.tbl) ∧ ALL_DISTINCT (MAP SND hs1.tbl) ∧
  (∀f. MEM f (MAP FST w1.open_fds) ⇔ MEM f (MAP SND hs1.tbl))
Proof
  simp[wstep_def] >> strip_tac >> simp[] >>
  simp[ALL_DISTINCT_ADELKEY, MAP_FST_ADELKEY, MEM_FILTER] >>
  rpt conj_tac
  >- (simp[ADELKEY_def, MEM_MAP, MEM_FILTER, PULL_EXISTS] >> rpt strip_tac >>
      qexists_tac ‘y’ >> simp[])
  >> drule_at (Pos last) MEM_SND_ADELKEY >> (impl_tac >- simp[]) >> strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem queue_keep:
  EVERY (λj. j < LENGTH w.chans ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut ∧
             ¬MEM j (MAP SND w.open_fds)) q ∧
  MEM j0 (MAP SND w.open_fds) ∧ LENGTH w1.chans = LENGTH w.chans ∧
  (∀j. j ≠ j0 ⇒ EL j w1.chans = EL j w.chans) ∧
  (∀j. MEM j (MAP SND w1.open_fds) ⇒ MEM j (MAP SND w.open_fds)) ⇒
  EVERY (λj. j < LENGTH w1.chans ∧ (EL j w1.chans).status = Up ∧ ¬(EL j w1.chans).shut ∧
             ¬MEM j (MAP SND w1.open_fds)) q
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  ‘j ≠ j0’ by (strip_tac >> gvs[]) >> gvs[] >> strip_tac >> res_tac
QED

Theorem MEM_LUPDATE_new:
  i < LENGTH l ⇒ MEM x (LUPDATE x i l)
Proof
  simp[MEM_EL, EL_LUPDATE] >> strip_tac >> qexists_tac ‘i’ >> simp[]
QED

Theorem MEM_LUPDATE_old:
  n < LENGTH l ∧ n ≠ i ∧ y = EL n l ⇒ MEM y (LUPDATE x i l)
Proof
  simp[MEM_EL, EL_LUPDATE] >> strip_tac >> qexists_tac ‘n’ >> simp[]
QED

Theorem MAP_phds_LUPDATE:
  i < LENGTH pc ∧ p'.fh = (EL i pc).fh ∧ p'.bh = (EL i pc).bh ⇒
  MAP phds (LUPDATE p' i pc) = MAP phds pc
Proof
  strip_tac >> simp[LUPDATE_MAP] >>
  ‘phds p' = EL i (MAP phds pc)’ by simp[EL_MAP, phds_def] >>
  simp[LUPDATE_SAME]
QED

Theorem hl_one_other:
  ((∃k. x = ERead h0 k) ∨ (∃bs. x = EWrite h0 bs)) ∧ h ≠ h0 ⇒ hsame h ps (ps ++ [(x, r)])
Proof
  strip_tac >> irule hsame_other >> gvs[]
QED

Theorem pok_others:
  EVERY (pok w hs ps rdy) pc ∧ ALL_DISTINCT (FLAT (MAP phds pc)) ∧ i < LENGTH pc ∧
  MEM h0 (phds (EL i pc)) ∧ hch w hs h0 j0 ∧ wstep h0 j0 w hs w1 hs1 ∧
  ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
  ((∃k. x = ERead h0 k) ∨ (∃bs. x = EWrite h0 bs)) ∧ pok w1 hs1 (ps ++ [(x, r)]) rdy p' ⇒
  EVERY (pok w1 hs1 (ps ++ [(x, r)]) rdy) (LUPDATE p' i pc)
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  simp[EVERY_EL, EL_LUPDATE] >> rpt strip_tac >> Cases_on ‘i = n’ >- gvs[] >>
  simp[] >>
  ‘pok w hs ps rdy (EL n pc)’ by fs[EVERY_EL] >>
  ‘¬MEM h0 (phds (EL n pc))’ by (irule phds_disjoint >> simp[] >> qexists_tac ‘i’ >> simp[]) >>
  ‘∀h. MEM h (phds (EL n pc)) ⇒ h ≠ h0’ by (rpt strip_tac >> fs[]) >>
  irule pok_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt strip_tac >> irule hl_one_other >> qexists_tac ‘h0’ >> res_tac >> simp[] >> NO_TAC) >>
  TRY (rpt strip_tac >> ‘h ≠ h0’ by res_tac >> drule_all wstep_hch >> simp[] >> NO_TAC) >>
  rpt strip_tac >> ‘h ≠ h0’ by res_tac >> drule wstep_tbl >> strip_tac >>
  qpat_x_assum ‘∀h. h ≠ h0 ⇒ _’ (qspec_then ‘h’ mp_tac) >> simp[]
QED

(* MAIN of this part: an action on pair i's handle h0 that only touches
   h0's channel j0, keeps the pair's handles, and leaves the pair good,
   keeps the relation *)
Theorem prel_step_pair:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ MEM h0 (popen (EL i st.pc)) ∧
  hch w hs h0 j0 ∧ wstep h0 j0 w hs w1 hs1 ∧
  ((∃k. x = ERead h0 k) ∨ (∃bs. x = EWrite h0 bs)) ∧
  p'.fh = (EL i st.pc).fh ∧ p'.bh = (EL i st.pc).bh ∧
  (∀h. MEM h (popen (EL i st.pc)) ∧ MEM h (MAP FST hs1.tbl) ⇒ MEM h (popen p')) ∧
  pok w1 hs1 (ps ++ [(x, r)]) rdy p' ⇒
  prel lfd (st with pc := LUPDATE p' i st.pc) rdy (ps ++ [(x, r)]) w1 hs1
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘MAP phds (LUPDATE p' i st.pc) = MAP phds st.pc’ by (irule MAP_phds_LUPDATE >> simp[]) >>
  ‘MEM h0 (phds (EL i st.pc))’ by metis_tac[popen_phds] >>
  ‘MEM h0 (FLAT (MAP phds st.pc))’
    by (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘EL i st.pc’ >> simp[EL_MEM]) >>
  ‘∀h. h ≠ h0 ⇒ hl_sent h [(x, r)] = [] ∧ hl_read h [(x, r)] = [] ∧ ¬hl_eof h [(x, r)] ∧
                 ¬hl_refused h [(x, r)] ∧ ¬hl_up h [(x, r)]’
    by (rpt gen_tac >> strip_tac >>
        qpat_x_assum ‘(∃k. _) ∨ _’ strip_assume_tac >> qpat_x_assum ‘x = _’ SUBST_ALL_TAC >>
        Cases_on ‘r’ >> simp[] >> TRY (rename1 ‘EGot oo’ >> Cases_on ‘oo’ >> simp[])) >>
  ‘hl_acc_handles [(x, r)] = [] ∧ hl_conn_handles [(x, r)] = []’
    by (qpat_x_assum ‘(∃k. _) ∨ _’ strip_assume_tac >> qpat_x_assum ‘x = _’ SUBST_ALL_TAC >> Cases_on ‘r’ >> simp[]) >>
  ‘ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds)’ by fs[prel_def] >>
  ‘∃f0. ALOOKUP hs.tbl h0 = SOME f0 ∧ ALOOKUP w.open_fds f0 = SOME j0 ∧ j0 < LENGTH w.chans’
    by fs[hch_def] >>
  ‘MEM j0 (MAP SND w.open_fds)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  qpat_x_assum ‘prel _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [prel_def]) >>
  ‘w1.takes = w.takes ∧ w1.alloc = w.alloc ∧ w1.reserved = w.reserved ∧
   w1.listening = w.listening ∧ LENGTH w1.chans = LENGTH w.chans ∧
   (∀j. j ≠ j0 ⇒ EL j w1.chans = EL j w.chans) ∧ hs1.nxt = hs.nxt’ by fs[wstep_def] >>
  ‘(∀f. MEM f (MAP FST w1.open_fds) ⇒ MEM f (MAP FST w.open_fds)) ∧
   (∀j. MEM j (MAP SND w1.open_fds) ⇒ MEM j (MAP SND w.open_fds)) ∧
   ALL_DISTINCT (MAP FST w1.open_fds) ∧ ALL_DISTINCT (MAP SND w1.open_fds) ∧
   ALL_DISTINCT (MAP FST hs1.tbl) ∧ ALL_DISTINCT (MAP SND hs1.tbl) ∧
   (∀f. MEM f (MAP FST w1.open_fds) ⇔ MEM f (MAP SND hs1.tbl))’
    by (drule wstep_fds >> (impl_tac >- simp[]) >> simp[]) >>
  qabbrev_tac ‘st' = st with pc := LUPDATE p' i st.pc’ >>
  ‘st'.pc = LUPDATE p' i st.pc’ by simp[Abbr ‘st'’] >>
  ‘LENGTH st'.pc = LENGTH st.pc’ by simp[] >>
  ‘FLAT (MAP phds st'.pc) = FLAT (MAP phds st.pc)’ by simp[] >>
  ‘∀q'. MEM q' st'.pc ⇔ ∃n. n < LENGTH st.pc ∧ q' = if n = i then p' else EL n st.pc’
    by (simp[MEM_EL, EL_LUPDATE] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
        qexists_tac ‘n’ >> simp[]) >>
  (* the listener's queue *)
  ‘EVERY (λj. j < LENGTH w1.chans ∧ (EL j w1.chans).status = Up ∧
              ¬(EL j w1.chans).shut ∧ ¬MEM j (MAP SND w1.open_fds)) q’
    by (irule queue_keep >> qexistsl_tac [‘j0’, ‘w’] >> simp[]) >>
  ‘EVERY (λj. j < LENGTH w1.chans) (MAP SND w1.open_fds)’
    by (qpat_x_assum ‘EVERY _ (MAP SND w.open_fds)’ mp_tac >> simp[EVERY_MEM] >>
        rpt strip_tac >> res_tac >> simp[]) >>
  ‘¬MEM lfd (MAP FST w1.open_fds)’ by (strip_tac >> res_tac) >>
  ‘∀h. MEM h (MAP FST hs1.tbl) ⇒ ∃p. MEM p st'.pc ∧ MEM h (popen p)’
    by (rpt strip_tac >>
        ‘MEM h (MAP FST hs.tbl)’
          by (drule wstep_tbl >> strip_tac >> Cases_on ‘h = h0’
              >- (pop_assum SUBST_ALL_TAC >> qpat_x_assum ‘MEM h0 _ ⇒ _’ irule >> simp[])
              >> qpat_x_assum ‘∀h. h ≠ h0 ⇒ (MEM h _ ⇔ _)’ (qspec_then ‘h’ mp_tac) >> simp[]) >>
        qpat_x_assum ‘∀h. MEM h (MAP FST hs.tbl) ⇒ _’ drule >> strip_tac >>
        qpat_x_assum ‘MEM p st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
        Cases_on ‘n = i’
        >- (qexists_tac ‘p'’ >> conj_tac >- (simp[] >> qexists_tac ‘i’ >> simp[]) >>
            qpat_x_assum ‘∀h. MEM h (popen _) ∧ _ ⇒ MEM h (popen p')’ irule >> gvs[])
        >> qexists_tac ‘p’ >> simp[] >> qexists_tac ‘n’ >> simp[]) >>
  ‘EVERY (pok w1 hs1 (ps ++ [(x, r)]) rdy) st'.pc’
    by (simp[] >> mp_tac (Q.INST [‘pc’ |-> ‘st.pc’] pok_others) >> impl_tac >- simp[] >> simp[]) >>
  ‘∀h. hl_sent h (ps ++ [(x, r)]) ≠ [] ∨ hl_read h (ps ++ [(x, r)]) ≠ [] ∨
       hl_eof h (ps ++ [(x, r)]) ∨ hl_refused h (ps ++ [(x, r)]) ∨ hl_up h (ps ++ [(x, r)]) ⇒
       MEM h (FLAT (MAP phds st.pc))’
    by (rpt gen_tac >> Cases_on ‘h = h0’ >- simp[] >>
        qpat_x_assum ‘∀h. h ≠ h0 ⇒ hl_sent _ _ = _ ∧ _’ (qspec_then ‘h’ mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
        asm_rewrite_tac [hl_APPEND, hl_up_APPEND, APPEND_NIL] >> disch_then assume_tac >>
        qpat_x_assum ‘∀h. hl_sent h ps ≠ [] ∨ _ ⇒ _’ irule >> fs[]) >>
  ‘hl_acc_handles (ps ++ [(x, r)]) = hl_acc_handles ps ∧
   hl_conn_handles (ps ++ [(x, r)]) = hl_conn_handles ps’
    by (REWRITE_TAC [CONJUNCT1 hl_acc_APPEND, hl_APPEND] >> asm_rewrite_tac [APPEND_NIL]) >>
  ‘∀hd. MEM hd (hl_acc_handles (ps ++ [(x, r)])) ⇔ ∃p. MEM p st'.pc ∧ p.fh = hd’
    by (gen_tac >> asm_rewrite_tac [] >>
        qpat_x_assum ‘∀hd. MEM hd (hl_acc_handles ps) ⇔ _’ (qspec_then ‘hd’ SUBST1_TAC) >>
        eq_tac >> strip_tac
        >- (qpat_x_assum ‘MEM p st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
            qexists_tac ‘if n = i then p' else EL n st.pc’ >>
            conj_tac >- (qexists_tac ‘n’ >> simp[]) >> rw[] >> gvs[])
        >> qexists_tac ‘EL n st.pc’ >> simp[EL_MEM] >> Cases_on ‘n = i’ >> gvs[]) >>
  ‘∀c. MEM c (hl_conn_handles (ps ++ [(x, r)])) ⇔ ∃p. MEM p st'.pc ∧ p.bh = SOME c’
    by (gen_tac >> asm_rewrite_tac [] >>
        qpat_x_assum ‘∀c. MEM c (hl_conn_handles ps) ⇔ _’ (qspec_then ‘c’ SUBST1_TAC) >>
        eq_tac >> strip_tac
        >- (qpat_x_assum ‘MEM p st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
            qexists_tac ‘if n = i then p' else EL n st.pc’ >>
            conj_tac >- (qexists_tac ‘n’ >> simp[]) >> rw[] >> gvs[])
        >> qexists_tac ‘EL n st.pc’ >> simp[EL_MEM] >> Cases_on ‘n = i’ >> gvs[]) >>
  REWRITE_TAC [prel_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (asm_simp_tac (srw_ss()) [] >> NO_TAC) >>
  TRY (qpat_x_assum ‘FLAT (MAP phds st'.pc) = _’ SUBST1_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [‘a’, ‘q’] >> asm_simp_tac (srw_ss()) []
QED

(* ------------------------------------------------------------------------
   The pair's actions
   ------------------------------------------------------------------------ *)

Theorem hch_inj:
  hch w hs h1 j ∧ hch w hs h2 j ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧
  ALL_DISTINCT (MAP SND w.open_fds) ⇒ h1 = h2
Proof
  rw[hch_def] >> ‘f = f'’ by metis_tac[ALOOKUP_SND_inj] >> gvs[] >>
  metis_tac[ALOOKUP_SND_inj]
QED

Theorem phds_distinct:
  ALL_DISTINCT (FLAT (MAP phds pc)) ∧ MEM p pc ⇒ ALL_DISTINCT (phds p)
Proof
  rw[ALL_DISTINCT_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem prel_pok:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ⇒ pok w hs ps rdy (EL i st.pc)
Proof
  rw[prel_def, EVERY_EL]
QED

Theorem prel_pair_distinct:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ⇒
  c ≠ (EL i st.pc).fh
Proof
  rw[prel_def] >> ‘MEM (EL i st.pc) st.pc’ by simp[EL_MEM] >>
  drule_all phds_distinct >> simp[phds_def]
QED

(* The write to the front: all of bq is taken *)
Theorem prel_write_front:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ (EL i st.pc).fo ∧ (EL i st.pc).bq ≠ [] ⇒
  ∃w1. ehdo lfd v (w, hs) (EWrite (EL i st.pc).fh (EL i st.pc).bq) =
         SOME (EWrote (LENGTH (EL i st.pc).bq), (w1, hs)) ∧
       prel lfd (pupd st [(i, EWrite (EL i st.pc).fh (EL i st.pc).bq)]
                         [EWrote (LENGTH (EL i st.pc).bq)]) rdy
         (ps ++ [(EWrite (EL i st.pc).fh (EL i st.pc).bq, EWrote (LENGTH (EL i st.pc).bq))])
         w1 hs
Proof
  strip_tac >> qabbrev_tac ‘p = EL i st.pc’ >>
  ‘pok w hs ps rdy p’ by (simp[Abbr ‘p’] >> irule prel_pok >> metis_tac[]) >>
  ‘∃c. p.bh = SOME c’ by (Cases_on ‘p.bh’ >> fs[pok_def]) >>
  ‘c ≠ p.fh’ by (simp[Abbr ‘p’] >> irule prel_pair_distinct >> metis_tac[]) >>
  ‘∃j. hch w hs p.fh j ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut’
    by fs[pok_def] >>
  ‘w.takes = (λj b n. n) ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds)’
    by fs[prel_def] >>
  ‘∃f. ALOOKUP hs.tbl p.fh = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans’
    by fs[hch_def] >>
  drule_all ehdo_write_up >> disch_then (qspecl_then [‘v’, ‘lfd’, ‘p.bq’] assume_tac) >>
  simp[] >>
  qabbrev_tac ‘w1 = upd_chan j (λc. c with <| sent := c.sent ++ p.bq;
                                              inflight := c.inflight + LENGTH p.bq |>) w’ >>
  ‘pres p (EWrite p.fh p.bq) (EWrote (LENGTH p.bq)) = p with bq := []’
    by simp[pres_def] >>
  simp[] >>
  ‘wstep p.fh j w hs w1 hs’
    by simp[wstep_def, Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >>
  ‘∀j'. j' ≠ j ⇒ EL j' w1.chans = EL j' w.chans’ by simp[Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >>
  ‘(EL j w1.chans).status = Up ∧ ¬(EL j w1.chans).shut ∧ LENGTH w1.chans = LENGTH w.chans ∧
   w1.open_fds = w.open_fds’
    by simp[Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >>
  ‘pok w1 hs (ps ++ [(EWrite p.fh p.bq, EWrote (LENGTH p.bq))]) rdy (p with bq := [])’
    by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >>
        ‘hl_sent c [(EWrite p.fh p.bq, EWrote (LENGTH p.bq))] = [] ∧
         hl_read c [(EWrite p.fh p.bq, EWrote (LENGTH p.bq))] = [] ∧
         hl_read p.fh [(EWrite p.fh p.bq, EWrote (LENGTH p.bq))] = [] ∧
         hl_sent p.fh [(EWrite p.fh p.bq, EWrote (LENGTH p.bq))] = p.bq’
          by simp[TAKE_LENGTH_ID] >>
        gvs[] >> rpt conj_tac >>
        TRY (qexists_tac ‘j’ >> simp[hch_def] >> qexists_tac ‘f’ >> simp[] >> NO_TAC) >>
        strip_tac >>
        qpat_x_assum ‘¬hl_eof c ps ∧ ¬hl_refused c ps ⇒ _’ mp_tac >>
        (impl_tac >- simp[]) >> strip_tac >>
        rename1 ‘hch w hs c jc’ >> qexists_tac ‘jc’ >>
        ‘jc ≠ j’ by (strip_tac >> qpat_x_assum ‘c ≠ p.fh’ mp_tac >> simp[] >>
                     irule hch_inj >> qexistsl_tac [‘hs’, ‘j’, ‘w’] >> gvs[]) >>
        qpat_x_assum ‘hch w hs c jc’ (strip_assume_tac o REWRITE_RULE [hch_def]) >>
        simp[hch_def] >> rpt strip_tac >> gvs[]) >>
  ‘MEM p.fh (popen p)’ by simp[popen_def] >>
  irule prel_step_pair >> rpt conj_tac >>
  TRY (simp[popen_def] >> NO_TAC) >>
  TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> simp[Abbr ‘w1’] >> NO_TAC) >>
  qexistsl_tac [‘p.fh’, ‘hs’, ‘j’, ‘w’] >> simp[] >>
  qpat_x_assum ‘wstep _ _ _ _ w1 _’ mp_tac >> simp[Abbr ‘w1’]
QED

(* The write to the backend: it has answered a read, so it is Up; all of fq
   is taken *)
Theorem prel_write_back:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧
  (EL i st.pc).bo ∧ (EL i st.pc).fq ≠ [] ⇒
  ∃w1. ehdo lfd v (w, hs) (EWrite c (EL i st.pc).fq) =
         SOME (EWrote (LENGTH (EL i st.pc).fq), (w1, hs)) ∧
       prel lfd (pupd st [(i, EWrite c (EL i st.pc).fq)] [EWrote (LENGTH (EL i st.pc).fq)]) rdy
         (ps ++ [(EWrite c (EL i st.pc).fq, EWrote (LENGTH (EL i st.pc).fq))]) w1 hs
Proof
  strip_tac >> qabbrev_tac ‘p = EL i st.pc’ >>
  ‘pok w hs ps rdy p’ by (simp[Abbr ‘p’] >> irule prel_pok >> metis_tac[]) >>
  ‘c ≠ p.fh’ by (simp[Abbr ‘p’] >> irule prel_pair_distinct >> metis_tac[]) >>
  ‘p.bup’
    by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >>
        ‘hl_read p.fh ps ≠ []’ by (strip_tac >> gvs[]) >> gvs[]) >>
  ‘∃j. hch w hs c j ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut’
    by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
        qexists_tac ‘j’ >> gvs[]) >>
  ‘w.takes = (λj b n. n) ∧ ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds)’
    by fs[prel_def] >>
  ‘∃f. ALOOKUP hs.tbl c = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans’
    by fs[hch_def] >>
  drule_all ehdo_write_up >> disch_then (qspecl_then [‘v’, ‘lfd’, ‘p.fq’] assume_tac) >>
  simp[] >>
  qabbrev_tac ‘w1 = upd_chan j (λc. c with <| sent := c.sent ++ p.fq;
                                              inflight := c.inflight + LENGTH p.fq |>) w’ >>
  ‘pres p (EWrite c p.fq) (EWrote (LENGTH p.fq)) = p with fq := []’
    by simp[pres_def] >>
  simp[] >>
  ‘wstep c j w hs w1 hs’
    by simp[wstep_def, Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >>
  ‘∀j'. j' ≠ j ⇒ EL j' w1.chans = EL j' w.chans’ by simp[Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >>
  ‘(EL j w1.chans).status = Up ∧ ¬(EL j w1.chans).shut ∧ LENGTH w1.chans = LENGTH w.chans ∧
   w1.open_fds = w.open_fds’
    by simp[Abbr ‘w1’, upd_chan_def, EL_LUPDATE] >>
  ‘pok w1 hs (ps ++ [(EWrite c p.fq, EWrote (LENGTH p.fq))]) rdy (p with fq := [])’
    by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >>
        ‘hl_sent p.fh [(EWrite c p.fq, EWrote (LENGTH p.fq))] = [] ∧
         hl_read p.fh [(EWrite c p.fq, EWrote (LENGTH p.fq))] = [] ∧
         hl_read c [(EWrite c p.fq, EWrote (LENGTH p.fq))] = [] ∧
         hl_sent c [(EWrite c p.fq, EWrote (LENGTH p.fq))] = p.fq’
          by simp[TAKE_LENGTH_ID] >>
        gvs[] >> rpt conj_tac >>
        TRY (qexists_tac ‘j’ >> simp[hch_def] >> qexists_tac ‘f’ >> simp[] >> NO_TAC) >>
        strip_tac >> fs[] >>
        rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
        ‘jf ≠ j’ by (strip_tac >> qpat_x_assum ‘c ≠ p.fh’ mp_tac >> simp[] >>
                     irule hch_inj >> qexistsl_tac [‘hs’, ‘j’, ‘w’] >> gvs[]) >>
        qpat_x_assum ‘hch w hs p.fh jf’ (strip_assume_tac o REWRITE_RULE [hch_def]) >>
        simp[hch_def] >> rpt strip_tac >> gvs[]) >>
  ‘MEM c (popen p)’ by simp[popen_def] >>
  irule prel_step_pair >> rpt conj_tac >>
  TRY (simp[popen_def] >> NO_TAC) >>
  TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> simp[Abbr ‘w1’] >> NO_TAC) >>
  qexistsl_tac [‘c’, ‘hs’, ‘j’, ‘w’] >> simp[] >>
  qpat_x_assum ‘wstep _ _ _ _ w1 _’ mp_tac >> simp[Abbr ‘w1’]
QED

Theorem pread_bounds[simp]:
  0 < pread ∧ pread < 256 ** 8
Proof
  simp[pread_def]
QED

Theorem wframe_wstep:
  wframe j w w1 ∧ hs1.nxt = hs.nxt ∧
  (w1.open_fds = w.open_fds ∧ hs1.tbl = hs.tbl ∨
   ∃f0. ALOOKUP hs.tbl h0 = SOME f0 ∧ w1.open_fds = ADELKEY f0 w.open_fds ∧
        hs1.tbl = ADELKEY h0 hs.tbl) ⇒
  wstep h0 j w hs w1 hs1
Proof
  rw[wframe_def, wstep_def] >> metis_tac[]
QED

(* The other handle of a pair keeps its fd and channel across an action on
   h0 at channel j that touches only channel j and maybe closes h0 *)
Theorem hch_keep_other:
  hch w hs h jh ∧ hch w hs h0 j ∧ h ≠ h0 ∧ wstep h0 j w hs w1 hs1 ∧
  ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds) ⇒
  hch w1 hs1 h jh ∧ jh ≠ j ∧ EL jh w1.chans = EL jh w.chans
Proof
  strip_tac >> drule_all wstep_hch >> simp[]
QED

(* The read of the front (its backend has answered a read): data goes to
   fq; EOF closes it; would-block changes nothing *)
Theorem prel_read_front:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ (EL i st.pc).fo ∧
  (EL i st.pc).bh = SOME c ∧ (EL i st.pc).bup ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) (ERead (EL i st.pc).fh pread) = SOME (r, (w1, hs1)) ∧
    prel lfd (pupd st [(i, ERead (EL i st.pc).fh pread)] [r]) rdy
      (ps ++ [(ERead (EL i st.pc).fh pread, r)]) w1 hs1
Proof
  strip_tac >> qabbrev_tac ‘p = EL i st.pc’ >>
  ‘pok w hs ps rdy p’ by (simp[Abbr ‘p’] >> irule prel_pok >> metis_tac[]) >>
  ‘c ≠ p.fh’ by (simp[Abbr ‘p’] >> irule prel_pair_distinct >> metis_tac[]) >>
  ‘∃j. hch w hs p.fh j ∧ (EL j w.chans).status = Up ∧ ¬(EL j w.chans).shut’
    by fs[pok_def] >>
  ‘ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
   ALL_DISTINCT (MAP FST hs.tbl) ∧ ALL_DISTINCT (MAP FST w.open_fds)’ by fs[prel_def] >>
  ‘∃f. ALOOKUP hs.tbl p.fh = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans’
    by fs[hch_def] >>
  ‘0 < pread ∧ pread < 256 ** 8’ by simp[] >>
  drule_all ehdo_read >>
  disch_then (qspecl_then [‘v’, ‘lfd’]
    (qx_choosel_then [‘r’, ‘w1’, ‘hs1’]
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
  qexistsl_tac [‘r’, ‘w1’, ‘hs1’] >> simp[] >>
  ‘MEM p.fh (popen p)’ by simp[popen_def] >>
  ‘hl_sent c [(ERead p.fh pread, r)] = [] ∧ hl_read c [(ERead p.fh pread, r)] = [] ∧
   ¬hl_eof c [(ERead p.fh pread, r)] ∧ ¬hl_refused c [(ERead p.fh pread, r)] ∧
   ¬hl_up c [(ERead p.fh pread, r)] ∧ hl_sent p.fh [(ERead p.fh pread, r)] = [] ∧
   ¬hl_refused p.fh [(ERead p.fh pread, r)] ∧ ¬hl_up c [(ERead p.fh pread, r)]’
    by (Cases_on ‘r’ >> simp[] >> TRY (rename1 ‘EGot oo’ >> Cases_on ‘oo’) >> simp[] >>
        gvs[]) >>
  qpat_x_assum ‘_ ∨ _ ∨ _ ∨ _’ strip_assume_tac
  >- gvs[]
  >- ((* data *)
      qabbrev_tac ‘d = TAKE pread (EL j w.chans).inbox’ >>
      ‘d ≠ []’ by (simp[Abbr ‘d’] >> Cases_on ‘(EL j w.chans).inbox’ >> gvs[]) >>
      ‘pres p (ERead p.fh pread) r = p with fq := p.fq ++ d’
        by (gvs[] >> Cases_on ‘d’ >> gvs[pres_def]) >>
      ‘wstep p.fh j w hs w1 hs1’ by (irule wframe_wstep >> gvs[]) >>
      ‘hl_read p.fh [(ERead p.fh pread, r)] = d ∧ ¬hl_eof p.fh [(ERead p.fh pread, r)]’
        by (gvs[] >> Cases_on ‘d’ >> gvs[]) >>
      ‘(EL j w1.chans).status = Up ∧ ¬(EL j w1.chans).shut ∧ LENGTH w1.chans = LENGTH w.chans’
        by fs[wframe_def] >>
      ‘hch w1 hs1 p.fh j’ by (gvs[hch_def] >> fs[wframe_def]) >>
      ‘pok w1 hs1 (ps ++ [(ERead p.fh pread, r)]) rdy (p with fq := p.fq ++ d)’
        by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
            rpt conj_tac >>
            TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC) >>
            strip_tac >>
            qpat_x_assum ‘¬hl_eof c ps ∧ ¬hl_refused c ps ⇒ _’ mp_tac >>
            (impl_tac >- simp[]) >> strip_tac >>
            rename1 ‘hch w hs c jc’ >> qexists_tac ‘jc’ >>
            mp_tac (Q.INST [‘h’ |-> ‘c’, ‘jh’ |-> ‘jc’, ‘h0’ |-> ‘p.fh’, ‘hs1’ |-> ‘hs’] hch_keep_other) >>
            (impl_tac >- simp[]) >> strip_tac >> gvs[]) >>
      irule prel_step_pair >> rpt conj_tac >>
      TRY (simp[popen_def] >> NO_TAC) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> gvs[] >> NO_TAC) >>
      qexistsl_tac [‘p.fh’, ‘hs’, ‘j’, ‘w’] >> gvs[])
  >- ((* EOF: the front is closed *)
      ‘pres p (ERead p.fh pread) r = p with fo := F’ by gvs[pres_def] >>
      ‘wstep p.fh j w hs w1 hs1’
        by (irule wframe_wstep >> gvs[eh_del_def] >> disj2_tac >> qexists_tac ‘f’ >> simp[]) >>
      ‘hl_read p.fh [(ERead p.fh pread, r)] = [] ∧ hl_eof p.fh [(ERead p.fh pread, r)]’
        by gvs[] >>
      ‘hs1.tbl = ADELKEY p.fh hs.tbl’ by gvs[eh_del_def] >>
      ‘¬MEM p.fh (MAP FST hs1.tbl)’ by simp[MAP_FST_ADELKEY, MEM_FILTER] >>
      ‘∀h. ¬MEM h (MAP FST hs.tbl) ⇒ ¬MEM h (MAP FST hs1.tbl)’
        by simp[MAP_FST_ADELKEY, MEM_FILTER] >>
      ‘pok w1 hs1 (ps ++ [(ERead p.fh pread, r)]) rdy (p with fo := F)’
        by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
            rpt conj_tac >>
            TRY (rpt strip_tac >> gvs[MAP_FST_ADELKEY, MEM_FILTER] >> NO_TAC) >>
            strip_tac >>
            qpat_x_assum ‘¬hl_eof c ps ∧ ¬hl_refused c ps ⇒ _’ mp_tac >>
            (impl_tac >- simp[]) >> strip_tac >>
            rename1 ‘hch w hs c jc’ >> qexists_tac ‘jc’ >>
            mp_tac (Q.INST [‘h’ |-> ‘c’, ‘jh’ |-> ‘jc’, ‘h0’ |-> ‘p.fh’,
                            ‘hs1’ |-> ‘eh_del p.fh hs’] hch_keep_other) >>
            (impl_tac >- simp[]) >> strip_tac >> gvs[]) >>
      irule prel_step_pair >> rpt conj_tac >>
      TRY (simp[popen_def] >> rpt strip_tac >> gvs[] >> NO_TAC) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> gvs[] >> NO_TAC) >>
      qexistsl_tac [‘p.fh’, ‘hs’, ‘j’, ‘w’] >> gvs[])
  >> (* would-block: nothing changes *)
  ‘pres p (ERead p.fh pread) r = p’ by gvs[pres_def] >>
  ‘wstep p.fh j w hs w1 hs1’ by (gvs[] >> simp[wstep_def]) >>
  ‘pok w1 hs1 (ps ++ [(ERead p.fh pread, r)]) rdy p’
    by (gvs[] >> qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def]) >>
  irule prel_step_pair >> rpt conj_tac >>
  TRY (simp[popen_def] >> rpt strip_tac >> gvs[] >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> gvs[] >> NO_TAC) >>
  qexistsl_tac [‘p.fh’, ‘hs’, ‘j’, ‘w’] >> gvs[]
QED

(* The read of the backend (not reported ready only if it has answered
   before): refused closes it; otherwise it is Up, data goes to bq, EOF
   closes it *)
Theorem prel_read_back:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧
  (EL i st.pc).bo ∧ (¬(EL i st.pc).bup ⇒ c ∈ rdy) ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) (ERead c pread) = SOME (r, (w1, hs1)) ∧
    prel lfd (pupd st [(i, ERead c pread)] [r]) rdy (ps ++ [(ERead c pread, r)]) w1 hs1
Proof
  strip_tac >> qabbrev_tac ‘p = EL i st.pc’ >>
  ‘pok w hs ps rdy p’ by (simp[Abbr ‘p’] >> irule prel_pok >> metis_tac[]) >>
  ‘c ≠ p.fh’ by (simp[Abbr ‘p’] >> irule prel_pair_distinct >> metis_tac[]) >>
  ‘p.fh ≠ c’ by (strip_tac >> fs[]) >>
  ‘∃j. hch w hs c j ∧ ¬(EL j w.chans).shut ∧
       (p.bup ⇒ (EL j w.chans).status = Up) ∧
       (EL j w.chans).status ≠ Connecting ∧ (EL j w.chans).status ≠ Failed’
    by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
        qexists_tac ‘j’ >> simp[] >> Cases_on ‘p.bup’ >> gvs[] >>
        Cases_on ‘(EL j w.chans).status’ >> gvs[]) >>
  ‘ALL_DISTINCT (MAP SND hs.tbl) ∧ ALL_DISTINCT (MAP SND w.open_fds) ∧
   ALL_DISTINCT (MAP FST hs.tbl) ∧ ALL_DISTINCT (MAP FST w.open_fds)’ by fs[prel_def] >>
  ‘∃f. ALOOKUP hs.tbl c = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans’
    by fs[hch_def] >>
  ‘0 < pread ∧ pread < 256 ** 8’ by simp[] >>
  drule_all ehdo_read >>
  disch_then (qspecl_then [‘v’, ‘lfd’]
    (qx_choosel_then [‘r’, ‘w1’, ‘hs1’]
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
  qexistsl_tac [‘r’, ‘w1’, ‘hs1’] >> simp[] >>
  ‘MEM c (popen p)’ by simp[popen_def] >>
  ‘hl_sent p.fh [(ERead c pread, r)] = [] ∧ hl_read p.fh [(ERead c pread, r)] = [] ∧
   ¬hl_eof p.fh [(ERead c pread, r)] ∧ ¬hl_refused p.fh [(ERead c pread, r)] ∧
   hl_sent c [(ERead c pread, r)] = []’
    by (Cases_on ‘r’ >> simp[] >> TRY (rename1 ‘EGot oo’ >> Cases_on ‘oo’) >> simp[] >>
        gvs[]) >>
  qpat_x_assum ‘_ ∨ _ ∨ _ ∨ _’ strip_assume_tac
  >- ((* refused: closed *)
      ‘pres p (ERead c pread) r = p with bo := F’ by gvs[pres_def] >>
      ‘wstep c j w hs w1 hs1’
        by (irule wframe_wstep >> gvs[eh_del_def] >> disj2_tac >> qexists_tac ‘f’ >> simp[]) >>
      ‘hl_refused c [(ERead c pread, r)] ∧ hl_read c [(ERead c pread, r)] = [] ∧
       ¬hl_up c [(ERead c pread, r)]’ by gvs[] >>
      ‘pok w1 hs1 (ps ++ [(ERead c pread, r)]) rdy (p with bo := F)’
        by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
            rpt conj_tac >>
            TRY (rpt strip_tac >> gvs[MAP_FST_ADELKEY, MEM_FILTER, eh_del_def] >> NO_TAC) >>
            TRY (strip_tac >>
                 qpat_x_assum ‘_ ⇒ ∃j. hch w hs p.fh j ∧ _’ mp_tac >> (impl_tac >- simp[]) >>
                 strip_tac >> rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
                 mp_tac (Q.INST [‘h’ |-> ‘p.fh’, ‘jh’ |-> ‘jf’, ‘h0’ |-> ‘c’, ‘hs1’ |-> ‘eh_del c hs’]
                           hch_keep_other) >>
                 (impl_tac >- simp[]) >> strip_tac >> gvs[] >> NO_TAC) >>
            TRY (rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
                 mp_tac (Q.INST [‘h’ |-> ‘p.fh’, ‘jh’ |-> ‘jf’, ‘h0’ |-> ‘c’, ‘hs1’ |-> ‘eh_del c hs’]
                           hch_keep_other) >>
                 (impl_tac >- simp[]) >> strip_tac >> gvs[] >> NO_TAC) >>
            rpt strip_tac >> gvs[MAP_FST_ADELKEY, MEM_FILTER, eh_del_def]) >>
      irule prel_step_pair >> rpt conj_tac >>
      TRY (simp[popen_def] >> rpt strip_tac >> gvs[eh_del_def, MAP_FST_ADELKEY, MEM_FILTER, popen_def] >> NO_TAC) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> gvs[] >> NO_TAC) >>
      TRY (qexistsl_tac [‘c’, ‘hs’, ‘j’, ‘w’] >> gvs[] >> NO_TAC) >>
      qexistsl_tac [‘hs’, ‘j’, ‘w’] >> gvs[])
  >- ((* data *)
      ‘(EL j w.chans).status = Up’
    by (Cases_on ‘(EL j w.chans).status’ >> gvs[]) >>
      qabbrev_tac ‘d = TAKE pread (EL j w.chans).inbox’ >>
      ‘d ≠ []’ by (simp[Abbr ‘d’] >> Cases_on ‘(EL j w.chans).inbox’ >> gvs[]) >>
      ‘pres p (ERead c pread) r = p with <| bup := T; bq := p.bq ++ d |>’
        by (gvs[] >> Cases_on ‘d’ >> gvs[pres_def]) >>
      ‘wstep c j w hs w1 hs1’ by (irule wframe_wstep >> gvs[]) >>
      ‘hl_read c [(ERead c pread, r)] = d ∧ ¬hl_eof c [(ERead c pread, r)] ∧
       ¬hl_refused c [(ERead c pread, r)] ∧ hl_up c [(ERead c pread, r)]’
        by (gvs[] >> Cases_on ‘d’ >> gvs[]) >>
      ‘(EL j w1.chans).status = Up ∧ ¬(EL j w1.chans).shut ∧ LENGTH w1.chans = LENGTH w.chans’
        by fs[wframe_def] >>
      ‘hch w1 hs1 c j’ by (gvs[hch_def] >> fs[wframe_def]) >>
      ‘pok w1 hs1 (ps ++ [(ERead c pread, r)]) rdy (p with <| bup := T; bq := p.bq ++ d |>)’
        by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
            rpt conj_tac >>
            TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC) >>
            TRY (strip_tac >>
                 qpat_x_assum ‘_ ⇒ ∃j. hch w hs p.fh j ∧ _’ mp_tac >> (impl_tac >- simp[]) >>
                 strip_tac >> rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
                 mp_tac (Q.INST [‘h’ |-> ‘p.fh’, ‘jh’ |-> ‘jf’, ‘h0’ |-> ‘c’, ‘hs1’ |-> ‘hs’]
                           hch_keep_other) >>
                 (impl_tac >- simp[]) >> strip_tac >> gvs[] >> NO_TAC) >>
            TRY (rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
                 mp_tac (Q.INST [‘h’ |-> ‘p.fh’, ‘jh’ |-> ‘jf’, ‘h0’ |-> ‘c’, ‘hs1’ |-> ‘hs’]
                           hch_keep_other) >>
                 (impl_tac >- simp[]) >> strip_tac >> gvs[] >> NO_TAC) >>
            rpt strip_tac >> gvs[]) >>
      irule prel_step_pair >> rpt conj_tac >>
      TRY (simp[popen_def] >> rpt strip_tac >> gvs[eh_del_def, MAP_FST_ADELKEY, MEM_FILTER, popen_def] >> NO_TAC) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> gvs[] >> NO_TAC) >>
      TRY (qexistsl_tac [‘c’, ‘hs’, ‘j’, ‘w’] >> gvs[] >> NO_TAC) >>
      qexistsl_tac [‘hs’, ‘j’, ‘w’] >> gvs[])
  >- ((* EOF: closed *)
      ‘(EL j w.chans).status = Up’
    by (Cases_on ‘(EL j w.chans).status’ >> gvs[]) >>
      ‘pres p (ERead c pread) r = p with <| bo := F; bup := T |>’ by gvs[pres_def] >>
      ‘wstep c j w hs w1 hs1’
        by (irule wframe_wstep >> gvs[eh_del_def] >> disj2_tac >> qexists_tac ‘f’ >> simp[]) >>
      ‘hl_eof c [(ERead c pread, r)] ∧ hl_read c [(ERead c pread, r)] = [] ∧
       hl_up c [(ERead c pread, r)]’ by gvs[] >>
      ‘pok w1 hs1 (ps ++ [(ERead c pread, r)]) rdy (p with <| bo := F; bup := T |>)’
        by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
            rpt conj_tac >>
            TRY (rpt strip_tac >> gvs[MAP_FST_ADELKEY, MEM_FILTER, eh_del_def] >> NO_TAC) >>
            TRY (strip_tac >>
                 qpat_x_assum ‘_ ⇒ ∃j. hch w hs p.fh j ∧ _’ mp_tac >> (impl_tac >- simp[]) >>
                 strip_tac >> rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
                 mp_tac (Q.INST [‘h’ |-> ‘p.fh’, ‘jh’ |-> ‘jf’, ‘h0’ |-> ‘c’, ‘hs1’ |-> ‘eh_del c hs’]
                           hch_keep_other) >>
                 (impl_tac >- simp[]) >> strip_tac >> gvs[] >> NO_TAC) >>
            TRY (rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
                 mp_tac (Q.INST [‘h’ |-> ‘p.fh’, ‘jh’ |-> ‘jf’, ‘h0’ |-> ‘c’, ‘hs1’ |-> ‘eh_del c hs’]
                           hch_keep_other) >>
                 (impl_tac >- simp[]) >> strip_tac >> gvs[] >> NO_TAC) >>
            rpt strip_tac >> gvs[MAP_FST_ADELKEY, MEM_FILTER, eh_del_def]) >>
      irule prel_step_pair >> rpt conj_tac >>
      TRY (simp[popen_def] >> rpt strip_tac >> gvs[eh_del_def, MAP_FST_ADELKEY, MEM_FILTER, popen_def] >> NO_TAC) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> gvs[] >> NO_TAC) >>
      TRY (qexistsl_tac [‘c’, ‘hs’, ‘j’, ‘w’] >> gvs[] >> NO_TAC) >>
      qexistsl_tac [‘hs’, ‘j’, ‘w’] >> gvs[])
  >> (* would-block: it has answered *)
  ‘(EL j w.chans).status = Up’
    by (Cases_on ‘(EL j w.chans).status’ >> gvs[]) >>
  ‘pres p (ERead c pread) r = p with bup := T’ by gvs[pres_def] >>
  ‘wstep c j w hs w1 hs1’ by (gvs[] >> simp[wstep_def]) >>
  ‘hl_read c [(ERead c pread, r)] = [] ∧ ¬hl_eof c [(ERead c pread, r)] ∧
   ¬hl_refused c [(ERead c pread, r)] ∧ hl_up c [(ERead c pread, r)]’ by gvs[] >>
  ‘pok w1 hs1 (ps ++ [(ERead c pread, r)]) rdy (p with bup := T)’
    by (qpat_x_assum ‘pok _ _ _ _ _’ mp_tac >> simp[pok_def] >> strip_tac >> gvs[] >>
        rpt conj_tac >> TRY (qexists_tac ‘j’ >> simp[] >> NO_TAC) >>
        TRY (strip_tac >>
             qpat_x_assum ‘_ ⇒ ∃j. hch w hs p.fh j ∧ _’ mp_tac >> (impl_tac >- simp[]) >>
             strip_tac >> rename1 ‘hch w hs p.fh jf’ >> qexists_tac ‘jf’ >>
             mp_tac (Q.INST [‘h’ |-> ‘p.fh’, ‘jh’ |-> ‘jf’, ‘h0’ |-> ‘c’, ‘hs1’ |-> ‘hs’]
                       hch_keep_other) >>
             (impl_tac >- simp[]) >> strip_tac >> gvs[] >> NO_TAC) >>
        rpt strip_tac >> gvs[]) >>
  irule prel_step_pair >> rpt conj_tac >>
  TRY (simp[popen_def] >> rpt strip_tac >> gvs[eh_del_def, MAP_FST_ADELKEY, MEM_FILTER, popen_def] >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_x_assum ‘pok w1 _ _ _ _’ mp_tac >> gvs[] >> NO_TAC) >>
  TRY (qexistsl_tac [‘c’, ‘hs’, ‘j’, ‘w’] >> gvs[] >> NO_TAC) >>
  qexistsl_tac [‘hs’, ‘j’, ‘w’] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The connect: the pair gets its backend, a new Connecting channel
   ------------------------------------------------------------------------ *)

Theorem LUPDATE_split:
  ∀l i x. i < LENGTH l ⇒ LUPDATE x i l = TAKE i l ++ x :: DROP (SUC i) l
Proof
  Induct >> Cases_on ‘i’ >> simp[LUPDATE_def]
QED

Theorem list_split_at:
  i < LENGTH l ⇒
  l = TAKE i l ++ EL i l :: DROP (SUC i) l ∧
  LUPDATE x i l = TAKE i l ++ x :: DROP (SUC i) l
Proof
  strip_tac >> simp[LUPDATE_split] >>
  ‘DROP i l = EL i l :: DROP (SUC i) l’ by simp[DROP_CONS_EL] >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> pop_assum (SUBST1_TAC o SYM) >> simp[TAKE_DROP]
QED

Theorem phds_LUPDATE_extend:
  i < LENGTH pc ∧ phds p' = phds (EL i pc) ++ [cn] ⇒
  PERM (FLAT (MAP phds (LUPDATE p' i pc))) (cn :: FLAT (MAP phds pc))
Proof
  strip_tac >> drule list_split_at >> disch_then (qspec_then ‘p'’ strip_assume_tac) >>
  qpat_x_assum ‘LUPDATE _ _ _ = _’ SUBST1_TAC >>
  qpat_x_assum ‘pc = _’ (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[FLAT_APPEND] >>
  ONCE_REWRITE_TAC [PERM_SYM] >> simp[PERM_CONS_EQ_APPEND] >>
  qexistsl_tac [‘FLAT (MAP phds (TAKE i pc)) ++ phds (EL i pc)’,
                ‘FLAT (MAP phds (DROP (SUC i) pc))’] >> simp[]
QED

Theorem LENGTH_phds_lt:
  ∀pc. MEM p pc ∧ p.bh = NONE ⇒ LENGTH (FLAT (MAP phds pc)) < 2 * LENGTH pc
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[phds_def]
  >- (qspec_then ‘pc’ mp_tac (Q.GEN ‘pc’ LENGTH_phds_le) >> simp[]) >>
  res_tac >> Cases_on ‘h.bh’ >> simp[]
QED

Theorem prel_connect:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ (EL i st.pc).bh = NONE ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) (EConnect b) = SOME (r, (w1, hs1)) ∧
    prel lfd (pupd st [(i, EConnect b)] [r]) rdy (ps ++ [(EConnect b, r)]) w1 hs1
Proof
  strip_tac >> qabbrev_tac ‘p = EL i st.pc’ >>
  ‘pok w hs ps rdy p’ by (simp[Abbr ‘p’] >> irule prel_pok >> metis_tac[]) >>
  ‘hs.nxt + 1 ≤ cbound’
    by (fs[prel_def] >> mp_tac (Q.INST [‘pc’ |-> ‘st.pc’] LENGTH_phds_le) >>
        ‘MEM p st.pc’ by simp[Abbr ‘p’, EL_MEM] >>
        ‘LENGTH (FLAT (MAP phds st.pc)) < 2 * LENGTH st.pc’
          by (irule LENGTH_phds_lt >> qexists_tac ‘p’ >> simp[]) >>
        simp[]) >>
  simp[ehdo_connect] >>
  IF_CASES_TAC
  >- (‘pres p (EConnect b) (EConnected NONE) = p’ by simp[pres_def] >>
      simp[] >> ‘LUPDATE p i st.pc = st.pc’ by simp[Abbr ‘p’, LUPDATE_SAME] >>
      ‘st with pc := st.pc = st’ by simp[moonshotProxyTheory.pst_component_equality] >>
      simp[] >> irule prel_quiet >> simp[] >> qexists_tac ‘ps’ >> simp[hsame_quiet]) >>
  ‘hs.nxt ≤ cbound’ by simp[] >>
  simp[hdln_lt_cbound] >>
  drule_all prel_fresh >> strip_tac >>
  qabbrev_tac ‘cn = hdl lfd hs.nxt’ >>
  qabbrev_tac ‘f' = w.alloc (LENGTH w.chans) (ep_used w)’ >>
  qabbrev_tac ‘J = LENGTH w.chans’ >>
  ‘LENGTH (ep_used w) < dimword (:64)’ by fs[] >>
  ‘¬MEM f' (ep_used w)’ by fs[prel_def, alloc_ok_def, Abbr ‘f'’] >>
  ‘¬MEM f' (MAP FST w.open_fds) ∧ f' ≠ lfd’
    by (qpat_x_assum ‘¬MEM f' _’ mp_tac >> simp[ep_used_def] >> fs[prel_def]) >>
  ‘pres p (EConnect b) (EConnected (SOME cn)) = p with <| bh := SOME cn; bo := T |>’
    by simp[pres_def] >>
  simp[] >>
  qabbrev_tac ‘p' = p with <| bh := SOME cn; bo := T |>’ >>
  qabbrev_tac ‘w1 = w with <| chans := w.chans ++ [new_chan (SOME b) Connecting];
                              open_fds := (f', J) :: w.open_fds;
                              nconnects := w.nconnects + 1 |>’ >>
  qabbrev_tac ‘hs1 = eh_new lfd f' hs with settling := cn :: hs.settling’ >>
  ‘MEM p st.pc’ by simp[Abbr ‘p’, EL_MEM] >>
  ‘w1.takes = w.takes ∧ w1.alloc = w.alloc ∧ w1.reserved = w.reserved ∧
   w1.listening = w.listening ∧ LENGTH w1.chans = J + 1 ∧
   (∀j. j < J ⇒ EL j w1.chans = EL j w.chans) ∧ EL J w1.chans = new_chan (SOME b) Connecting ∧
   w1.open_fds = (f', J) :: w.open_fds ∧ hs1.tbl = (cn, f') :: hs.tbl ∧ hs1.nxt = hs.nxt + 1’
    by simp[Abbr ‘w1’, Abbr ‘hs1’, eh_new_def, EL_APPEND1, EL_APPEND2, Abbr ‘J’] >>
  ‘phds p' = phds p ++ [cn]’ by simp[Abbr ‘p'’, phds_def] >>
  ‘PERM (FLAT (MAP phds (LUPDATE p' i st.pc))) (cn :: FLAT (MAP phds st.pc))’
    by (irule phds_LUPDATE_extend >> simp[Abbr ‘p’]) >>
  qpat_x_assum ‘prel _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [prel_def]) >>
  ‘∀j. MEM j (MAP SND w.open_fds) ⇒ j < J’
    by (fs[EVERY_MEM, Abbr ‘J’]) >>
  ‘∀h j. hch w hs h j ∧ h ≠ cn ⇒ hch w1 hs1 h j ∧ EL j w1.chans = EL j w.chans’
    by (rpt gen_tac >> simp[hch_def] >> strip_tac >>
        ‘MEM f (MAP FST w.open_fds)’
          by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> qexists_tac ‘(h, f)’ >> simp[]) >>
        ‘f ≠ f'’ by (strip_tac >> fs[]) >>
        ‘j < J’ by simp[Abbr ‘J’] >> simp[]) >>
  qabbrev_tac ‘ps1 = ps ++ [(EConnect b, EConnected (SOME cn))]’ >>
  ‘∀h. hsame h ps ps1’ by simp[Abbr ‘ps1’, hsame_quiet] >>
  ‘hl_acc_handles ps1 = hl_acc_handles ps ∧ hl_conn_handles ps1 = hl_conn_handles ps ++ [cn]’
    by simp[Abbr ‘ps1’] >>
  ‘¬MEM J (MAP SND w.open_fds)’ by (strip_tac >> res_tac >> fs[]) >>
  ‘EVERY (λj. j < LENGTH w1.chans ∧ (EL j w1.chans).status = Up ∧ ¬(EL j w1.chans).shut ∧
              ¬MEM j (MAP SND w1.open_fds)) q’
    by (qpat_x_assum ‘EVERY _ q’ mp_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
        first_x_assum drule >> strip_tac >> ‘j < J’ by simp[Abbr ‘J’] >> simp[]) >>
  ‘ALL_DISTINCT (FLAT (MAP phds (LUPDATE p' i st.pc))) ∧
   LENGTH (FLAT (MAP phds (LUPDATE p' i st.pc))) = hs.nxt + 1 ∧
   ∀h. MEM h (FLAT (MAP phds (LUPDATE p' i st.pc))) ⇔ h = cn ∨ MEM h (FLAT (MAP phds st.pc))’
    by (rpt conj_tac
        >- (drule ALL_DISTINCT_PERM >> simp[])
        >- (drule PERM_LENGTH >> simp[])
        >> drule PERM_MEM_EQ >> simp[]) >>
  ‘∀q'. MEM q' (LUPDATE p' i st.pc) ⇔
        ∃n. n < LENGTH st.pc ∧ q' = if n = i then p' else EL n st.pc’
    by (simp[MEM_EL, EL_LUPDATE] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
        qexists_tac ‘n’ >> simp[]) >>
  ‘pok w1 hs1 ps1 rdy p'’
    by (qpat_x_assum ‘pok _ _ _ _ p’ mp_tac >>
        ‘MEM p.fh (FLAT (MAP phds st.pc))’
          by (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘p’ >> simp[phds_def]) >>
        ‘p.fh ≠ cn’ by (strip_tac >> fs[]) >>
        ‘hsame p.fh ps ps1 ∧ hsame cn ps ps1’ by simp[] >>
        fs[hsame_def] >>
        simp[pok_def, Abbr ‘p'’] >> strip_tac >> simp[] >> rpt conj_tac >>
        TRY (qexists_tac ‘J’ >> simp[hch_def, new_chan_def] >> NO_TAC) >>
        strip_tac >> qpat_x_assum ‘_ ⇒ ∃j. hch w hs p.fh j ∧ _’ mp_tac >>
        (impl_tac >- fs[]) >> strip_tac >> qexists_tac ‘j’ >>
        qpat_x_assum ‘∀h j. hch w hs h j ∧ h ≠ cn ⇒ _’ (qspecl_then [‘p.fh’, ‘j’] mp_tac) >>
        simp[]) >>
  ‘EVERY (pok w1 hs1 ps1 rdy) (LUPDATE p' i st.pc)’
    by (simp[EVERY_EL, EL_LUPDATE] >> rpt strip_tac >> Cases_on ‘i = n’ >- gvs[] >>
        simp[] >> ‘pok w hs ps rdy (EL n st.pc)’ by fs[EVERY_EL] >>
        irule pok_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> simp[] >>
        ‘∀h. MEM h (phds (EL n st.pc)) ⇒ h ≠ cn’
          by (rpt strip_tac >> qpat_x_assum ‘¬MEM cn (FLAT _)’ mp_tac >>
              simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘EL n st.pc’ >>
              gvs[EL_MEM]) >>
        rpt conj_tac >> rpt strip_tac >> res_tac >> gvs[]) >>
  ‘EL i st.pc = p’ by simp[Abbr ‘p’] >>
  ‘p'.fh = p.fh ∧ p'.bh = SOME cn ∧ p'.fo = p.fo ∧ p'.bo’ by simp[Abbr ‘p'’] >>
  ‘MEM p' (LUPDATE p' i st.pc)’ by (simp[] >> qexists_tac ‘i’ >> simp[]) >>
  ‘∀n. n < LENGTH st.pc ∧ n ≠ i ⇒ MEM (EL n st.pc) (LUPDATE p' i st.pc)’
    by (rpt strip_tac >> simp[] >> qexists_tac ‘n’ >> simp[]) >>
  ‘∀h. hl_sent h ps1 ≠ [] ∨ hl_read h ps1 ≠ [] ∨ hl_eof h ps1 ∨ hl_refused h ps1 ∨
       hl_up h ps1 ⇒ MEM h (FLAT (MAP phds (LUPDATE p' i st.pc)))’
    by (rpt gen_tac >>
        qpat_x_assum ‘∀h. hsame h ps ps1’
          (qspec_then ‘h’ (strip_assume_tac o REWRITE_RULE [hsame_def])) >>
        asm_rewrite_tac [] >> disch_then assume_tac >>
        qpat_x_assum ‘∀h. MEM h (FLAT (MAP phds (LUPDATE _ _ _))) ⇔ _’
          (fn th => REWRITE_TAC [th]) >> disj2_tac >>
        qpat_x_assum ‘∀h. hl_sent h ps ≠ [] ∨ _ ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
  ‘∀hd. MEM hd (hl_acc_handles ps1) ⇔ ∃q'. MEM q' (LUPDATE p' i st.pc) ∧ q'.fh = hd’
    by (gen_tac >> qpat_x_assum ‘hl_acc_handles ps1 = _’ SUBST1_TAC >>
        qpat_x_assum ‘∀hd. MEM hd (hl_acc_handles ps) ⇔ _’ (qspec_then ‘hd’ SUBST1_TAC) >>
        eq_tac >> strip_tac
        >- (qpat_x_assum ‘MEM _ st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
            Cases_on ‘n = i’
            >- (qexists_tac ‘p'’ >> rveq >> asm_rewrite_tac [] >> rfs[])
            >> qexists_tac ‘EL n st.pc’ >> rveq >> simp[])
        >> qpat_x_assum ‘MEM q' (LUPDATE _ _ _)’
             (strip_assume_tac o REWRITE_RULE [MEM_EL, EL_LUPDATE]) >>
        Cases_on ‘n = i’ >> fs[]
        >- (qexists_tac ‘p’ >> rveq >> fs[])
        >> qexists_tac ‘EL n st.pc’ >> simp[EL_MEM]) >>
  ‘∀c. MEM c (hl_conn_handles ps1) ⇔ ∃q'. MEM q' (LUPDATE p' i st.pc) ∧ q'.bh = SOME c’
    by (gen_tac >> qpat_x_assum ‘hl_conn_handles ps1 = _’ SUBST1_TAC >>
        REWRITE_TAC [MEM_APPEND, MEM, OR_CLAUSES] >>
        qpat_x_assum ‘∀c. MEM c (hl_conn_handles ps) ⇔ _’ (qspec_then ‘c’ SUBST1_TAC) >>
        eq_tac >> strip_tac
        >- (qpat_x_assum ‘MEM _ st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
            Cases_on ‘n = i’
            >- (rveq >> rfs[])
            >> qexists_tac ‘EL n st.pc’ >> rveq >> simp[])
        >- (qexists_tac ‘p'’ >> rveq >> simp[])
        >> qpat_x_assum ‘MEM q' (LUPDATE _ _ _)’
             (strip_assume_tac o REWRITE_RULE [MEM_EL, EL_LUPDATE]) >>
        Cases_on ‘n = i’ >> fs[] >>
        TRY (disj2_tac >> rveq >> fs[] >> NO_TAC) >>
        disj1_tac >> qexists_tac ‘EL n st.pc’ >> simp[EL_MEM]) >>
  ‘∀h. MEM h (MAP FST hs1.tbl) ⇒ ∃q'. MEM q' (LUPDATE p' i st.pc) ∧ MEM h (popen q')’
    by (qpat_x_assum ‘hs1.tbl = _’ SUBST1_TAC >> REWRITE_TAC [MAP, MEM] >> rpt strip_tac
        >- (qexists_tac ‘p'’ >> rveq >> asm_rewrite_tac [] >> simp[popen_def])
        >> qpat_x_assum ‘∀h. MEM h (MAP FST hs.tbl) ⇒ _’ drule >> strip_tac >>
        qpat_x_assum ‘MEM p'' st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
        Cases_on ‘n = i’
        >- (qexists_tac ‘p'’ >> asm_rewrite_tac [] >> rveq >> rfs[popen_def])
        >> qexists_tac ‘EL n st.pc’ >> rveq >> simp[]) >>
  REWRITE_TAC [prel_def] >> simp_tac (srw_ss()) [] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[hdln_lt_cbound] >> NO_TAC) >>
  TRY (qexistsl_tac [‘a’, ‘q’] >> simp[] >> NO_TAC) >>
  TRY (asm_simp_tac (srw_ss()) [] >> NO_TAC) >>
  ‘¬MEM f' (MAP SND hs.tbl)’
    by (strip_tac >> qpat_x_assum ‘∀f. MEM f (MAP FST w.open_fds) ⇔ _’ (qspec_then ‘f'’ mp_tac) >>
        simp[]) >>
  TRY (mp_tac (Q.INST [‘k’ |-> ‘hs.nxt’] hdln_lt_cbound) >> simp[] >> NO_TAC) >>
  TRY (asm_simp_tac (srw_ss()) [] >> NO_TAC) >>
  TRY (simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  (* the handles' numbers *)
  TRY (rpt strip_tac >> qpat_x_assum ‘MEM _ (FLAT (MAP phds (LUPDATE _ _ _)))’ mp_tac >>
       asm_rewrite_tac [] >> strip_tac
       >- (qexists_tac ‘hs.nxt’ >> simp[Abbr ‘cn’])
       >> qpat_x_assum ‘∀h. MEM h (FLAT (MAP phds st.pc)) ⇒ ∃k. _’ drule >> strip_tac >>
       qexists_tac ‘k’ >> simp[] >> NO_TAC) >>
  gen_tac >> strip_tac >> qpat_x_assum ‘∀h. hl_sent h ps1 ≠ [] ∨ _ ⇒ _’ irule >>
  CCONTR_TAC >> fs[]
QED

(* ------------------------------------------------------------------------
   A pair's actions, one at a time
   ------------------------------------------------------------------------ *)

(* Action x can be taken for pair k in state st *)
Definition pstep_ok_def:
  pstep_ok b (rdy : word64 set) st k x ⇔
    k < LENGTH st.pc ∧
    let p = EL k st.pc in
      (x = EConnect b ∧ p.bh = NONE) ∨
      (x = EWrite p.fh p.bq ∧ p.fo ∧ p.bq ≠ []) ∨
      (∃c. p.bh = SOME c ∧ x = EWrite c p.fq ∧ p.bo ∧ p.fq ≠ []) ∨
      (∃c. p.bh = SOME c ∧ x = ERead p.fh pread ∧ p.fo ∧ p.bup) ∨
      (∃c. p.bh = SOME c ∧ x = ERead c pread ∧ p.bo ∧ (¬p.bup ⇒ c ∈ rdy))
End

Theorem pupd_pc_keep:
  (∀l. x ≠ ELevel l) ∧ (∀l. x ≠ EAccept l) ⇒
  pupd st [(k, x)] [r] = st with pc := LUPDATE (pres (EL k st.pc) x r) k st.pc
Proof
  Cases_on ‘x’ >> simp[]
QED

Theorem prel_step:
  prel lfd st rdy ps w hs ∧ pstep_ok b rdy st k x ⇒
  ∃r w1 hs1. ehdo lfd v (w, hs) x = SOME (r, (w1, hs1)) ∧
    prel lfd (pupd st [(k, x)] [r]) rdy (ps ++ [(x, r)]) w1 hs1
Proof
  strip_tac >>
  qpat_x_assum ‘pstep_ok _ _ _ _ _’ (strip_assume_tac o SIMP_RULE bool_ss [pstep_ok_def, LET_THM]) >>
  rveq
  >- (drule_all prel_connect >> disch_then (qspecl_then [‘v’, ‘b’] strip_assume_tac) >>
      qexistsl_tac [‘r’, ‘w1’, ‘hs1’] >> asm_rewrite_tac [])
  >- (drule_all prel_write_front >> disch_then (qspec_then ‘v’ strip_assume_tac) >>
      qexistsl_tac [‘EWrote (LENGTH (EL k st.pc).bq)’, ‘w1’, ‘hs’] >> asm_rewrite_tac [])
  >- (drule_all prel_write_back >> disch_then (qspec_then ‘v’ strip_assume_tac) >>
      qexistsl_tac [‘EWrote (LENGTH (EL k st.pc).fq)’, ‘w1’, ‘hs’] >> asm_rewrite_tac [])
  >- (drule_all prel_read_front >> disch_then (qspec_then ‘v’ strip_assume_tac) >>
      qexistsl_tac [‘r’, ‘w1’, ‘hs1’] >> asm_rewrite_tac [])
  >> drule_all prel_read_back >> disch_then (qspec_then ‘v’ strip_assume_tac) >>
  qexistsl_tac [‘r’, ‘w1’, ‘hs1’] >> asm_rewrite_tac []
QED

(* A list of actions for pair k, each possible after the ones before,
   whatever their results *)
Definition pseq_ok_def:
  pseq_ok b rdy st k [] = T ∧
  pseq_ok b rdy st k (x :: xs) =
    (pstep_ok b rdy st k x ∧ ∀r. pseq_ok b rdy (pupd st [(k, x)] [r]) k xs)
End

Theorem pupd_cons:
  pupd st ((i, x) :: xs) (r :: rs) = pupd (pupd st [(i, x)] [r]) xs rs
Proof
  simp[Once pupd_def] >> simp[pupd_def]
QED

Theorem prel_seq:
  ∀xs st ps w hs ix.
    prel lfd st rdy ps w hs ∧ pseq_ok b rdy st k xs ⇒
    ∃rs w1 hs1. ehacts lfd lv n ix (w, hs) xs = SOME (rs, (w1, hs1)) ∧
      LENGTH rs = LENGTH xs ∧
      prel lfd (pupd st (MAP (λx. (k, x)) xs) rs) rdy (ps ++ ZIP (xs, rs)) w1 hs1
Proof
  Induct >- (simp[ehacts_def, pupd_def]) >>
  rpt gen_tac >> REWRITE_TAC [pseq_ok_def] >> strip_tac >>
  drule_all prel_step >> disch_then (qspec_then ‘lv n ix’ strip_assume_tac) >>
  qpat_x_assum ‘∀r. pseq_ok _ _ _ _ _’ (qspec_then ‘r’ assume_tac) >>
  qpat_x_assum ‘∀st ps w hs ix. _’ drule_all >>
  disch_then (qspec_then ‘ix + 1’ strip_assume_tac) >>
  qexistsl_tac [‘r :: rs’, ‘w1'’, ‘hs1'’] >>
  simp[ehacts_def] >> ONCE_REWRITE_TAC [pupd_cons] >>
  full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem pres_EWrite:
  (pres p (EWrite h bs) r).fh = p.fh ∧ (pres p (EWrite h bs) r).fo = p.fo ∧
  (pres p (EWrite h bs) r).bh = p.bh ∧ (pres p (EWrite h bs) r).bo = p.bo ∧
  (pres p (EWrite h bs) r).bup = p.bup ∧
  (h = p.fh ⇒ (pres p (EWrite h bs) r).fq = p.fq)
Proof
  Cases_on ‘r’ >> rw[pres_def]
QED

Theorem pres_ERead_front:
  h = p.fh ⇒
  (pres p (ERead h n) r).fh = p.fh ∧ (pres p (ERead h n) r).bh = p.bh ∧
  (pres p (ERead h n) r).bo = p.bo ∧ (pres p (ERead h n) r).bup = p.bup
Proof
  strip_tac >> Cases_on ‘r’ >> rw[pres_def] >> every_case_tac >> simp[]
QED

Theorem pseq_ok_one:
  pstep_ok b rdy st k x ⇒ pseq_ok b rdy st k [x]
Proof
  simp[pseq_ok_def]
QED

(* A pair's actions of the round can be taken one after the other *)
Theorem pone_ok:
  prel lfd st rdy ps w hs ∧ k < LENGTH st.pc ⇒
  pseq_ok b rdy st k (pone b hw lvs lw nw rdy (EL k st.pc))
Proof
  strip_tac >>
  ‘pok w hs ps rdy (EL k st.pc)’ by (irule prel_pok >> metis_tac[]) >>
  qabbrev_tac ‘p = EL k st.pc’ >>
  Cases_on ‘p.bh’
  >- (‘p.bq = []’ by fs[pok_def] >>
      simp[pone_def, pconnects_def, pwrites_def, preads_def] >>
      irule pseq_ok_one >> simp[pstep_ok_def]) >>
  rename1 ‘p.bh = SOME c’ >>
  simp[pone_def, pconnects_def, pwrites_def, preads_def] >>
  rw[] >>
  simp[pseq_ok_def, pstep_ok_def, EL_LUPDATE, pres_EWrite, pres_ERead_front] >>
  rpt strip_tac >>
  simp[pseq_ok_def, pstep_ok_def, EL_LUPDATE, pres_EWrite, pres_ERead_front] >>
  rpt strip_tac >>
  simp[pseq_ok_def, pstep_ok_def, EL_LUPDATE, pres_EWrite, pres_ERead_front] >>
  rpt strip_tac >>
  simp[pseq_ok_def, pstep_ok_def, EL_LUPDATE, pres_EWrite, pres_ERead_front]
QED
