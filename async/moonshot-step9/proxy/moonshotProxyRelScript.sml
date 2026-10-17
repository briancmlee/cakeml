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
