(*
  E1 (design/36 §6): the prefetching L1 with connect (honestL1EPModel), in
  ANY L0 world, refines the endpoint handle layer (endpointHLModel) in an
  endpoint world built from L1's own run, as R1-safe (honestL1PFRefine)
  does for the version-2 handle layer.

  The endpoint world's state mirrors L1's:
   - channel j is the j-th channel L1 created: its connects (sys_connect,
     in action order) and its accepts (the fetch log's FConn), numbered as
     endpointWorld numbers them; cm maps each fd to its channel;
   - an open handle's channel has inbox = the fd's inbox and peer_eof = the
     fd's EOF; a connect handle not yet up is Connecting, or Refused once
     L1 has seen the refusal;
   - the listener's pending channels are L1's accept queue;
   - the open fds are the handles' fds, which are the kernel's (alloc
     returns the kernel's fd);
   - the world takes every byte offered (L1 buffers writes).
  This part: the relation, and one action of L1 matches one action of the
  layer.
*)
Theory honestL1EPRefine
Ancestors
  honestL1EPModel honestL1PFRefine honestL1PFModel honestL1Model honestL1Steps
  honestL1Inv honestL0Rely honestL0World honestL0
  endpointHLModel endpointWorld asyncHLModel asyncCore asyncLevel1 asyncM3World
  llist alist
Libs
  preamble

(* ------------------------------------------------------------------------
   The relation
   ------------------------------------------------------------------------ *)

(* L1's state is the endpoint world's (listener lfd on address a) *)
Definition ev_rel_def:
  ev_rel lfd a cm es w ⇔
    w.listening = [(lfd, a, MAP (cl cm) es.p.acq)] ∧ w.reserved = [] ∧
    w.takes = (λj b n. n) ∧
    ALL_DISTINCT (MAP FST w.open_fds) ∧
    (∀f. MEM f (MAP FST w.open_fds) ⇔ MEM f (MAP SND es.p.b.tbl) ∨ MEM f (MAP SND es.ctbl)) ∧
    ALL_DISTINCT (MAP SND cm) ∧ EVERY (λj. j < LENGTH w.chans) (MAP SND cm) ∧
    (∀h f. ALOOKUP es.p.b.tbl h = SOME f ⇒
       MEM f (MAP FST cm) ∧ ALOOKUP w.open_fds f = SOME (cl cm f) ∧
       (EL (cl cm f) w.chans).inbox = inb_of es.p f ∧
       ((EL (cl cm f) w.chans).peer_eof ⇔ MEM f es.p.eof) ∧
       (EL (cl cm f) w.chans).status = Up ∧ ¬(EL (cl cm f) w.chans).shut) ∧
    (∀h f. ALOOKUP es.ctbl h = SOME f ⇒
       MEM f (MAP FST cm) ∧ ALOOKUP w.open_fds f = SOME (cl cm f) ∧
       (EL (cl cm f) w.chans).inbox = [] ∧ ¬(EL (cl cm f) w.chans).peer_eof ∧
       (EL (cl cm f) w.chans).status =
         (if cstat_of es f = CRefused then Refused else Connecting)) ∧
    (∀f. MEM f es.p.acq ⇒
       MEM f (MAP FST cm) ∧
       (EL (cl cm f) w.chans).inbox = [] ∧ ¬(EL (cl cm f) w.chans).peer_eof ∧
       (EL (cl cm f) w.chans).status = Up ∧ ¬(EL (cl cm f) w.chans).shut ∧
       ∀used. ¬MEM f used ⇒ w.alloc (cl cm f) used = f)
End

(* L1's own invariant: the prefetching part's (pown), and the connect
   table's fds and handles are fresh against it *)
Definition eown_def:
  eown lfd es ⇔
    pown lfd es.p ∧
    ALL_DISTINCT (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl) ∧
    ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl) ∧
    (∀h f. ALOOKUP es.ctbl h = SOME f ⇒
       (∃i. i < es.p.b.nxt ∧ h = hdl lfd i) ∧ cstat_of es f ≠ CUp) ∧
    (∀f. MEM f (MAP FST es.early) ⇒ MEM f (MAP SND es.ctbl) ∧ cstat_of es f = CPending) ∧
    ALL_DISTINCT (MAP FST es.early) ∧ EVERY (λ(f, c). c ≠ CPending) es.early ∧
    (∀h. MEM h es.settling ⇒ ∃i. i < es.p.b.nxt ∧ h = hdl lfd i)
End

(* The fds L1 holds are open in L0 *)
Definition l0owne_def:
  l0owne lfd w es ⇔ l0own lfd w es.p ∧ ∀f. MEM f (MAP SND es.ctbl) ⇒ MEM f (l0_used w)
End

(* The layer's handle state is L1's tables: the same lookups, the same
   handle count, and the same unreported settled handles among the open
   ones *)
Definition ehs_rel_def:
  ehs_rel hs es ⇔
    hs.nxt = es.p.b.nxt ∧
    (∀h. ALOOKUP hs.tbl h =
         case ALOOKUP es.p.b.tbl h of SOME f => SOME f | NONE => ALOOKUP es.ctbl h) ∧
    (∀h. MEM h hs.settling ⇔ MEM h es.settling ∧ ALOOKUP hs.tbl h ≠ NONE)
End

(* ------------------------------------------------------------------------
   Lemmas
   ------------------------------------------------------------------------ *)

Theorem l1hdl_hdl:
  l1hdl lfd i = hdl lfd i ∧ l1hdln n i = hdln n i
Proof
  simp[l1hdl_def, hdl_def, l1hdln_def, hdln_def]
QED

Theorem ev_rel_tbl:
  ev_rel lfd a cm es w ∧ ALOOKUP es.p.b.tbl h = SOME f ⇒
  ep_chan_of w f = SOME (cl cm f) ∧ cl cm f < LENGTH w.chans ∧
  ALOOKUP w.open_fds f = SOME (cl cm f) ∧ MEM f (MAP FST cm) ∧
  (EL (cl cm f) w.chans).inbox = inb_of es.p f ∧
  ((EL (cl cm f) w.chans).peer_eof ⇔ MEM f es.p.eof) ∧
  (EL (cl cm f) w.chans).status = Up ∧ ¬(EL (cl cm f) w.chans).shut
Proof
  simp[ev_rel_def] >> strip_tac >> first_x_assum drule >> strip_tac >>
  ‘cl cm f < LENGTH w.chans’
    by (gvs[EVERY_MEM, cl_def] >> Cases_on ‘ALOOKUP cm f’ >> gvs[ALOOKUP_NONE] >>
        metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  simp[ep_chan_of_def]
QED

Theorem ev_rel_ctbl:
  ev_rel lfd a cm es w ∧ ALOOKUP es.ctbl h = SOME f ⇒
  ep_chan_of w f = SOME (cl cm f) ∧ cl cm f < LENGTH w.chans ∧
  ALOOKUP w.open_fds f = SOME (cl cm f) ∧ MEM f (MAP FST cm) ∧
  (EL (cl cm f) w.chans).inbox = [] ∧ ¬(EL (cl cm f) w.chans).peer_eof ∧
  (EL (cl cm f) w.chans).status = (if cstat_of es f = CRefused then Refused else Connecting)
Proof
  simp[ev_rel_def] >> strip_tac >> qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = _ ⇒ _’ drule >>
  strip_tac >>
  ‘cl cm f < LENGTH w.chans’
    by (gvs[EVERY_MEM, cl_def] >> Cases_on ‘ALOOKUP cm f’ >> gvs[ALOOKUP_NONE] >>
        metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  simp[ep_chan_of_def]
QED

Theorem ev_rel_lookup:
  ehs_rel hs es ⇒
  (ALOOKUP es.p.b.tbl h = SOME f ⇒ ALOOKUP hs.tbl h = SOME f) ∧
  (ALOOKUP es.p.b.tbl h = NONE ⇒ ALOOKUP hs.tbl h = ALOOKUP es.ctbl h)
Proof
  rw[ehs_rel_def]
QED

(* The fds in use, counted *)
Theorem eown_count:
  eown lfd es ⇒
  LENGTH es.p.b.tbl + LENGTH es.ctbl ≤ es.p.b.nxt
Proof
  rw[eown_def, pown_def] >>
  ‘ALL_DISTINCT (MAP FST (es.p.b.tbl ++ es.ctbl))’ by gvs[] >>
  ‘∀h. MEM h (MAP FST (es.p.b.tbl ++ es.ctbl)) ⇒ ∃i. i < es.p.b.nxt ∧ h = hdl lfd i’
    by (rw[MEM_MAP, EXISTS_PROD] >> rename1 ‘MEM (h, f) _’ >>
        ‘ALOOKUP (es.p.b.tbl ++ es.ctbl) h = SOME f’
          by (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[]) >>
        gvs[ALOOKUP_APPEND, AllCaseEqs()] >> metis_tac[]) >>
  ‘set (MAP FST (es.p.b.tbl ++ es.ctbl)) ⊆ IMAGE (hdl lfd) (count es.p.b.nxt)’
    by (rw[SUBSET_DEF] >> metis_tac[MAP_APPEND, MEM_APPEND]) >>
  ‘CARD (set (MAP FST (es.p.b.tbl ++ es.ctbl))) ≤ CARD (IMAGE (hdl lfd) (count es.p.b.nxt))’
    by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (IMAGE (hdl lfd) (count es.p.b.nxt)) ≤ es.p.b.nxt’
    by metis_tac[CARD_IMAGE_LE, CARD_COUNT, FINITE_COUNT] >>
  ‘CARD (set (MAP FST (es.p.b.tbl ++ es.ctbl))) = LENGTH es.p.b.tbl + LENGTH es.ctbl’
    by (drule ALL_DISTINCT_CARD_LIST_TO_SET >> simp[]) >>
  decide_tac
QED

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

Theorem ev_accept:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
  edo lfd hw (wl, es) (EAccept l) = SOME (r, (wl', es'), evs) ⇒
  ∃w' hs'. ehdo lfd (w, hs) (EAccept l) = SOME (r, (w', hs')) ∧
           ev_rel lfd a cm es' w' ∧ eown lfd es' ∧ ehs_rel hs' es' ∧ wl' = wl ∧
           w'.chans = w.chans ∧ w'.alloc = w.alloc ∧ w'.env = w.env ∧ w'.clock = w.clock ∧
           es'.ctbl = es.ctbl ∧ es'.cst = es.cst ∧ es'.early = es.early ∧
           es'.settling = es.settling
Proof
  simp[edo_def, pdo_def] >> strip_tac >> gvs[AllCaseEqs()]
  >- ((* nothing pending *)
      ‘es with p := es.p = es’ by simp[l1e_component_equality] >> gvs[] >>
      ‘w.listening = [(l, a, [])]’ by gvs[ev_rel_def] >>
      simp[ehdo_def, ep_accept_def]) >>
  rename1 ‘es.p.acq = f :: q’ >>
  qabbrev_tac ‘h = l1hdl l es.p.b.nxt’ >>
  ‘LENGTH es.p.b.tbl + LENGTH es.ctbl ≤ es.p.b.nxt’ by metis_tac[eown_count] >>
  ‘es.p.b.nxt + 1 < dimword (:64)’ by (irule hdln_suc_lt >> qexists_tac ‘l’ >> simp[]) >>
  ‘f ≠ l ∧ ¬MEM f (MAP SND es.p.b.tbl) ∧ ¬MEM f q ∧ ¬MEM f es.p.b.closing ∧
   ¬MEM f (MAP SND es.ctbl)’
    by (gvs[eown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘inb_of es.p f = [] ∧ ¬MEM f es.p.eof’ by (gvs[eown_def, pown_def] >> metis_tac[]) >>
  ‘ep_used w = l :: MAP FST w.open_fds’ by gvs[ep_used_def, ev_rel_def] >>
  ‘¬MEM f (ep_used w)’ by (gvs[ev_rel_def] >> metis_tac[]) >>
  ‘w.alloc (cl cm f) (ep_used w) = f’ by (gvs[ev_rel_def] >> metis_tac[]) >>
  ‘LENGTH w.open_fds = LENGTH es.p.b.tbl + LENGTH es.ctbl’
    by (‘set (MAP FST w.open_fds) = set (MAP SND es.p.b.tbl ++ MAP SND es.ctbl)’
          by (gvs[ev_rel_def, EXTENSION] >> metis_tac[]) >>
        ‘ALL_DISTINCT (MAP SND es.p.b.tbl ++ MAP SND es.ctbl)’
          by gvs[eown_def, ALL_DISTINCT_APPEND] >>
        ‘ALL_DISTINCT (MAP FST w.open_fds)’ by gvs[ev_rel_def] >>
        metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET, LENGTH_MAP, LENGTH_APPEND]) >>
  ‘LENGTH (ep_used w) < dimword (:64)’ by fs[] >>
  ‘FILTER (λ(l', a', q). l' = l) w.listening = [(l, a, MAP (cl cm) (f :: q))]’
    by gvs[ev_rel_def] >>
  simp[ehdo_def, ep_accept_def, ep_alloc_def, l1hdl_hdl] >>
  gvs[l1hdl_hdl, Abbr ‘h’] >>
  ‘hs.nxt = es.p.b.nxt’ by gvs[ehs_rel_def] >>
  qabbrev_tac ‘hn = hdl l es.p.b.nxt’ >>
  ‘∀i. i < es.p.b.nxt ⇒ hdl l i ≠ hn’
    by (rw[Abbr ‘hn’] >> irule hdl_fresh >> simp[]) >>
  ‘ALOOKUP es.p.b.tbl hn = NONE ∧ ALOOKUP es.ctbl hn = NONE ∧ ¬MEM hn es.settling’
    by (gvs[eown_def, pown_def] >> rpt conj_tac
        >- (Cases_on ‘ALOOKUP es.p.b.tbl hn’ >> simp[] >> res_tac >> metis_tac[])
        >- (Cases_on ‘ALOOKUP es.ctbl hn’ >> simp[] >> res_tac >> metis_tac[])
        >> strip_tac >> res_tac >> metis_tac[]) >>
  ‘¬MEM hn (MAP FST es.p.b.tbl) ∧ ¬MEM hn (MAP FST es.ctbl)’ by gvs[ALOOKUP_NONE] >>
  simp[eh_new_def] >> rpt conj_tac
  >- (qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >>
      simp[ev_rel_def, AFUPDKEY_def, inb_of_def, cstat_of_def] >> strip_tac >>
      gvs[inb_of_def] >> rpt conj_tac
      >- metis_tac[]
      >- (rpt gen_tac >> Cases_on ‘hn = h’ >> simp[]
          >- (strip_tac >> gvs[])
          >> strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
          ‘f' ≠ f’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >> simp[])
      >> rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      ‘f' ≠ f’ by (strip_tac >> gvs[] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >> simp[])
  >- ((* L1's invariant *)
      qpat_x_assum ‘eown _ _’ mp_tac >>
      simp[eown_def, pown_def, inb_of_def, cstat_of_def, l1hdl_hdl] >> strip_tac >>
      gvs[ALL_DISTINCT_APPEND] >> rpt conj_tac >> rpt strip_tac >>
      TRY (metis_tac[] >> NO_TAC)
      >- (Cases_on ‘hn = h’ >> gvs[]
          >- (qexists_tac ‘es.p.b.nxt’ >> gvs[markerTheory.Abbrev_def])
          >> res_tac >> qexists_tac ‘i’ >> simp[])
      >> res_tac >> qexists_tac ‘i’ >> simp[])
  >> gvs[ehs_rel_def] >> conj_tac
  >- (gen_tac >> rw[])
  >> gen_tac >> Cases_on ‘h = hn’ >> gvs[] >> metis_tac[]
QED

(* Distinct fds of the relation have distinct channels *)
Theorem ev_rel_cl_ne:
  ev_rel lfd a cm es w ∧ eown lfd es ∧
  (MEM f (MAP SND es.p.b.tbl) ∨ MEM f (MAP SND es.ctbl) ∨ MEM f es.p.acq) ∧
  (MEM g (MAP SND es.p.b.tbl) ∨ MEM g (MAP SND es.ctbl) ∨ MEM g es.p.acq) ∧ g ≠ f ⇒
  cl cm g ≠ cl cm f
Proof
  strip_tac >>
  ‘∀x. MEM x (MAP SND es.p.b.tbl) ∨ MEM x (MAP SND es.ctbl) ∨ MEM x es.p.acq ⇒
       MEM x (MAP FST cm)’
    by (rw[] >> gvs[ev_rel_def, MEM_MAP, EXISTS_PROD] >>
        TRY (rename1 ‘MEM (hh, x) es.p.b.tbl’ >>
             ‘ALOOKUP es.p.b.tbl hh = SOME x’
               by (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[eown_def, ALL_DISTINCT_APPEND]) >>
             res_tac >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
        TRY (rename1 ‘MEM (hh, x) es.ctbl’ >>
             ‘ALOOKUP es.ctbl hh = SOME x’
               by (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[eown_def, ALL_DISTINCT_APPEND]) >>
             res_tac >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
        res_tac >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘ALL_DISTINCT (MAP SND cm)’ by gvs[ev_rel_def] >>
  metis_tac[cl_inj]
QED

Theorem upd_chan_fields[simp]:
  (upd_chan j g w).open_fds = w.open_fds ∧ (upd_chan j g w).listening = w.listening ∧
  (upd_chan j g w).reserved = w.reserved ∧ (upd_chan j g w).alloc = w.alloc ∧
  (upd_chan j g w).takes = w.takes ∧ (upd_chan j g w).env = w.env ∧
  (upd_chan j g w).clock = w.clock ∧ (upd_chan j g w).hist = w.hist ∧
  LENGTH (upd_chan j g w).chans = LENGTH w.chans
Proof
  simp[upd_chan_def]
QED

(* The prefetching part changed within its own fds and handles: L1's
   invariant kept *)
Theorem eown_p:
  eown lfd es ∧ pown lfd ps' ∧ ps'.b.nxt = es.p.b.nxt ∧
  (∀g. MEM g (MAP SND ps'.b.tbl) ∨ MEM g ps'.b.closing ∨ MEM g ps'.acq ⇒
       MEM g (MAP SND es.p.b.tbl) ∨ MEM g es.p.b.closing ∨ MEM g es.p.acq) ∧
  (∀k. MEM k (MAP FST ps'.b.tbl) ⇒ MEM k (MAP FST es.p.b.tbl)) ⇒
  eown lfd (es with p := ps')
Proof
  simp[eown_def, cstat_of_def] >> strip_tac >>
  gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* One channel changed: the relation holds if its fd's view is right *)
Theorem ev_rel_upd:
  ev_rel lfd a cm es w ∧ eown lfd es ∧
  (MEM f (MAP SND es.p.b.tbl) ∨ MEM f (MAP SND es.ctbl)) ∧
  es'.p.b.tbl = es.p.b.tbl ∧ es'.ctbl = es.ctbl ∧ es'.p.acq = es.p.acq ∧
  (∀g. g ≠ f ⇒ inb_of es'.p g = inb_of es.p g ∧ (MEM g es'.p.eof ⇔ MEM g es.p.eof) ∧
                cstat_of es' g = cstat_of es g) ∧
  (MEM f (MAP SND es.p.b.tbl) ⇒
     (gc (EL (cl cm f) w.chans)).inbox = inb_of es'.p f ∧
     ((gc (EL (cl cm f) w.chans)).peer_eof ⇔ MEM f es'.p.eof) ∧
     (gc (EL (cl cm f) w.chans)).status = Up ∧ ¬(gc (EL (cl cm f) w.chans)).shut) ∧
  (MEM f (MAP SND es.ctbl) ⇒
     (gc (EL (cl cm f) w.chans)).inbox = [] ∧ ¬(gc (EL (cl cm f) w.chans)).peer_eof ∧
     (gc (EL (cl cm f) w.chans)).status =
       (if cstat_of es' f = CRefused then Refused else Connecting)) ⇒
  ev_rel lfd a cm es' (upd_chan (cl cm f) gc w)
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [GSYM MEM_APPEND]) >>
  ‘∀g. (MEM g (MAP SND es.p.b.tbl) ∨ MEM g (MAP SND es.ctbl) ∨ MEM g es.p.acq) ∧ g ≠ f ⇒
       cl cm g ≠ cl cm f’ by metis_tac[ev_rel_cl_ne, MEM_APPEND] >>
  ‘¬MEM f es.p.acq’ by (gvs[eown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘cl cm f < LENGTH w.chans’
    by (‘ALL_DISTINCT (MAP FST es.p.b.tbl) ∧ ALL_DISTINCT (MAP FST es.ctbl)’
          by gvs[eown_def, ALL_DISTINCT_APPEND] >>
        metis_tac[tbl_alookup_exists, ev_rel_tbl, ev_rel_ctbl, MEM_APPEND]) >>
  qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >>
  simp[ev_rel_def, upd_chan_def, EL_LUPDATE] >> strip_tac >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      ‘MEM f' (MAP SND es.p.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
      first_x_assum drule >> strip_tac >>
      Cases_on ‘f' = f’ >> gvs[] >>
      ‘cl cm f' ≠ cl cm f’ by metis_tac[] >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      ‘MEM f' (MAP SND es.ctbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
      qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = _ ⇒ _’ drule >> strip_tac >>
      Cases_on ‘f' = f’ >> gvs[] >>
      ‘cl cm f' ≠ cl cm f’ by metis_tac[] >> simp[])
  >> rpt gen_tac >> strip_tac >> gvs[] >> res_tac >>
  ‘f' ≠ f’ by (strip_tac >> gvs[]) >>
  ‘cl cm f' ≠ cl cm f’ by metis_tac[] >> simp[]
QED

(* A channel's fd closed in both: its handle forgotten *)
Theorem ev_rel_close:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
  (ALOOKUP es.p.b.tbl h = SOME f ∨ (ALOOKUP es.p.b.tbl h = NONE ∧ ALOOKUP es.ctbl h = SOME f)) ∧
  ep_close f w1 = SOME w2 ∧ w1.open_fds = w.open_fds ∧ w1.listening = w.listening ∧
  w1.reserved = w.reserved ∧ w1.takes = w.takes ∧ w1.alloc = w.alloc ∧
  LENGTH w1.chans = LENGTH w.chans ∧
  (∀j. j ≠ cl cm f ⇒ EL j w1.chans = EL j w.chans) ∧
  es'.p.b.tbl = ADELKEY h es.p.b.tbl ∧ es'.ctbl = ADELKEY h es.ctbl ∧
  es'.p.b.nxt = es.p.b.nxt ∧ es'.p.acq = es.p.acq ∧
  (∀g. g ≠ f ⇒ inb_of es'.p g = inb_of es.p g ∧ (MEM g es'.p.eof ⇔ MEM g es.p.eof) ∧
                cstat_of es' g = cstat_of es g) ∧
  (∀h'. h' ≠ h ⇒ (MEM h' es'.settling ⇔ MEM h' es.settling)) ⇒
  ev_rel lfd a cm es' w2 ∧
  ehs_rel (eh_del h hs) es'
Proof
  PURE_REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  ‘ALL_DISTINCT (MAP FST es.p.b.tbl) ∧ ALL_DISTINCT (MAP FST es.ctbl) ∧
   ALL_DISTINCT (MAP SND es.p.b.tbl) ∧ ALL_DISTINCT (MAP SND es.ctbl) ∧
   (∀g. MEM g (MAP SND es.p.b.tbl) ⇒ ¬MEM g (MAP SND es.ctbl)) ∧
   (∀k. MEM k (MAP FST es.p.b.tbl) ⇒ ¬MEM k (MAP FST es.ctbl)) ∧
   (∀g. MEM g es.p.acq ⇒ ¬MEM g (MAP SND es.p.b.tbl) ∧ ¬MEM g (MAP SND es.ctbl))’
    by (qpat_x_assum ‘eown _ _’ mp_tac >> rpt (pop_assum kall_tac) >>
        simp[eown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘MEM f (MAP SND es.p.b.tbl ++ MAP SND es.ctbl)’
    by (qpat_x_assum ‘_ ∨ _’ strip_assume_tac >> imp_res_tac ALOOKUP_SOME_MEM_SND >> simp[]) >>
  ‘¬MEM f es.p.acq’ by metis_tac[MEM_APPEND] >>
  ‘¬MEM f (MAP SND es'.p.b.tbl) ∧ ¬MEM f (MAP SND es'.ctbl)’
    by (qpat_x_assum ‘ALOOKUP _ _ = _ ∨ _’ strip_assume_tac >> simp[] >>
        metis_tac[MEM_SND_ADELKEY, MEM_SND_ADELKEY_sub, ALOOKUP_SOME_MEM_SND]) >>
  ‘∀g. MEM g (MAP SND es'.p.b.tbl) ∨ MEM g (MAP SND es'.ctbl) ⇔
       (MEM g (MAP SND es.p.b.tbl) ∨ MEM g (MAP SND es.ctbl)) ∧ g ≠ f’
    by (gen_tac >> eq_tac
        >- (strip_tac >> gvs[] >> metis_tac[MEM_SND_ADELKEY_sub]) >>
        qpat_x_assum ‘ALOOKUP _ _ = _ ∨ _’ strip_assume_tac >> simp[]
        >- (‘¬MEM h (MAP FST es.ctbl)’ by metis_tac[ALOOKUP_SOME_MEM_FST] >>
            simp[ADELKEY_not_MEM] >> metis_tac[MEM_SND_ADELKEY])
        >> ‘¬MEM h (MAP FST es.p.b.tbl)’ by gvs[ALOOKUP_NONE] >>
        simp[ADELKEY_not_MEM] >> metis_tac[MEM_SND_ADELKEY]) >>
  ‘∀g. (MEM g (MAP SND es.p.b.tbl) ∨ MEM g (MAP SND es.ctbl) ∨ MEM g es.p.acq) ∧ g ≠ f ⇒
       cl cm g ≠ cl cm f’ by metis_tac[ev_rel_cl_ne, MEM_APPEND] >>
  ‘ALOOKUP w.open_fds f = SOME (cl cm f) ∧ cl cm f < LENGTH w.chans’
    by (qpat_x_assum ‘ALOOKUP _ _ = _ ∨ _’ strip_assume_tac >>
        metis_tac[ev_rel_tbl, ev_rel_ctbl]) >>
  ‘w2 = upd_chan (cl cm f) (λc. c with <| shut := T; closed := T |>)
          (w1 with open_fds := ADELKEY f w.open_fds)’
    by (qpat_x_assum ‘ep_close _ _ = _’ mp_tac >>
        simp[ep_close_def, ep_chan_of_def]) >>
  conj_tac
  >- (qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >>
      simp[ev_rel_def, upd_chan_def, EL_LUPDATE] >> strip_tac >> rpt conj_tac
      >- simp[ALL_DISTINCT_MAP_FST_ADELKEY]
      >- (simp[MEM_FST_ADELKEY] >> metis_tac[])
      >- (rpt gen_tac >> strip_tac >>
          ‘ALOOKUP es.p.b.tbl h' = SOME f'’ by gvs[ALOOKUP_ADELKEY, AllCaseEqs()] >>
          ‘f' ≠ f’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          first_x_assum drule >> strip_tac >>
          ‘cl cm f' ≠ cl cm f’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          simp[ALOOKUP_ADELKEY])
      >- (rpt gen_tac >> strip_tac >>
          ‘ALOOKUP es.ctbl h' = SOME f'’ by gvs[ALOOKUP_ADELKEY, AllCaseEqs()] >>
          ‘f' ≠ f’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = _ ⇒ _’ drule >> strip_tac >>
          ‘cl cm f' ≠ cl cm f’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          simp[ALOOKUP_ADELKEY])
      >> rpt gen_tac >> strip_tac >> gvs[] >> res_tac >>
      ‘f' ≠ f’ by (strip_tac >> gvs[]) >>
      ‘cl cm f' ≠ cl cm f’ by metis_tac[] >> simp[])
  >> qpat_x_assum ‘ehs_rel _ _’ mp_tac >>
  simp[ehs_rel_def, eh_del_def, ALOOKUP_ADELKEY, MEM_FILTER] >> strip_tac >>
  conj_tac
  >- (gen_tac >> Cases_on ‘h = h'’ >> simp[])
  >> gen_tac >> Cases_on ‘h = h'’ >> simp[] >> metis_tac[]
QED

Theorem cstat_of_ec_del:
  cstat_of (ec_del h f es) g = if g = f then CPending else cstat_of es g
Proof
  rw[cstat_of_def, ec_del_def, ALOOKUP_ADELKEY]
QED

(* A refused connect handle forgotten: L1's invariant kept *)
Theorem eown_ec_del:
  eown lfd es ∧ ALOOKUP es.ctbl h = SOME f ∧ cstat_of es f = CRefused ⇒
  eown lfd (ec_del h f es)
Proof
  strip_tac >>
  ‘ALL_DISTINCT (MAP FST es.ctbl) ∧ ALL_DISTINCT (MAP SND es.ctbl)’
    by gvs[eown_def, ALL_DISTINCT_APPEND] >>
  ‘∀g. MEM g (MAP SND (ADELKEY h es.ctbl)) ⇔ MEM g (MAP SND es.ctbl) ∧ g ≠ f’
    by metis_tac[MEM_SND_ADELKEY] >>
  qpat_x_assum ‘eown _ _’ mp_tac >>
  simp[eown_def, cstat_of_ec_del] >> simp[ec_del_def] >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, ALL_DISTINCT_MAP_FST_ADELKEY, ALL_DISTINCT_MAP_SND_ADELKEY,
      MEM_FST_ADELKEY, ALOOKUP_ADELKEY, MEM_FILTER, FILTER_ALL_DISTINCT] >>
  rpt conj_tac >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  res_tac >> gvs[]
QED

Theorem pown_set_inb:
  pown lfd ps ∧ MEM f (MAP SND ps.b.tbl) ⇒ pown lfd (set_inb f x ps)
Proof
  simp[pown_def] >> rw[] >> Cases_on ‘f' = f’ >> gvs[]
QED

(* ERead on a connect handle: pending (nothing yet), or refused (reported,
   the fd closed in both) *)
Theorem ev_read_conn:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧ ALOOKUP es.ctbl h = SOME f ∧
  edo lfd hw (wl, es) (ERead h n) = SOME (r, (wl', es'), evs) ⇒
  ∃w' hs'. ehdo lfd (w, hs) (ERead h n) = SOME (r, (w', hs')) ∧
           ev_rel lfd a cm es' w' ∧ eown lfd es' ∧ ehs_rel hs' es' ∧
           w'.listening = w.listening ∧ w'.alloc = w.alloc ∧ w'.env = w.env ∧
           w'.clock = w.clock ∧ w'.hist = w.hist ∧ LENGTH w'.chans = LENGTH w.chans ∧
           es'.p.b.nxt = es.p.b.nxt ∧ es'.p.acq = es.p.acq ∧ es'.early = es.early
Proof
  strip_tac >>
  ‘ALOOKUP es.p.b.tbl h = NONE’
    by (gvs[eown_def, ALL_DISTINCT_APPEND, ALOOKUP_NONE] >>
        metis_tac[ALOOKUP_SOME_MEM_FST]) >>
  ‘ALOOKUP hs.tbl h = SOME f’ by gvs[ehs_rel_def] >>
  drule_all ev_rel_ctbl >> strip_tac >>
  qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
  Cases_on ‘0 < n ∧ n < 256 ** 8’ >> simp[] >> simp[ehdo_def] >>
  Cases_on ‘cstat_of es f = CRefused’ >> simp[]
  >- ((* refused *)
      strip_tac >> rename1 ‘l1_close f _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
      rename1 ‘l1_close f _ = SOME ((wl', b'), evs)’ >>
      drule l1_close_b >> strip_tac >>
      simp[ep_conn_err_def] >>
      qabbrev_tac ‘w1 = upd_chan (cl cm f) (λc. c with status := Failed) w’ >>
      ‘∃w2. ep_close f w1 = SOME w2’
        by simp[ep_close_def, ep_chan_of_def, Abbr ‘w1’] >>
      ‘¬MEM f es.p.b.closing’
        by (gvs[eown_def, ALL_DISTINCT_APPEND] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >>
      ‘b'.closing = es.p.b.closing’ by simp[FILTER_EQ_ID, EVERY_MEM] >>
      ‘eown lfd (es with p := es.p with b := b')’
        by (irule eown_p >> simp[] >> gvs[eown_def, pown_b]) >>
      ‘ev_rel lfd a cm (ec_del h f (es with p := es.p with b := b')) w2 ∧
       ehs_rel (eh_del h hs) (ec_del h f (es with p := es.p with b := b'))’
        by (irule ev_rel_close >> qexistsl_tac [‘es’, ‘f’, ‘w’, ‘w1’] >>
            simp[ec_del_def, cstat_of_ec_del, inb_of_def, Abbr ‘w1’, MEM_FILTER] >>
            simp[upd_chan_def, EL_LUPDATE] >> rw[] >>
            gvs[ALOOKUP_NONE, ADELKEY_not_MEM, cstat_of_def]) >>
      simp[] >> conj_tac
      >- (irule eown_ec_del >> simp[ec_del_def, cstat_of_def] >> gvs[cstat_of_def]) >>
      qpat_x_assum ‘ep_close _ _ = _’ mp_tac >>
      simp[ep_close_def, ep_chan_of_def, Abbr ‘w1’] >> strip_tac >> gvs[] >>
      simp[ec_del_def])
  >> strip_tac >> gvs[] >>
  simp[ep_conn_err_def, ep_read_def]
QED

(* ERead on any other handle: the prefetching part's read (data, nothing
   yet, or EOF and the fd closed in both) *)
Theorem ev_read_pf:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧ ALOOKUP es.ctbl h = NONE ∧
  edo lfd hw (wl, es) (ERead h n) = SOME (r, (wl', es'), evs) ⇒
  ∃w' hs'. ehdo lfd (w, hs) (ERead h n) = SOME (r, (w', hs')) ∧
           ev_rel lfd a cm es' w' ∧ eown lfd es' ∧ ehs_rel hs' es' ∧
           w'.listening = w.listening ∧ w'.alloc = w.alloc ∧ w'.env = w.env ∧
           w'.clock = w.clock ∧ w'.hist = w.hist ∧ LENGTH w'.chans = LENGTH w.chans ∧
           es'.p.b.nxt = es.p.b.nxt ∧ es'.p.acq = es.p.acq ∧ es'.early = es.early
Proof
  strip_tac >>
  ‘ALOOKUP hs.tbl h = ALOOKUP es.p.b.tbl h’
    by (gvs[ehs_rel_def] >> Cases_on ‘ALOOKUP es.p.b.tbl h’ >> simp[]) >>
  qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >> strip_tac >>
  rename1 ‘pdo _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
  rename1 ‘pdo _ _ _ = SOME (rr, (wl', ps'), evs)’ >>
  ‘0 < n ∧ n < 256 ** 8’ by gvs[pdo_def, AllCaseEqs()] >>
  simp[ehdo_def] >>
  Cases_on ‘ALOOKUP es.p.b.tbl h’ >> simp[]
  >- (gvs[pdo_def] >>
      ‘es with p := es.p = es’ by simp[l1e_component_equality] >> simp[]) >>
  rename1 ‘ALOOKUP es.p.b.tbl h = SOME f’ >>
  drule_all ev_rel_tbl >> strip_tac >>
  simp[ep_conn_err_def, ep_read_def] >>
  Cases_on ‘inb_of es.p f = []’ >> simp[]
  >- (Cases_on ‘MEM f es.p.eof’ >> simp[]
      >- ((* EOF: closed *)
          drule_all pdo_read_eof >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
          gvs[] >>
          ‘ADELKEY h es.ctbl = es.ctbl’ by gvs[ALOOKUP_NONE, ADELKEY_not_MEM] >>
          (* both closing outcomes alike *)
          (‘∃w2. ep_close f w = SOME w2’ by simp[ep_close_def] >>
          qexists_tac ‘w2’ >> simp[] >>
          ‘ev_rel lfd a cm (es with p := ps') w2 ∧ ehs_rel (eh_del h hs) (es with p := ps')’
            by (irule ev_rel_close >> qexistsl_tac [‘es’, ‘f’, ‘w’, ‘w’] >>
                simp[inb_of_def, cstat_of_def, MEM_FILTER]) >>
          ‘MEM f (MAP SND es.p.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          simp[] >> conj_tac
          >- (irule eown_p >> simp[MEM_FST_ADELKEY] >> conj_tac
              >- (rpt strip_tac >> gvs[MEM_FILTER] >> metis_tac[MEM_SND_ADELKEY_sub]) >>
              irule read_eof_pown >> qexistsl_tac [‘f’, ‘h’, ‘es.p’] >>
              gvs[eown_def]) >>
          qpat_x_assum ‘ep_close _ _ = _’ mp_tac >> simp[ep_close_def] >>
          disch_then (SUBST_ALL_TAC o SYM) >> simp[])) >>
      gvs[pdo_def] >>
      ‘es with p := es.p = es’ by simp[l1e_component_equality] >> simp[]) >>
  (* data *)
  ‘∃x xs. TAKE n (inb_of es.p f) = x :: xs’
    by (Cases_on ‘inb_of es.p f’ >> gvs[] >> Cases_on ‘n’ >> gvs[]) >>
  gvs[pdo_def] >>
  ‘¬MEM f (MAP SND es.ctbl)’
    by (gvs[eown_def, ALL_DISTINCT_APPEND] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  rpt conj_tac
  >- (irule ev_rel_upd >> qexists_tac ‘es’ >> simp[cstat_of_def] >>
      metis_tac[ALOOKUP_SOME_MEM_SND])
  >- (irule eown_p >> simp[] >> irule pown_set_inb >> gvs[eown_def] >>
      metis_tac[ALOOKUP_SOME_MEM_SND])
  >> gvs[ehs_rel_def]
QED

Theorem ev_read:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
  edo lfd hw (wl, es) (ERead h n) = SOME (r, (wl', es'), evs) ⇒
  ∃w' hs'. ehdo lfd (w, hs) (ERead h n) = SOME (r, (w', hs')) ∧
           ev_rel lfd a cm es' w' ∧ eown lfd es' ∧ ehs_rel hs' es' ∧
           w'.listening = w.listening ∧ w'.alloc = w.alloc ∧ w'.env = w.env ∧
           w'.clock = w.clock ∧ w'.hist = w.hist ∧ LENGTH w'.chans = LENGTH w.chans ∧
           es'.p.b.nxt = es.p.b.nxt ∧ es'.p.acq = es.p.acq ∧ es'.early = es.early
Proof
  strip_tac >> Cases_on ‘ALOOKUP es.ctbl h’
  >- (drule_all ev_read_pf >> simp[])
  >> drule_all ev_read_conn >> simp[]
QED

Theorem ev_rel_b:
  b'.tbl = es.p.b.tbl ⇒
  (ev_rel lfd a cm (es with p := es.p with b := b') w ⇔ ev_rel lfd a cm es w)
Proof
  simp[ev_rel_def, inb_of_def, cstat_of_def]
QED

(* EWrite: a refused connect handle takes nothing; an accepted handle
   takes everything (the world's policy takes all) *)
Theorem ev_write:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
  edo lfd hw (wl, es) (EWrite h bs) = SOME (r, (wl', es'), evs) ⇒
  ∃w' hs'. ehdo lfd (w, hs) (EWrite h bs) = SOME (r, (w', hs')) ∧
           ev_rel lfd a cm es' w' ∧ eown lfd es' ∧ ehs_rel hs' es' ∧
           w'.listening = w.listening ∧ w'.alloc = w.alloc ∧ w'.env = w.env ∧
           w'.clock = w.clock ∧ w'.hist = w.hist ∧ LENGTH w'.chans = LENGTH w.chans ∧
           es'.p.b.nxt = es.p.b.nxt ∧ es'.p.acq = es.p.acq ∧ es'.early = es.early
Proof
  strip_tac >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
  Cases_on ‘ALOOKUP es.ctbl h’ >> simp[]
  >- ((* the prefetching part's write *)
      strip_tac >> pairarg_tac >> gvs[pdo_def] >>
      rename1 ‘l1do _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
      rename1 ‘l1do _ _ _ = SOME (r1, (wl', b'), evs)’ >>
      drule l1do_write_tbl >> strip_tac >> gvs[] >>
      ‘ALOOKUP hs.tbl h = ALOOKUP es.p.b.tbl h’
        by (gvs[ehs_rel_def] >> Cases_on ‘ALOOKUP es.p.b.tbl h’ >> simp[]) >>
      ‘eown lfd (es with p := es.p with b := b')’
        by (irule eown_p >> simp[pown_b] >> gvs[eown_def]) >>
      ‘ehs_rel hs (es with p := es.p with b := b')’ by gvs[ehs_rel_def] >>
      simp[ehdo_def] >>
      Cases_on ‘ALOOKUP es.p.b.tbl h’ >> simp[ev_rel_b] >>
      rename1 ‘ALOOKUP es.p.b.tbl h = SOME f’ >>
      drule_all ev_rel_tbl >> strip_tac >>
      simp[chan_status_def, ep_send_def] >>
      ‘w.takes = (λj b n. n)’ by gvs[ev_rel_def] >> simp[] >>
      ‘¬MEM f (MAP SND es.ctbl)’
        by (gvs[eown_def, ALL_DISTINCT_APPEND] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >>
      irule ev_rel_upd >> qexists_tac ‘es’ >> simp[inb_of_def, cstat_of_def] >>
      metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  (* a refused connect handle *)
  rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
  rw[] >>
  ‘ALOOKUP es.p.b.tbl h = NONE’
    by (gvs[eown_def, ALL_DISTINCT_APPEND, ALOOKUP_NONE] >>
        metis_tac[ALOOKUP_SOME_MEM_FST]) >>
  ‘ALOOKUP hs.tbl h = SOME f’ by gvs[ehs_rel_def] >>
  drule_all ev_rel_ctbl >> strip_tac >>
  simp[ehdo_def, chan_status_def, ep_send_def] >>
  ‘es with p := es.p = es’ by simp[l1e_component_equality] >>
  ‘MEM f (MAP SND es.ctbl) ∧ ¬MEM f (MAP SND es.p.b.tbl)’
    by (imp_res_tac ALOOKUP_SOME_MEM_SND >> gvs[eown_def, ALL_DISTINCT_APPEND] >>
        metis_tac[]) >>
  irule ev_rel_upd >> qexists_tac ‘es’ >> simp[]
QED
