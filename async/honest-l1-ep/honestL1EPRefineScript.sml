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
  socketV2FFI ffiSpikeSocketFFI Marshalling
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
         (if cstat_of es f = CRefused then Refused else Connecting) ∧
       ¬(EL (cl cm f) w.chans).shut) ∧
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
  (EL (cl cm f) w.chans).status = (if cstat_of es f = CRefused then Refused else Connecting) ∧
  ¬(EL (cl cm f) w.chans).shut
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
           w'.hist = w.hist ∧
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
Theorem eown_p_disj:
  eown lfd es ∧ pown lfd ps' ∧ ps'.b.nxt = es.p.b.nxt ∧
  (∀g. MEM g (MAP SND ps'.b.tbl) ∨ MEM g ps'.b.closing ∨ MEM g ps'.acq ⇒
       ¬MEM g (MAP SND es.ctbl)) ∧
  (∀k. MEM k (MAP FST ps'.b.tbl) ⇒ MEM k (MAP FST es.p.b.tbl)) ⇒
  eown lfd (es with p := ps')
Proof
  simp[eown_def, cstat_of_def] >> strip_tac >>
  gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem eown_p:
  eown lfd es ∧ pown lfd ps' ∧ ps'.b.nxt = es.p.b.nxt ∧
  (∀g. MEM g (MAP SND ps'.b.tbl) ∨ MEM g ps'.b.closing ∨ MEM g ps'.acq ⇒
       MEM g (MAP SND es.p.b.tbl) ∨ MEM g es.p.b.closing ∨ MEM g es.p.acq) ∧
  (∀k. MEM k (MAP FST ps'.b.tbl) ⇒ MEM k (MAP FST es.p.b.tbl)) ⇒
  eown lfd (es with p := ps')
Proof
  strip_tac >> irule eown_p_disj >> simp[] >>
  gvs[eown_def, ALL_DISTINCT_APPEND] >> metis_tac[]
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
       (if cstat_of es' f = CRefused then Refused else Connecting) ∧
     ¬(gc (EL (cl cm f) w.chans)).shut) ⇒
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

Theorem cl_cons:
  cl ((f, n) :: cm) g = if g = f then n else cl cm g
Proof
  rw[cl_def]
QED

Theorem ev_rel_cl_lt:
  ev_rel lfd a cm es w ∧ MEM g (MAP FST cm) ⇒ cl cm g < LENGTH w.chans
Proof
  rw[ev_rel_def, EVERY_MEM, cl_def] >>
  Cases_on ‘ALOOKUP cm g’ >> gvs[ALOOKUP_NONE] >> metis_tac[ALOOKUP_SOME_MEM_SND]
QED

(* The world's fds in use: the listener and one per handle *)
Theorem ev_used_len:
  ev_rel lfd a cm es w ∧ eown lfd es ⇒
  ep_used w = lfd :: MAP FST w.open_fds ∧
  LENGTH w.open_fds = LENGTH es.p.b.tbl + LENGTH es.ctbl
Proof
  strip_tac >> conj_tac >- gvs[ep_used_def, ev_rel_def] >>
  ‘set (MAP FST w.open_fds) = set (MAP SND es.p.b.tbl ++ MAP SND es.ctbl)’
    by (gvs[ev_rel_def, EXTENSION] >> metis_tac[]) >>
  ‘ALL_DISTINCT (MAP SND es.p.b.tbl ++ MAP SND es.ctbl)’
    by gvs[eown_def, ALL_DISTINCT_APPEND] >>
  ‘ALL_DISTINCT (MAP FST w.open_fds)’ by gvs[ev_rel_def] >>
  metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET, LENGTH_MAP, LENGTH_APPEND]
QED

(* EConnect with a socket: the new fd f, if fresh and the world's
   allocation, is a new connecting channel (numbered next) *)
Theorem ev_connect:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
  edo lfd hw (wl, es) (EConnect p) = SOME (r, (wl', es'), evs) ∧ r ≠ EConnected NONE ⇒
  ∃f. es'.ctbl = (hdl lfd es.p.b.nxt, f) :: es.ctbl ∧
      (¬MEM f (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl) ∧
       w.alloc (LENGTH w.chans) (ep_used w) = f ⇒
       ∃w' hs'. ehdo lfd (w, hs) (EConnect p) = SOME (r, (w', hs')) ∧
                ev_rel lfd a ((f, LENGTH w.chans) :: cm) es' w' ∧ eown lfd es' ∧
                ehs_rel hs' es' ∧
                w'.listening = w.listening ∧ w'.alloc = w.alloc ∧ w'.env = w.env ∧
                w'.clock = w.clock ∧ w'.hist = w.hist ∧
                LENGTH w'.chans = LENGTH w.chans + 1 ∧
                es'.p.b.nxt = es.p.b.nxt + 1 ∧ es'.p.acq = es.p.acq)
Proof
  strip_tac >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >>
  simp[edo_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac ‘(hn, f) :: es.ctbl’ >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac ‘<| p := _; ctbl := _; cst := _; settling := _; early := ely |>’ >>
  ‘EVERY (λ(f, c). c ≠ CPending) ely ∧ ALL_DISTINCT (MAP FST ely) ∧
   ∀g. MEM g (MAP FST ely) ⇔ MEM g (MAP FST es.early) ∨ (g = f ∧ ely ≠ es.early)’
    by (‘¬MEM f (MAP FST es.early)’ by (gvs[eown_def] >> metis_tac[]) >>
        simp[Abbr ‘ely’] >> rw[] >> gvs[eown_def] >> TRY (metis_tac[]) >>
        every_case_tac >> gvs[]) >>
  ‘∀X. ep_used (w with chans := X) = ep_used w’ by simp[ep_used_def] >>
  drule_all ev_used_len >> strip_tac >>
  ‘LENGTH es.p.b.tbl + LENGTH es.ctbl ≤ es.p.b.nxt’ by metis_tac[eown_count] >>
  ‘es.p.b.nxt + 1 < dimword (:64)’
    by (irule hdln_suc_lt >> qexists_tac ‘lfd’ >> simp[dimword_64]) >>
  ‘hs.nxt = es.p.b.nxt’ by gvs[ehs_rel_def] >>
  simp[ehdo_def, ep_connect_def, ep_alloc_def, eh_new_def] >>
  ‘∀i. i < es.p.b.nxt ⇒ hdl lfd i ≠ hn’
    by (rw[Abbr ‘hn’] >> irule hdl_fresh >> simp[]) >>
  ‘ALOOKUP es.p.b.tbl hn = NONE ∧ ALOOKUP es.ctbl hn = NONE ∧ ¬MEM hn es.settling’
    by (gvs[eown_def, pown_def, l1hdl_hdl] >> rpt conj_tac
        >- (Cases_on ‘ALOOKUP es.p.b.tbl hn’ >> simp[] >> res_tac >> metis_tac[])
        >- (Cases_on ‘ALOOKUP es.ctbl hn’ >> simp[] >> res_tac >> metis_tac[])
        >> strip_tac >> res_tac >> metis_tac[]) >>
  ‘¬MEM hn (MAP FST es.p.b.tbl) ∧ ¬MEM hn (MAP FST es.ctbl)’ by gvs[ALOOKUP_NONE] >>
  ‘¬MEM f (MAP FST w.open_fds)’ by (gvs[ev_rel_def] >> metis_tac[]) >>
  ‘SUC (LENGTH es.ctbl + LENGTH es.p.b.tbl) < 18446744073709551616’ by fs[] >>
  ‘w.alloc (LENGTH w.chans) (lfd :: MAP FST w.open_fds) = f’ by gvs[] >>
  simp[] >> rpt conj_tac
  >- (‘∀g. MEM g (MAP FST cm) ⇒ cl cm g < LENGTH w.chans’ by metis_tac[ev_rel_cl_lt] >>
      qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >>
      simp[ev_rel_def, cl_cons, cstat_of_def, inb_of_def] >> strip_tac >>
      rpt conj_tac
      >- (irule MAP_CONG >> rw[cl_cons] >> gvs[])
      >- metis_tac[]
      >- (gvs[EVERY_MEM] >> strip_tac >> res_tac >> gvs[])
      >- (gvs[EVERY_MEM] >> rw[] >> res_tac >> simp[])
      >- (rpt gen_tac >> strip_tac >>
          ‘f' ≠ f’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          qpat_x_assum ‘∀h f'. ALOOKUP es.p.b.tbl h = _ ⇒ _’ drule >> strip_tac >>
          ‘cl cm f' < LENGTH w.chans’ by (qpat_assum ‘∀g. MEM g (MAP FST cm) ⇒ _’ irule >> simp[]) >>
          simp[EL_APPEND1])
      >- (rpt gen_tac >> Cases_on ‘hn = h’ >> simp[]
          >- (strip_tac >> gvs[] >> simp[EL_LENGTH_APPEND, new_chan_def]) >>
          strip_tac >> ‘f' ≠ f’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          qpat_x_assum ‘∀h f'. ALOOKUP es.ctbl h = _ ⇒ _’ drule >> strip_tac >>
          ‘cl cm f' < LENGTH w.chans’ by (qpat_assum ‘∀g. MEM g (MAP FST cm) ⇒ _’ irule >> simp[]) >>
          simp[EL_APPEND1, ALOOKUP_ADELKEY])
      >> rpt gen_tac >> strip_tac >> ‘f' ≠ f’ by (strip_tac >> gvs[]) >>
      qpat_x_assum ‘∀f. MEM f es.p.acq ⇒ _’ drule >> strip_tac >>
      ‘cl cm f' < LENGTH w.chans’ by (qpat_assum ‘∀g. MEM g (MAP FST cm) ⇒ _’ irule >> simp[]) >>
      simp[EL_APPEND1])
  >- (qpat_x_assum ‘eown _ _’ mp_tac >>
      simp[eown_def, pown_def, cstat_of_def, l1hdl_hdl, ALOOKUP_ADELKEY, inb_of_def] >>
      strip_tac >>
      gvs[ALL_DISTINCT_APPEND, inb_of_def] >> rpt conj_tac >> rpt strip_tac >> gvs[] >>
      TRY (res_tac >> qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
      TRY (metis_tac[] >> NO_TAC) >>
      TRY (qexists_tac ‘es.p.b.nxt’ >> gvs[markerTheory.Abbrev_def] >> NO_TAC) >>
      qpat_x_assum ‘(if _ then _ else _) = SOME _’ mp_tac >> rw[] >> gvs[] >>
      TRY (qexists_tac ‘es.p.b.nxt’ >> gvs[markerTheory.Abbrev_def] >> NO_TAC) >>
      TRY (strip_tac >> gvs[] >> NO_TAC) >>
      TRY (qpat_x_assum ‘∀h f'. ALOOKUP es.ctbl h = SOME f' ⇒ _’ drule >> strip_tac >>
           qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
      strip_tac >> qpat_x_assum ‘∀h f'. ALOOKUP es.ctbl h = SOME f' ⇒ _’ drule >>
      strip_tac >> imp_res_tac ALOOKUP_SOME_MEM_SND >>
      Cases_on ‘w.alloc (LENGTH w.chans) (lfd::MAP FST w.open_fds) = f'’ >> gvs[])
  >> qpat_x_assum ‘ehs_rel _ _’ mp_tac >> simp[ehs_rel_def] >> strip_tac >> conj_tac
  >- (gen_tac >> Cases_on ‘h = hn’ >> simp[])
  >> gen_tac >> Cases_on ‘h = hn’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The fetch, through a version-2 view of the endpoint world: the
   prefetching part's fetch lemma (fetch_rel) is about a version-2 world;
   the endpoint world agrees with that world on its up channels
   ------------------------------------------------------------------------ *)

(* The version-2 world the prefetching part sees: the clients are the
   channels, the open fds its own *)
Definition v2v_def:
  v2v lfd cm es w =
    <| listening := [(lfd, MAP (cl cm) es.p.acq)];
       clients := MAP (λc. <| incoming := c.inbox; peer_closed := c.peer_eof;
                              outgoing := c.sent |>) w.chans;
       open_fds := FILTER (λ(f, j). MEM f (MAP SND es.p.b.tbl)) w.open_fds;
       reserved := []; alloc := w.alloc; future := [||] |>
End

(* A version-2 world and an endpoint world: the same listener queue and
   channel count; the up channels' streams agree *)
Definition vagree_def:
  vagree lfd a s w ⇔
    (∃q. s.listening = [(lfd, q)] ∧ w.listening = [(lfd, a, q)]) ∧
    LENGTH s.clients = LENGTH w.chans ∧
    ∀j. j < LENGTH w.chans ∧ (EL j w.chans).status = Up ⇒
        (EL j s.clients).incoming = (EL j w.chans).inbox ∧
        ((EL j s.clients).peer_closed ⇔ (EL j w.chans).peer_eof)
End

(* A version-2 arrival as an endpoint arrival (connects: to the listener's
   address) *)
Definition conv_def:
  conv a (Connect2 l) = Incoming a ∧
  conv a (Data2 j bs) = PData j bs ∧
  conv a (Eof2 j) = PEof j
End

(* What a non-settling arrival leaves: the channels' statuses and shut
   flags, a channel not up untouched, new channels up *)
Definition ep_grows_def:
  ep_grows w w' ⇔
    LENGTH w.chans ≤ LENGTH w'.chans ∧
    (∀j. j < LENGTH w.chans ⇒
         (EL j w'.chans).status = (EL j w.chans).status ∧
         (EL j w'.chans).shut = (EL j w.chans).shut ∧
         ((EL j w.chans).status ≠ Up ⇒ EL j w'.chans = EL j w.chans)) ∧
    (∀j. LENGTH w.chans ≤ j ∧ j < LENGTH w'.chans ⇒
         (EL j w'.chans).status = Up ∧ ¬(EL j w'.chans).shut) ∧
    w'.open_fds = w.open_fds ∧ w'.reserved = w.reserved ∧ w'.alloc = w.alloc ∧
    w'.takes = w.takes ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist ∧
    w'.calls = w.calls
End

Theorem ep_grows_refl[simp]:
  ep_grows w w
Proof
  simp[ep_grows_def]
QED

Theorem ep_grows_trans:
  ep_grows w1 w2 ∧ ep_grows w2 w3 ⇒ ep_grows w1 w3
Proof
  rw[ep_grows_def] >> rpt strip_tac >> res_tac >> gvs[] >>
  Cases_on ‘j < LENGTH w2.chans’ >> gvs[] >> res_tac >> gvs[] >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]
QED

Theorem vagree_deliver:
  vagree lfd a s w ∧ (∀l. x = Connect2 l ⇒ l = lfd) ⇒
  vagree lfd a (deliver2 s x) (ep_deliver w (conv a x)) ∧
  ep_grows w (ep_deliver w (conv a x))
Proof
  Cases_on ‘x’ >> simp[conv_def] >> strip_tac
  >- (gvs[vagree_def, deliver2_def, ep_deliver_def, AFUPDKEY_def, ep_grows_def] >>
      rw[EL_APPEND_EQN, empty_conn_def, new_chan_def] >> gvs[] >>
      ‘j = LENGTH w.chans’ by simp[] >> gvs[])
  >- (gvs[vagree_def, deliver2_def, ep_deliver_def, ep_grows_def] >>
      rw[upd_chan_def, update_client_def, EL_LUPDATE] >> rw[] >> gvs[])
  >> gvs[vagree_def, deliver2_def, ep_deliver_def, ep_grows_def] >>
  rw[upd_chan_def, update_client_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem vagree_deliver_all:
  ∀as s w. vagree lfd a s w ∧ EVERY (λx. ∀l. x = Connect2 l ⇒ l = lfd) as ⇒
           vagree lfd a (FOLDL deliver2 s as) (FOLDL ep_deliver w (MAP (conv a) as)) ∧
           ep_grows w (FOLDL ep_deliver w (MAP (conv a) as))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  drule_all vagree_deliver >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  metis_tac[ep_grows_trans]
QED

Theorem arrs_connects:
  ∀l cm k as cm' k'.
    arrs lfd (cm, k) l = (as, (cm', k')) ⇒ EVERY (λx. ∀l. x = Connect2 l ⇒ l = lfd) as
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* The fds a fetch log accepted *)
Definition fconns_def:
  fconns [] = [] ∧
  fconns (FConn f :: l) = f :: fconns l ∧
  fconns (FData f bs :: l) = fconns l ∧
  fconns (FEof f :: l) = fconns l ∧
  fconns (FReset f :: l) = fconns l
End

Theorem arrs_new:
  ∀l cm k as cm' k'.
    arrs lfd (cm, k) l = (as, (cm', k')) ⇒
    ∃new. cm' = new ++ cm ∧ (∀f. MEM f (MAP FST new) ⇔ MEM f (fconns l)) ∧
          EVERY (λj. k ≤ j) (MAP SND new)
Proof
  Induct >> simp[arrs_def, fconns_def] >> Cases >> simp[arrs_def, fconns_def] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[]
  >- (gvs[EVERY_MEM] >> rw[] >- metis_tac[] >> res_tac >> simp[])
  >> qexists_tac ‘new’ >> simp[]
QED

Theorem ALL_DISTINCT_MAP_FILTER_FST:
  ∀l. ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP FST (FILTER P l))
Proof
  Induct >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* The view of a world in the relation is in the prefetching part's
   relation, and agrees with the world *)
Theorem ev_pv:
  ev_rel lfd a cm es w ∧ eown lfd es ⇒
  pv_rel lfd cm es.p (v2v lfd cm es w) ∧ vagree lfd a (v2v lfd cm es w) w
Proof
  strip_tac >>
  ‘∀g. MEM g (MAP FST cm) ⇒ cl cm g < LENGTH w.chans’ by metis_tac[ev_rel_cl_lt] >>
  qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >>
  simp[ev_rel_def, pv_rel_def, vagree_def, v2v_def, EL_MAP] >> strip_tac >>
  rpt conj_tac
  >- (irule ALL_DISTINCT_MAP_FILTER_FST >> simp[])
  >- (gen_tac >> eq_tac
      >- (rw[MEM_MAP, MEM_FILTER] >> pairarg_tac >> gvs[] >> metis_tac[]) >>
      strip_tac >>
      ‘MEM f (MAP FST w.open_fds)’
        by (qpat_x_assum ‘∀f. MEM f (MAP FST w.open_fds) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
            simp[]) >>
      pop_assum (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
      rw[MEM_MAP, MEM_FILTER] >> qexists_tac ‘y’ >> PairCases_on ‘y’ >> gvs[] >>
      gvs[MEM_MAP] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  ‘MEM f (MAP SND es.p.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
  ‘cl cm f < LENGTH w.chans’ by metis_tac[] >>
  simp[ALOOKUP_FILTER, EL_MAP]
QED

Theorem fconns_APPEND:
  ∀l1 l2. fconns (l1 ++ l2) = fconns l1 ++ fconns l2
Proof
  Induct >> simp[fconns_def] >> Cases >> simp[fconns_def]
QED

(* A fetch's accepted fds: queued, and new to L0 *)
Theorem fetch_acq:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ fds_lt w ⇒
    ps'.acq = ps.acq ++ fconns log ∧
    (∀f. MEM f (fconns log) ⇒ ¬MEM f (l0_used w)) ∧
    (∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w'))
Proof
  Induct >- simp[pf_fetch_def, fconns_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl)’ >>
      Cases_on ‘pf_fetch lfd hw fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
      PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
      ‘l0_rely w1’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule_all l0_do_rely >> simp[]) >>
      ‘fds_lt w1’ by (drule_all sys_accept_fds_lt >> simp[]) >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule l0_do_used >> simp[]) >>
      first_x_assum drule_all >> strip_tac >>
      simp[fconns_APPEND] >>
      Cases_on ‘l0_res_of out’ >> gvs[fconns_def]
      >- (drule_all sys_accept_fresh >> strip_tac >> rw[] >> metis_tac[]) >>
      rw[] >> metis_tac[]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl)’ >>
  Cases_on ‘pf_fetch lfd hw fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_rely w1’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        drule_all l0_do_rely >> simp[]) >>
  ‘l0_used w1 = l0_used w ∧ w1.fd_limit = w.fd_limit’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        imp_res_tac l0_do_env >> drule l0_do_used >> simp[]) >>
  ‘fds_lt w1’ by gvs[fds_lt_def] >>
  first_x_assum drule_all >> strip_tac >>
  ‘fconns fl = [] ∧ ps1.acq = ps.acq’
    by (Cases_on ‘l0_res_of out’ >> gvs[AllCaseEqs(), fconns_def] >> rw[] >> gvs[fconns_def]) >>
  gvs[fconns_APPEND]
QED

Theorem cl_append:
  cl (new ++ cm) f = if MEM f (MAP FST new) then cl new f else cl cm f
Proof
  Cases_on ‘ALOOKUP new f’ >> simp[cl_def, ALOOKUP_APPEND] >> gvs[ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_MEM >> rw[] >> gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem cl_new_mem:
  MEM f (MAP FST new) ⇒ MEM (cl new f) (MAP SND new)
Proof
  rw[cl_def] >> Cases_on ‘ALOOKUP new f’ >> gvs[ALOOKUP_NONE] >>
  metis_tac[ALOOKUP_SOME_MEM_SND]
QED

(* Back from the view: the world with the fetched arrivals delivered is in
   the relation with the state after the fetch *)
Theorem ev_back:
  ev_rel lfd a cm es w ∧ eown lfd es ∧
  pv_rel lfd (new ++ cm) ps' s' ∧ vagree lfd a s' w' ∧ ep_grows w w' ∧
  s'.open_fds = FILTER (λ(f, j). MEM f (MAP SND es.p.b.tbl)) w.open_fds ∧
  s'.alloc = w.alloc ∧ ps'.b.tbl = es.p.b.tbl ∧
  EVERY (λj. LENGTH w.chans ≤ j) (MAP SND new) ∧
  (∀f. MEM f (MAP FST new) ⇒
       ¬MEM f (MAP SND es.ctbl) ∧ ¬MEM f es.p.acq ∧ ¬MEM f (MAP SND es.p.b.tbl)) ∧
  (∀f. MEM f ps'.acq ⇒ MEM f es.p.acq ∨ MEM f (MAP FST new)) ⇒
  ev_rel lfd a (new ++ cm) (es with p := ps') w'
Proof
  strip_tac >>
  ‘∀g. MEM g (MAP FST cm) ⇒ cl cm g < LENGTH w.chans’ by metis_tac[ev_rel_cl_lt] >>
  ‘LENGTH s'.clients = LENGTH w'.chans’ by gvs[vagree_def] >>
  qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >>
  simp[ev_rel_def, pv_rel_def, cstat_of_def, inb_of_def] >>
  ntac 2 (disch_then strip_assume_tac) >> gvs[ep_grows_def] >> rpt conj_tac
  >- gvs[vagree_def]
  >- (rpt gen_tac >> strip_tac >>
      ‘MEM f (MAP SND es.p.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
      qpat_x_assum ‘∀h f. ALOOKUP es.p.b.tbl h = SOME f ⇒ (MEM f (MAP FST new) ∨ _) ∧ _’
        drule >> strip_tac >>
      qpat_x_assum ‘∀h f. ALOOKUP es.p.b.tbl h = SOME f ⇒ MEM f (MAP FST cm) ∧ _’
        drule >> strip_tac >>
      gvs[ALOOKUP_FILTER] >>
      ‘cl cm f < LENGTH w.chans’ by metis_tac[] >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘cl cm f’ mp_tac) >>
      simp[] >> strip_tac >> gvs[vagree_def])
  >- (rpt gen_tac >> strip_tac >>
      ‘MEM f (MAP SND es.ctbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
      ‘¬MEM f (MAP FST new)’ by metis_tac[] >>
      qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ _’ drule >> strip_tac >>
      ‘cl cm f < LENGTH w.chans’ by metis_tac[] >>
      simp[cl_append] >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘cl cm f’ mp_tac) >>
      simp[] >> rw[] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘∀f. MEM f ps'.acq ⇒ (MEM f (MAP FST new) ∨ _) ∧ _’ drule >> strip_tac >>
  ‘(EL (cl (new ++ cm) f) w'.chans).status = Up ∧ ¬(EL (cl (new ++ cm) f) w'.chans).shut’
    by (Cases_on ‘MEM f (MAP FST new)’ >> simp[cl_append]
        >- (drule cl_new_mem >> strip_tac >>
            qpat_x_assum ‘∀j. LENGTH w.chans ≤ j ∧ _ ⇒ _’ irule >> gvs[EVERY_MEM]) >>
        ‘MEM f es.p.acq’ by metis_tac[] >>
        qpat_x_assum ‘∀f. MEM f es.p.acq ⇒ _’ drule >> strip_tac >>
        ‘cl cm f < LENGTH w.chans’ by metis_tac[] >>
        qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘cl cm f’ mp_tac) >>
        simp[]) >>
  ‘cl (new ++ cm) f < LENGTH w'.chans’
    by (Cases_on ‘MEM f (MAP FST new)’ >> simp[cl_append]
        >- (drule cl_new_mem >> gvs[EVERY_MEM]) >>
        ‘MEM f (MAP FST cm)’ by metis_tac[] >>
        ‘cl cm f < LENGTH w.chans’ by metis_tac[] >> simp[]) >>
  gvs[vagree_def]
QED

Theorem FOLDL_deliver2_open_fds[simp]:
  ∀as s. (FOLDL deliver2 s as).open_fds = s.open_fds ∧
         (FOLDL deliver2 s as).reserved = s.reserved
Proof
  Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def]
QED

(* The fetch: the fetched arrivals delivered to the endpoint world keep the
   relation (with the accepted connections' channels numbered next) *)
Theorem ev_fetch:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ l0owne lfd w0 es ∧ l0_rely w0 ∧ fds_lt w0 ∧
  pf_fetch lfd hw fs (w0, es.p) = SOME ((w0', ps'), log, evs) ∧
  arrs lfd (cm, LENGTH w.chans) log = (as, (cm', k')) ∧
  (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND es.p.b.tbl)) ∧
  (∀f j. MEM (f, j) cm' ∧ LENGTH w.chans ≤ j ⇒ ∀used. ¬MEM f used ⇒ w.alloc j used = f) ∧
  k' + 1 < dimword (:64) ⇒
  ev_rel lfd a cm' (es with p := ps') (FOLDL ep_deliver w (MAP (conv a) as)) ∧
  eown lfd (es with p := ps') ∧ l0owne lfd w0' (es with p := ps') ∧
  l0_rely w0' ∧ fds_lt w0' ∧
  ep_grows w (FOLDL ep_deliver w (MAP (conv a) as)) ∧
  k' = LENGTH (FOLDL ep_deliver w (MAP (conv a) as)).chans ∧
  ps'.b.tbl = es.p.b.tbl ∧ ps'.b.nxt = es.p.b.nxt ∧ ps'.b.closing = es.p.b.closing
Proof
  strip_tac >>
  drule_all ev_pv >> strip_tac >>
  qabbrev_tac ‘s = v2v lfd cm es w’ >>
  ‘LENGTH s.clients = LENGTH w.chans ∧ s.alloc = w.alloc ∧
   s.open_fds = FILTER (λ(f, j). MEM f (MAP SND es.p.b.tbl)) w.open_fds’
    by simp[Abbr ‘s’, v2v_def] >>
  ‘l0own lfd w0 es.p’ by gvs[l0owne_def] >>
  ‘arrs lfd (cm, LENGTH s.clients) log = (as, (cm', k'))’ by simp[] >>
  ‘∀f j. MEM (f, j) cm' ∧ LENGTH s.clients ≤ j ⇒ ∀used. ¬MEM f used ⇒ s.alloc j used = f’
    by metis_tac[] >>
  ‘pown lfd es.p’ by gvs[eown_def] >>
  drule_all fetch_rel >> strip_tac >>
  drule_all fetch_acq >> strip_tac >>
  drule arrs_new >> strip_tac >>
  drule arrs_connects >> strip_tac >>
  drule_all vagree_deliver_all >> strip_tac >>
  ‘∀f. MEM f (MAP FST new) ⇒
       ¬MEM f (MAP SND es.ctbl) ∧ ¬MEM f es.p.acq ∧ ¬MEM f (MAP SND es.p.b.tbl)’
    by (rpt strip_tac >> gvs[l0owne_def, l0own_def] >> metis_tac[]) >>
  ‘LENGTH (FOLDL ep_deliver w (MAP (conv a) as)).chans =
   LENGTH (FOLDL deliver2 s as).clients’ by gvs[vagree_def] >>
  rpt conj_tac
  >- (gvs[] >> irule ev_back >> simp[] >> qexists_tac ‘FOLDL deliver2 s as’ >>
      simp[] >> rw[] >> gvs[MEM_APPEND] >> metis_tac[])
  >- (irule eown_p_disj >> simp[] >> rpt strip_tac >> gvs[MEM_APPEND] >>
      gvs[eown_def, ALL_DISTINCT_APPEND, l0owne_def, l0own_def] >> metis_tac[])
  >- (gvs[l0owne_def])
  >> gvs[]
QED

(* ------------------------------------------------------------------------
   The L0 side of connects: sys_connect's fd is new; sys_connerr changes no
   fd
   ------------------------------------------------------------------------ *)

Theorem res_val_enc:
  v < 2 ** 64 ⇒
  res_val (enc_res (Ok v)) = v ∧ res_val (enc_err_val w e v) = v
Proof
  rw[res_val_def, enc_res_def, enc_err_val_def] >>
  ‘LENGTH (n2w8 v) = 8’ by simp[LENGTH_n2w8] >>
  simp[TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >> irule w82n_n2w8 >> simp[]
QED

Theorem sys_connerr_l0:
  sys_connerr f w = SOME (out, w', ev) ∧ l0_rely w ⇒
  l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧ l0_rely w'
Proof
  strip_tac >>
  ‘l0_rely w'’ by (gvs[sys_connerr_def] >> drule_all l0_do_rely >> simp[]) >>
  gvs[sys_connerr_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, l0_connerr_def, AllCaseEqs()] >> simp[upd_lchan_def]
QED

Theorem l0_used_cons:
  (MEM g (l0_used (w with <| chans := c; open_fds := x :: w.open_fds |>)) ⇔
     g = FST x ∨ MEM g (l0_used w)) ∧
  (MEM g (l0_used (w with <| chans := c; open_fds := x :: w.open_fds; hist := h |>)) ⇔
     g = FST x ∨ MEM g (l0_used w)) ∧
  l0_used (w with hist := h) = l0_used w ∧
  (w with <| chans := c; open_fds := o'; hist := h |>).fd_limit = w.fd_limit ∧
  (w with <| chans := c; open_fds := o' |>).fd_limit = w.fd_limit
Proof
  simp[l0_used_def] >> metis_tac[]
QED

Theorem sys_connect_l0:
  l0_rely w ∧ fds_lt w ∧ sys_connect p w = SOME (out, w', ev) ⇒
  l0_rely w' ∧ fds_lt w' ∧ (∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w')) ∧
  (res_val out ≠ 0 ⇒
     MEM (n2w (res_val out)) (l0_used w') ∧ ¬MEM (n2w (res_val out)) (l0_used w))
Proof
  strip_tac >>
  ‘l0_rely w'’ by (gvs[sys_connect_def] >> drule_all l0_do_rely >> simp[]) >>
  simp[] >>
  qpat_x_assum ‘sys_connect _ _ = _’ mp_tac >>
  simp[sys_connect_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >> strip_tac >>
  qabbrev_tac ‘tw = l0_tick «sys_connect» w’ >>
  ‘l0_used tw = l0_used w ∧ tw.fd_limit = w.fd_limit’ by simp[Abbr ‘tw’] >>
  ‘fds_lt tw’ by gvs[fds_lt_def] >>
  ‘w.fd_limit ≤ 2 ** 31’ by gvs[l0_rely_def] >>
  ‘¬MEM (lowest_fd tw) (l0_used tw)’ by (irule lowest_fd_fresh >> fs[]) >>
  ‘w2n (lowest_fd tw) < 2 ** 64’
    by (assume_tac (w2n_lt |> INST_TYPE [alpha |-> “:64”]) >> fs[]) >>
  gvs[l0_call_def, l0_connect_def, fail_def, l0_alloc_def, AllCaseEqs()] >>
  gvs[res_val_enc, fds_lt_def, l0_used_cons] >> rw[] >> gvs[] >>
  fs[upd_lchan_def, l0_used_cons]
QED

(* The prefetching part's actions close only its own fds *)
Theorem pdo_keep:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ⇒
  ∀g. MEM g (l0_used w) ∧ ¬MEM g (MAP SND ps.b.tbl) ⇒ MEM g (l0_used w')
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- gvs[AllCaseEqs()]
  >- (gvs[AllCaseEqs()] >> rw[] >>
      TRY (PairCases_on ‘z’ >> gvs[] >> drule_all l1_close_l0 >> strip_tac >>
           first_x_assum irule >> simp[] >> strip_tac >> gvs[] >>
           metis_tac[ALOOKUP_SOME_MEM_SND]))
  >> pairarg_tac >> gvs[] >> rename1 ‘l1do _ _ _ = SOME (r, (w', b'), evs)’ >>
  drule_all l1do_write_l0 >> simp[]
QED

Theorem pdo_l0owne:
  pdo lfd (wl, es.p) a = SOME (r, (wl', ps'), evs) ∧
  l0_rely wl ∧ fds_lt wl ∧ l0owne lfd wl es ∧ eown lfd es ⇒
  l0_rely wl' ∧ fds_lt wl' ∧ l0owne lfd wl' (es with p := ps')
Proof
  strip_tac >> ‘pown lfd es.p ∧ l0own lfd wl es.p’ by gvs[eown_def, l0owne_def] >>
  drule_all pdo_l0 >> strip_tac >> imp_res_tac pdo_keep >>
  simp[l0owne_def] >> rw[] >>
  qpat_x_assum ‘∀g. ¬MEM g (MAP SND es.p.b.tbl) ⇒ _’ irule >>
  gvs[l0owne_def, eown_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* Any action: L0's rely, the fd bound, and L1's fds open in L0 *)
Theorem edo_l0:
  edo lfd hw (wl, es) a = SOME (r, (wl', es'), evs) ∧
  l0_rely wl ∧ fds_lt wl ∧ l0owne lfd wl es ∧ eown lfd es ⇒
  l0_rely wl' ∧ fds_lt wl' ∧ l0owne lfd wl' es'
Proof
  strip_tac >> Cases_on ‘a’ >| [
    (* EAccept *)
    gvs[edo_def] >> PairCases_on ‘z’ >> gvs[] >> drule_all pdo_l0owne >> simp[],
    (* ERead *)
    gvs[edo_def, AllCaseEqs()]
      >- (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_l0owne >> simp[])
      >> PairCases_on ‘z’ >> gvs[] >> rename1 ‘l1_close f _ = SOME ((wl', b'), evs)’ >>
      drule_all l1_close_l0 >> strip_tac >>
      ‘MEM f (MAP SND es.ctbl) ∧ ALL_DISTINCT (MAP SND es.ctbl) ∧ ALL_DISTINCT (MAP FST es.ctbl) ∧
       ¬MEM f (MAP SND es.p.b.tbl) ∧ ¬MEM f es.p.b.closing ∧ ¬MEM f es.p.acq ∧ f ≠ lfd’
        by (imp_res_tac ALOOKUP_SOME_MEM_SND >> gvs[eown_def, ALL_DISTINCT_APPEND] >>
            metis_tac[]) >>
      gvs[fds_lt_def, l0owne_def, l0own_def, ec_del_def, MEM_FILTER] >> rw[] >>
      TRY (first_x_assum irule >> metis_tac[] >> NO_TAC) >>
      first_x_assum irule >> metis_tac[MEM_SND_ADELKEY, MEM_SND_ADELKEY_sub],
    (* EWrite *)
    gvs[edo_def, AllCaseEqs()] >> PairCases_on ‘z’ >> gvs[] >> drule_all pdo_l0owne >> simp[],
    (* EConnect *)
    gvs[edo_def, AllCaseEqs()] >> drule_all sys_connect_l0 >> strip_tac >> simp[] >>
    gvs[l0owne_def, l0own_def, l1hdl_hdl] >> metis_tac[]]
QED

(* A connect's fd is new to L1 *)
Theorem edo_connect_fresh:
  edo lfd hw (wl, es) (EConnect p) = SOME (r, (wl', es'), evs) ∧ r ≠ EConnected NONE ∧
  l0_rely wl ∧ fds_lt wl ∧ l0owne lfd wl es ⇒
  ∀f. es'.ctbl = (hdl lfd es.p.b.nxt, f) :: es.ctbl ⇒
      ¬MEM f (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl)
Proof
  strip_tac >> gvs[edo_def, AllCaseEqs()] >> drule_all sys_connect_l0 >> strip_tac >>
  gvs[l0owne_def, l0own_def] >> metis_tac[]
QED

(* The connect handles are issued ones (part of eown) *)
Definition ciss_def:
  ciss lfd es ⇔ ∀h f. ALOOKUP es.ctbl h = SOME f ⇒ ∃i. i < es.p.b.nxt ∧ h = hdl lfd i
End

Theorem edo_ciss:
  edo lfd hw (wl, es) a = SOME (r, (wl', es'), evs) ∧ ciss lfd es ⇒
  ciss lfd es' ∧ es.p.b.nxt ≤ es'.p.b.nxt
Proof
  strip_tac >> Cases_on ‘a’ >| [
    gvs[edo_def] >> PairCases_on ‘z’ >> gvs[pdo_def, AllCaseEqs(), ciss_def] >>
    rw[] >> res_tac >> qexists_tac ‘i’ >> simp[],
    gvs[edo_def, AllCaseEqs()] >> TRY (PairCases_on ‘z’) >> gvs[]
    >- (gvs[pdo_def, AllCaseEqs(), ciss_def] >> TRY (PairCases_on ‘z’) >> gvs[] >>
        imp_res_tac l1_close_b >> gvs[])
    >> imp_res_tac l1_close_b >> gvs[ciss_def, ec_del_def, ALOOKUP_ADELKEY] >>
    rw[] >> res_tac >> metis_tac[],
    gvs[edo_def, AllCaseEqs()] >> TRY (PairCases_on ‘z’) >> gvs[pdo_def] >>
    TRY (pairarg_tac >> gvs[] >> imp_res_tac l1do_write_tbl) >> gvs[ciss_def],
    gvs[edo_def, AllCaseEqs(), ciss_def, l1hdl_hdl] >> rw[]
    >- (qexists_tac ‘es.p.b.nxt’ >> simp[])
    >> res_tac >> qexists_tac ‘i’ >> simp[]]
QED

(* A connect handle still pending stays, with its fd, through any action *)
Theorem edo_keeps_pending:
  edo lfd hw (wl, es) a = SOME (r, (wl', es'), evs) ∧ ciss lfd es ∧
  ALOOKUP es.ctbl h = SOME f ∧ cstat_of es f = CPending ⇒
  ALOOKUP es'.ctbl h = SOME f ∧ cstat_of es' f = CPending
Proof
  strip_tac >> Cases_on ‘a’ >| [
    gvs[edo_def] >> PairCases_on ‘z’ >> gvs[cstat_of_def],
    gvs[edo_def, AllCaseEqs()]
    >- (PairCases_on ‘z’ >> gvs[cstat_of_def]) >>
    PairCases_on ‘z’ >> gvs[] >> rename1 ‘ALOOKUP es.ctbl c = SOME g’ >>
    ‘g ≠ f’ by (strip_tac >> gvs[]) >>
    ‘c ≠ h’ by (strip_tac >> gvs[]) >>
    simp[ec_del_def, ALOOKUP_ADELKEY, cstat_of_def] >> gvs[cstat_of_def],
    gvs[edo_def, AllCaseEqs()] >> PairCases_on ‘z’ >> gvs[cstat_of_def],
    gvs[edo_def, AllCaseEqs()] >>
    ‘h ≠ l1hdl lfd es.p.b.nxt’
      by (gvs[ciss_def, l1hdl_hdl] >> res_tac >> gvs[] >>
          irule hdl_fresh >> simp[]) >>
    simp[cstat_of_def, ALOOKUP_ADELKEY] >> rw[] >> gvs[cstat_of_def]]
QED

(* ------------------------------------------------------------------------
   A round's actions
   ------------------------------------------------------------------------ *)

(* The handles of a round's connects, in order *)
Definition conn_hdls_def:
  conn_hdls [] = [] ∧
  conn_hdls (EConnected (SOME h) :: rs) = h :: conn_hdls rs ∧
  conn_hdls (r :: rs) = conn_hdls rs
End

(* Their fds (the connect handles stay pending through the round) *)
Definition rfds_def:
  rfds es rs = MAP (λh. THE (ALOOKUP es.ctbl h)) (conn_hdls rs)
End

(* Their channels: numbered from k, in order (newest first, as cl reads) *)
Definition cnew_def:
  cnew k fs = REVERSE (ZIP (fs, GENLIST (λi. k + i) (LENGTH fs)))
End

Theorem cnew_thm:
  cnew k [] = [] ∧ cnew k (f :: fs) = cnew (k + 1) fs ++ [(f, k)]
Proof
  simp[cnew_def] >>
  ‘LENGTH fs + 1 = SUC (LENGTH fs)’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC[GENLIST_CONS] >> simp[combinTheory.o_DEF, ADD1] >>
  ‘(λx. k + (x + 1)) = (λi. i + (k + 1))’ by simp[FUN_EQ_THM] >> simp[]
QED


Theorem edo_conn_hdls:
  edo lfd hw (wl, es) act = SOME (r, ws', evs) ∧ (∀p. act ≠ EConnect p) ⇒ conn_hdls [r] = []
Proof
  Cases_on ‘act’ >> simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >> TRY (Cases_on ‘z0’) >> simp[conn_hdls_def] >>
  TRY (Cases_on ‘o'’) >> simp[conn_hdls_def]
QED

(* One action: the layer's action, with a connect's channel numbered next *)
Theorem ev_act:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
  l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ∧
  edo lfd hw (wl, es) act = SOME (r, (wl', es'), evs) ∧ r ≠ EConnected NONE ∧
  (∀f. MEM f (rfds es' [r]) ⇒ ∀used. ¬MEM f used ⇒ w.alloc (LENGTH w.chans) used = f) ⇒
  ∃w' hs'. ehdo lfd (w, hs) act = SOME (r, (w', hs')) ∧
    ev_rel lfd a (cnew (LENGTH w.chans) (rfds es' [r]) ++ cm) es' w' ∧ eown lfd es' ∧
    ehs_rel hs' es' ∧ l0owne lfd wl' es' ∧ l0_rely wl' ∧ fds_lt wl' ∧
    w'.alloc = w.alloc ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist ∧
    LENGTH w'.chans = LENGTH w.chans + LENGTH (conn_hdls [r]) ∧
    (∀h. MEM h (conn_hdls [r]) ⇒ ∃f. ALOOKUP es'.ctbl h = SOME f ∧ cstat_of es' f = CPending)
Proof
  strip_tac >> drule_all edo_l0 >> strip_tac >> simp[] >>
  Cases_on ‘act’ >| [
    (* EAccept *)
    drule_all ev_accept >> strip_tac >>
    ‘conn_hdls [r] = []’ by (qpat_x_assum ‘edo _ _ _ _ = _’ assume_tac >> drule edo_conn_hdls >> simp[]) >>
    simp[rfds_def, cnew_thm] >> metis_tac[],
    (* ERead *)
    drule_all ev_read >> strip_tac >>
    ‘conn_hdls [r] = []’ by (qpat_x_assum ‘edo _ _ _ _ = _’ assume_tac >> drule edo_conn_hdls >> simp[]) >>
    simp[rfds_def, cnew_thm] >> metis_tac[],
    (* EWrite *)
    drule_all ev_write >> strip_tac >>
    ‘conn_hdls [r] = []’ by (qpat_x_assum ‘edo _ _ _ _ = _’ assume_tac >> drule edo_conn_hdls >> simp[]) >>
    simp[rfds_def, cnew_thm] >> metis_tac[],
    (* EConnect *)
    ‘r = EConnected (SOME (hdl lfd es.p.b.nxt))’
      by gvs[edo_def, AllCaseEqs(), l1hdl_hdl] >>
    imp_res_tac edo_connect_fresh >>
    qpat_x_assum ‘edo _ _ _ _ = _’ assume_tac >>
    drule_all ev_connect >> strip_tac >>
    ‘rfds es' [r] = [f]’ by simp[rfds_def, conn_hdls_def] >>
    ‘cstat_of es' f = CPending’ by gvs[edo_def, AllCaseEqs(), cstat_of_def] >>
    ‘¬MEM f (lfd :: MAP SND es.p.b.tbl ++ es.p.b.closing ++ es.p.acq ++ MAP SND es.ctbl)’
      by metis_tac[] >>
    ‘ep_used w = lfd :: MAP FST w.open_fds’ by metis_tac[ev_used_len] >>
    ‘¬MEM f (ep_used w)’ by (simp[] >> gvs[ev_rel_def] >> metis_tac[]) >>
    ‘w.alloc (LENGTH w.chans) (ep_used w) = f’
      by (qpat_x_assum ‘∀f. MEM f (rfds es' [r]) ⇒ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
    qpat_x_assum ‘_ ∧ _ ⇒ ∃w' hs'. _’ mp_tac >> impl_tac >- gvs[] >> strip_tac >>
    gvs[conn_hdls_def, cnew_thm]]
QED

Theorem eown_ciss:
  eown lfd es ⇒ ciss lfd es
Proof
  rw[eown_def, ciss_def] >> res_tac >> metis_tac[]
QED

Theorem eacts_keeps_pending:
  ∀acts wl es rs evs wl' es' h f.
    eacts lfd hw (wl, es) acts = SOME (rs, evs, (wl', es')) ∧ ciss lfd es ∧
    ALOOKUP es.ctbl h = SOME f ∧ cstat_of es f = CPending ⇒
    ALOOKUP es'.ctbl h = SOME f ∧ cstat_of es' f = CPending
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all edo_keeps_pending >> strip_tac >>
  drule_all edo_ciss >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem cnew_append:
  ∀xs k. cnew k (xs ++ ys) = cnew (k + LENGTH xs) ys ++ cnew k xs
Proof
  Induct >> simp[cnew_thm] >> rpt gen_tac >> simp[ADD1]
QED

Theorem rfds_length:
  LENGTH (rfds es rs) = LENGTH (conn_hdls rs)
Proof
  simp[rfds_def]
QED

Theorem conn_hdls_cons:
  conn_hdls (r :: rs) = conn_hdls [r] ++ conn_hdls rs
Proof
  Cases_on ‘r’ >> simp[conn_hdls_def] >> rename1 ‘EConnected oh’ >>
  Cases_on ‘oh’ >> simp[conn_hdls_def]
QED

(* A connect's handle is pending, with its fd *)
Theorem edo_conn_pending:
  edo lfd hw (wl, es) act = SOME (r, (wl', es'), evs) ∧ MEM h (conn_hdls [r]) ⇒
  ∃f. ALOOKUP es'.ctbl h = SOME f ∧ cstat_of es' f = CPending
Proof
  strip_tac >> Cases_on ‘∃p. act = EConnect p’
  >- (gvs[edo_def, AllCaseEqs(), conn_hdls_def, cstat_of_def]) >>
  ‘conn_hdls [r] = []’ by (drule edo_conn_hdls >> metis_tac[]) >> gvs[]
QED

(* A round's actions: the layer's actions, its connects' channels numbered
   in order from the channel count *)
Theorem ev_acts:
  ∀acts cm es w hs wl rs evs wl' es'.
    ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
    l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ∧
    eacts lfd hw (wl, es) acts = SOME (rs, evs, (wl', es')) ∧ ¬MEM (EConnected NONE) rs ∧
    (∀f j. MEM (f, j) (cnew (LENGTH w.chans) (rfds es' rs)) ⇒
           ∀used. ¬MEM f used ⇒ w.alloc j used = f) ⇒
    ∃w' hs'. ehacts lfd (w, hs) acts = SOME (rs, (w', hs')) ∧
      ev_rel lfd a (cnew (LENGTH w.chans) (rfds es' rs) ++ cm) es' w' ∧ eown lfd es' ∧
      ehs_rel hs' es' ∧ l0owne lfd wl' es' ∧ l0_rely wl' ∧ fds_lt wl' ∧
      w'.alloc = w.alloc ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist ∧
      LENGTH w'.chans = LENGTH w.chans + LENGTH (conn_hdls rs)
Proof
  Induct >- simp[eacts_def, ehacts_def, rfds_def, conn_hdls_def, cnew_thm] >>
  rpt gen_tac >> rename1 ‘eacts _ _ _ (act :: acts)’ >> strip_tac >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ mp_tac >> simp[Once eacts_def] >>
  Cases_on ‘edo lfd hw (wl, es) act’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  rename1 ‘edo _ _ _ _ = SOME (r1, (wl1, es1), evs1)’ >> simp[] >>
  Cases_on ‘eacts lfd hw (wl1, es1) acts’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  rename1 ‘eacts _ _ _ acts = SOME (rs1, evs2, (wl', es'))’ >>
  ‘ciss lfd es1’ by metis_tac[edo_ciss, eown_ciss] >>
  ‘∀h. MEM h (conn_hdls [r1]) ⇒ ALOOKUP es'.ctbl h = ALOOKUP es1.ctbl h’
    by (rpt strip_tac >> drule_all edo_conn_pending >> strip_tac >>
        drule_all eacts_keeps_pending >> simp[]) >>
  ‘rfds es' (r1 :: rs1) = rfds es1 [r1] ++ rfds es' rs1’
    by (simp[rfds_def] >>
        ‘conn_hdls (r1 :: rs1) = conn_hdls [r1] ++ conn_hdls rs1’ by metis_tac[conn_hdls_cons] >>
        pop_assum SUBST1_TAC >>
        simp[MAP_APPEND] >> irule MAP_CONG >> simp[]) >>
  ‘LENGTH (rfds es1 [r1]) = LENGTH (conn_hdls [r1])’ by simp[rfds_length] >>
  ‘∀f. MEM f (rfds es1 [r1]) ⇒ ∀used. ¬MEM f used ⇒ w.alloc (LENGTH w.chans) used = f’
    by (rpt strip_tac >>
        ‘rfds es1 [r1] = [f]’
          by (Cases_on ‘rfds es1 [r1]’ >> gvs[] >>
              ‘LENGTH (conn_hdls [r1]) ≤ 1’
                by (Cases_on ‘r1’ >> simp[conn_hdls_def] >> rename1 ‘EConnected oh’ >>
                    Cases_on ‘oh’ >> simp[conn_hdls_def]) >>
              Cases_on ‘t’ >> gvs[]) >>
        qpat_x_assum ‘∀f j. MEM (f, j) _ ⇒ _’ irule >>
        simp[cnew_append, cnew_thm]) >>
  drule_all ev_act >> strip_tac >>
  rename1 ‘ehdo lfd (w, hs) act = SOME (r1, (w1, hs1))’ >>
  first_x_assum (qspecl_then [‘cnew (LENGTH w.chans) (rfds es1 [r1]) ++ cm’, ‘es1’, ‘w1’, ‘hs1’,
                              ‘wl1’, ‘rs1’, ‘evs2’, ‘wl'’, ‘es'’] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum ‘∀f j. MEM (f, j) (cnew _ (rfds es' (r1 :: rs1))) ⇒ _’ irule >>
      gvs[cnew_append]) >>
  strip_tac >>
  simp[ehacts_def] >>
  gvs[cnew_append] >>
  ‘LENGTH (conn_hdls (r1 :: rs1)) = LENGTH (conn_hdls [r1]) + LENGTH (conn_hdls rs1)’
    by metis_tac[conn_hdls_cons, LENGTH_APPEND] >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The tail's settling: settled connects' channels settle (Settle arrivals),
   up connect handles join the prefetching table
   ------------------------------------------------------------------------ *)

Theorem ALOOKUP_FILTER_SOME:
  ∀l. ALOOKUP l k = SOME v ∧ P (k, v) ⇒ ALOOKUP (FILTER P l) k = SOME v
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem ALOOKUP_FILTER_NONE:
  ∀l. ALOOKUP l k = NONE ⇒ ALOOKUP (FILTER P l) k = NONE
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem cstat_of_promote:
  cstat_of es f ≠ CUp ⇒ cstat_of (promote es) f = cstat_of es f
Proof
  rw[cstat_of_def, promote_def] >> Cases_on ‘ALOOKUP es.cst f’ >> gvs[]
  >- simp[ALOOKUP_FILTER_NONE] >>
  ‘ALOOKUP (FILTER (λ(f, c). c ≠ CUp) es.cst) f = SOME x’
    by (irule ALOOKUP_FILTER_SOME >> simp[]) >> simp[]
QED

(* Settles on distinct connecting channels *)
Theorem settles_deliver:
  ∀l w. ALL_DISTINCT (MAP FST l) ∧
        (∀j b. MEM (j, b) l ⇒ j < LENGTH w.chans ∧ (EL j w.chans).status = Connecting) ⇒
        let w' = FOLDL ep_deliver w (MAP (λ(j, b). Settle j b) l) in
          LENGTH w'.chans = LENGTH w.chans ∧
          w'.listening = w.listening ∧ w'.open_fds = w.open_fds ∧ w'.reserved = w.reserved ∧
          w'.alloc = w.alloc ∧ w'.takes = w.takes ∧ w'.env = w.env ∧ w'.clock = w.clock ∧
          w'.hist = w.hist ∧ w'.calls = w.calls ∧
          ∀k. k < LENGTH w.chans ⇒
              EL k w'.chans = case ALOOKUP l k of
                              | SOME b => EL k w.chans with status := (if b then Up else Refused)
                              | NONE => EL k w.chans
Proof
  Induct >> simp[FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  rename1 ‘Settle j b’ >>
  first_x_assum (qspec_then ‘ep_deliver w (Settle j b)’ mp_tac) >>
  ‘ep_deliver w (Settle j b) =
   upd_chan j (λc. c with status := if b then Up else Refused) w’
    by (simp[ep_deliver_def] >> metis_tac[]) >>
  simp[] >> impl_tac
  >- (rw[] >> res_tac >> simp[upd_chan_def, EL_LUPDATE] >> rw[] >> gvs[MEM_MAP] >>
      metis_tac[FST]) >>
  strip_tac >> simp[] >> rw[] >> simp[upd_chan_def, EL_LUPDATE] >> rw[] >>
  gvs[] >> Cases_on ‘ALOOKUP l j’ >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem ALOOKUP_FILTER_IMP:
  ∀l. ALL_DISTINCT (MAP FST l) ∧ ALOOKUP (FILTER P l) k = SOME v ⇒
      ALOOKUP l k = SOME v ∧ P (k, v)
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_FILTER, MEM_MAP] >> metis_tac[FST]
QED

(* Promotion moves handles between the tables: the same lookups *)
Theorem promote_lookup:
  ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl) ⇒
  (case ALOOKUP (promote es).p.b.tbl h of
   | SOME f => SOME f | NONE => ALOOKUP (promote es).ctbl h) =
  (case ALOOKUP es.p.b.tbl h of SOME f => SOME f | NONE => ALOOKUP es.ctbl h)
Proof
  rw[promote_def, ALOOKUP_APPEND, ALL_DISTINCT_APPEND] >>
  Cases_on ‘ALOOKUP es.ctbl h’ >> simp[]
  >- (simp[ALOOKUP_FILTER_NONE] >> CASE_TAC >> simp[]) >>
  rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
  ‘ALOOKUP es.p.b.tbl h = NONE’
    by (simp[ALOOKUP_NONE] >> metis_tac[ALOOKUP_SOME_MEM_FST]) >>
  Cases_on ‘cstat_of es f = CUp’
  >- (‘ALOOKUP (FILTER (λ(h, f). cstat_of es f = CUp) es.ctbl) h = SOME f’
        by (irule ALOOKUP_FILTER_SOME >> simp[]) >> simp[]) >>
  ‘ALOOKUP (FILTER (λ(h, f). cstat_of es f = CUp) es.ctbl) h = NONE’
    by (Cases_on ‘ALOOKUP (FILTER (λ(h, f). cstat_of es f = CUp) es.ctbl) h’ >> simp[] >>
        imp_res_tac ALOOKUP_FILTER_IMP >> gvs[]) >>
  simp[] >> irule ALOOKUP_FILTER_SOME >> simp[]
QED

(* The settled connects, and their Settle arrivals *)
Definition settled_def:
  settled es es5 =
    FILTER (λ(h, f). cstat_of es f = CPending ∧ cstat_of es5 f ≠ CPending) es.ctbl
End

Definition settles_def:
  settles cm es es5 =
    MAP (λ(h, f). Settle (cl cm f) (cstat_of es5 f = CUp)) (settled es es5)
End

(* After the Settle arrivals, a connect channel has its new status *)
Theorem settle_world:
  ev_rel lfd a cm es w ∧ eown lfd es ⇒
  let w' = FOLDL ep_deliver w (settles cm es es5) in
    LENGTH w'.chans = LENGTH w.chans ∧
    w'.listening = w.listening ∧ w'.open_fds = w.open_fds ∧ w'.reserved = w.reserved ∧
    w'.alloc = w.alloc ∧ w'.takes = w.takes ∧ w'.env = w.env ∧ w'.clock = w.clock ∧
    w'.hist = w.hist ∧ w'.calls = w.calls ∧
    (∀h f. ALOOKUP es.ctbl h = SOME f ⇒
       EL (cl cm f) w'.chans =
         if cstat_of es f = CPending ∧ cstat_of es5 f ≠ CPending
         then EL (cl cm f) w.chans with status := (if cstat_of es5 f = CUp then Up else Refused)
         else EL (cl cm f) w.chans) ∧
    (∀k. k < LENGTH w.chans ∧ (∀h f. ALOOKUP es.ctbl h = SOME f ⇒ k ≠ cl cm f) ⇒
       EL k w'.chans = EL k w.chans)
Proof
  strip_tac >>
  qabbrev_tac ‘l = MAP (λ(h, f). (cl cm f, cstat_of es5 f = CUp)) (settled es es5)’ >>
  ‘settles cm es es5 = MAP (λ(j, b). Settle j b) l’
    by simp[Abbr ‘l’, settles_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  ‘ALL_DISTINCT (MAP FST es.ctbl) ∧ ALL_DISTINCT (MAP SND es.ctbl)’
    by gvs[eown_def, ALL_DISTINCT_APPEND] >>
  ‘∀h f. MEM (h, f) es.ctbl ⇔ ALOOKUP es.ctbl h = SOME f’
    by metis_tac[ALOOKUP_ALL_DISTINCT_MEM, ALOOKUP_MEM] >>
  ‘∀f g. MEM f (MAP SND es.ctbl) ∧ MEM g (MAP SND es.ctbl) ∧ cl cm f = cl cm g ⇒ f = g’
    by metis_tac[ev_rel_cl_ne] >>
  ‘∀j b. MEM (j, b) l ⇔ ∃h f. ALOOKUP es.ctbl h = SOME f ∧ cstat_of es f = CPending ∧
                               cstat_of es5 f ≠ CPending ∧ j = cl cm f ∧
                               (b ⇔ cstat_of es5 f = CUp)’
    by (simp[Abbr ‘l’, MEM_MAP, settled_def, MEM_FILTER, EXISTS_PROD] >> metis_tac[]) >>
  ‘ALL_DISTINCT (MAP FST l)’
    by (simp[Abbr ‘l’, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, settled_def] >>
        irule ALL_DISTINCT_MAP_INJ >> simp[FORALL_PROD, MEM_FILTER] >> conj_tac
        >- (rpt gen_tac >> strip_tac >>
            ‘MEM p_2 (MAP SND es.ctbl) ∧ MEM p_2' (MAP SND es.ctbl)’
              by (imp_res_tac ALOOKUP_SOME_MEM_SND >> simp[]) >>
            ‘p_2 = p_2'’
              by (qpat_x_assum ‘∀f g. MEM f (MAP SND es.ctbl) ∧ _ ⇒ _’ irule >> simp[]) >>
            gvs[] >> imp_res_tac ALOOKUP_MEM >>
            irule (Q.ISPEC ‘es.ctbl’ snd_unique) >> qexistsl_tac [‘es’, ‘p_2’] >> simp[]) >>
        irule FILTER_ALL_DISTINCT >> qpat_x_assum ‘ALL_DISTINCT (MAP FST es.ctbl)’ assume_tac >>
        drule ALL_DISTINCT_MAP >> simp[]) >>
  ‘∀j b. MEM (j, b) l ⇒ j < LENGTH w.chans ∧ (EL j w.chans).status = Connecting’
    by (rw[] >> drule_all ev_rel_ctbl >> simp[cstat_of_def] >> gvs[cstat_of_def]) >>
  drule_all settles_deliver >> simp[] >> strip_tac >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      ‘cl cm f < LENGTH w.chans’ by (drule_all ev_rel_ctbl >> simp[]) >> simp[] >>
      IF_CASES_TAC
      >- (‘MEM (cl cm f, cstat_of es5 f = CUp) l’
            by (qpat_x_assum ‘∀j b. MEM (j, b) l ⇔ _’ (fn th => REWRITE_TAC [th]) >>
                qexistsl_tac [‘h’, ‘f’] >> gvs[]) >>
          ‘ALOOKUP l (cl cm f) = SOME (cstat_of es5 f = CUp)’
            by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >> simp[]) >>
      ‘ALOOKUP l (cl cm f) = NONE’
        by (simp[ALOOKUP_NONE] >> simp[Once MEM_MAP, EXISTS_PROD] >> rpt strip_tac >>
            ‘MEM f (MAP SND es.ctbl) ∧ MEM f' (MAP SND es.ctbl)’
              by (imp_res_tac ALOOKUP_SOME_MEM_SND >> simp[]) >>
            ‘f' = f’ by (qpat_x_assum ‘∀f g. MEM f (MAP SND es.ctbl) ∧ _ ⇒ _’ irule >> simp[]) >>
            fs[]) >>
      simp[]) >>
  rpt strip_tac >>
  ‘ALOOKUP l k = NONE’
    by (simp[ALOOKUP_NONE] >> simp[Once MEM_MAP, EXISTS_PROD] >> rpt strip_tac >>
        qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ k ≠ _’ drule >> simp[]) >>
  simp[]
QED

Theorem ALL_DISTINCT_MAP_FILTER_gen:
  ∀l. ALL_DISTINCT (MAP f l) ⇒ ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem MEM_MAP_FILTER_IMP:
  MEM e (MAP f (FILTER P l)) ⇒ MEM e (MAP f l)
Proof
  rw[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem promote_fields:
  (promote es).p.acq = es.p.acq ∧ (promote es).p.inb = es.p.inb ∧
  (promote es).p.eof = es.p.eof ∧
  (promote es).p.b.tbl = FILTER (λ(h, f). cstat_of es f = CUp) es.ctbl ++ es.p.b.tbl ∧
  (promote es).ctbl = FILTER (λ(h, f). cstat_of es f ≠ CUp) es.ctbl ∧
  (promote es).p.b.nxt = es.p.b.nxt ∧ (promote es).settling = es.settling ∧
  (promote es).p.b.closing = es.p.b.closing
Proof
  simp[promote_def]
QED

(* A connect handle's fd is no other of L1's, and has no input *)
Theorem eown_ctbl_fresh:
  eown lfd es ∧ MEM f (MAP SND es.ctbl) ⇒
  inb_of es.p f = [] ∧ ¬MEM f es.p.eof ∧ ¬MEM f (MAP SND es.p.b.tbl) ∧
  ¬MEM f es.p.acq ∧ ¬MEM f es.p.b.closing ∧ f ≠ lfd
Proof
  simp[eown_def, pown_def, ALL_DISTINCT_APPEND] >> strip_tac >>
  ‘¬MEM f (MAP SND es.p.b.tbl) ∧ ¬MEM f es.p.acq ∧ ¬MEM f es.p.b.closing ∧ f ≠ lfd’
    by metis_tac[] >>
  simp[] >> metis_tac[]
QED

(* Settling and promotion keep the relation, L1's invariant and the
   handle state *)
Theorem ev_settle:
  ev_rel lfd a cm es w ∧ eown lfd es ∧
  es5.p = es.p ∧ es5.ctbl = es.ctbl ∧ es5.settling = es.settling ∧ es5.early = [] ∧
  (∀f. MEM f (MAP SND es.ctbl) ∧ cstat_of es f ≠ CPending ⇒ cstat_of es5 f = cstat_of es f) ⇒
  ev_rel lfd a cm (promote es5) (FOLDL ep_deliver w (settles cm es es5)) ∧
  eown lfd (promote es5) ∧
  (∀hs. ehs_rel hs es ⇒ ehs_rel hs (promote es5))
Proof
  strip_tac >> drule_all settle_world >>
  disch_then (qspec_then ‘es5’ mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac ‘w' = FOLDL ep_deliver w (settles cm es es5)’ >>
  ‘ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl)’ by gvs[eown_def] >>
  ‘ALL_DISTINCT (MAP FST es5.p.b.tbl ++ MAP FST es5.ctbl)’ by gvs[] >>
  rpt conj_tac
  >- (‘∀g. MEM g (MAP FST cm) ⇒ cl cm g < LENGTH w.chans’ by (rpt strip_tac >> drule_all ev_rel_cl_lt >> simp[]) >>
      ‘∀f g. (MEM f (MAP SND es.p.b.tbl) ∨ MEM f (MAP SND es.ctbl) ∨ MEM f es.p.acq) ∧
             (MEM g (MAP SND es.p.b.tbl) ∨ MEM g (MAP SND es.ctbl) ∨ MEM g es.p.acq) ∧ g ≠ f ⇒
             cl cm g ≠ cl cm f’ by (rpt gen_tac >> strip_tac >> irule ev_rel_cl_ne >> simp[] >>
                qexistsl_tac [‘a’, ‘es’, ‘lfd’, ‘w’] >> simp[]) >>
      ‘∀f. MEM f (MAP SND es.ctbl) ⇒ inb_of es.p f = [] ∧ ¬MEM f es.p.eof ∧
           ¬MEM f (MAP SND es.p.b.tbl) ∧ ¬MEM f es.p.acq’
        by (rpt gen_tac >> strip_tac >> drule_all eown_ctbl_fresh >> simp[]) >>
      qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >>
      simp[ev_rel_def, promote_fields, inb_of_def] >> strip_tac >> rpt conj_tac
      >- (‘∀f. MEM f (MAP SND es.ctbl) ⇔
               MEM f (MAP SND (FILTER (λ(h,f). cstat_of es5 f = CUp) es.ctbl)) ∨
               MEM f (MAP SND (FILTER (λ(h,f). cstat_of es5 f ≠ CUp) es.ctbl))’
            by (rpt (pop_assum kall_tac) >> rw[MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
                metis_tac[]) >>
          pop_assum mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[])
      >- (rpt gen_tac >> simp[ALOOKUP_APPEND] >>
          Cases_on ‘ALOOKUP (FILTER (λ(h,f). cstat_of es5 f = CUp) es.ctbl) h’ >> simp[] >>
          strip_tac
          >- ((* a prefetching handle: its channel is no connect channel *)
              qpat_x_assum ‘∀h f. ALOOKUP es.p.b.tbl h = SOME f ⇒ _’ drule >> strip_tac >>
              ‘MEM f (MAP SND es.p.b.tbl)’ by (imp_res_tac ALOOKUP_SOME_MEM_SND >> simp[]) >>
              ‘cl cm f < LENGTH w.chans’
                by (qpat_x_assum ‘∀g. MEM g (MAP FST cm) ⇒ _’ irule >> simp[]) >>
              ‘∀h' g. ALOOKUP es.ctbl h' = SOME g ⇒ cl cm f ≠ cl cm g’
                by (rpt strip_tac >> imp_res_tac ALOOKUP_SOME_MEM_SND >>
                    ‘g ≠ f’
                      by (strip_tac >>
                          qpat_x_assum ‘∀f. MEM f (MAP SND es.ctbl) ⇒ inb_of _ _ = [] ∧ _’
                            (qspec_then ‘g’ mp_tac) >> simp[] >> fs[]) >>
                    qpat_x_assum ‘∀f g. _ ∧ _ ∧ g ≠ f ⇒ cl cm g ≠ cl cm f’
                      (qspecl_then [‘f’, ‘g’] mp_tac) >> simp[]) >>
              qpat_x_assum ‘∀k. k < LENGTH w.chans ∧ _ ⇒ _’ (qspec_then ‘cl cm f’ mp_tac) >>
              impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
          (* an up connect handle: its channel settled up *)
          rename1 ‘ALOOKUP (FILTER _ _) h = SOME g’ >> strip_tac >> pop_assum SUBST_ALL_TAC >>
          ‘ALOOKUP es.ctbl h = SOME f ∧ cstat_of es5 f = CUp’
            by (qpat_x_assum ‘ALOOKUP (FILTER _ _) _ = _’ assume_tac >>
                drule_at (Pos last) ALOOKUP_FILTER_IMP >> impl_tac
                >- fs[ALL_DISTINCT_APPEND] >> simp[]) >>
          ‘MEM f (MAP SND es.ctbl)’ by (imp_res_tac ALOOKUP_SOME_MEM_SND >> simp[]) >>
          ‘cstat_of es f = CPending’
            by (spose_not_then assume_tac >>
                qpat_x_assum ‘∀f. MEM f (MAP SND es.ctbl) ∧ _ ⇒ cstat_of es5 f = _’
                  (qspec_then ‘f’ mp_tac) >> simp[] >>
                qpat_x_assum ‘eown _ _’ mp_tac >> simp[eown_def] >> strip_tac >>
                first_x_assum drule >> simp[]) >>
          qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ MEM f _ ∧ _’ drule >> strip_tac >>
          qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ w'.chans❲_❳ = _’ drule >>
          strip_tac >> qpat_x_assum ‘∀f. MEM f (MAP SND es.ctbl) ⇒ inb_of _ _ = [] ∧ _’
            (qspec_then ‘f’ mp_tac) >> simp[inb_of_def])
      >- (rpt gen_tac >> strip_tac >>
          ‘ALOOKUP es.ctbl h = SOME f ∧ cstat_of es5 f ≠ CUp’
            by (qpat_x_assum ‘ALOOKUP (FILTER _ _) _ = _’ assume_tac >>
                drule_at (Pos last) ALOOKUP_FILTER_IMP >> impl_tac
                >- fs[ALL_DISTINCT_APPEND] >> simp[]) >>
          ‘MEM f (MAP SND es.ctbl)’ by (imp_res_tac ALOOKUP_SOME_MEM_SND >> simp[]) >>
          ‘cstat_of (promote es5) f = cstat_of es5 f’ by (irule cstat_of_promote >> simp[]) >>
          qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ MEM f _ ∧ _’ drule >> strip_tac >>
          qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ w'.chans❲_❳ = _’ drule >>
          strip_tac >>
          qpat_x_assum ‘∀f. MEM f (MAP SND es.ctbl) ∧ _ ⇒ cstat_of es5 f = _’
            (qspec_then ‘f’ mp_tac) >>
          simp[] >> Cases_on ‘cstat_of es f’ >> Cases_on ‘cstat_of es5 f’ >> gvs[]) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘∀f. MEM f es.p.acq ⇒ _’ drule >> strip_tac >>
      ‘cl cm f < LENGTH w.chans’
        by (qpat_x_assum ‘∀g. MEM g (MAP FST cm) ⇒ _’ irule >> simp[]) >>
      ‘∀h' g. ALOOKUP es.ctbl h' = SOME g ⇒ cl cm f ≠ cl cm g’
        by (rpt strip_tac >> imp_res_tac ALOOKUP_SOME_MEM_SND >>
            ‘g ≠ f’
              by (strip_tac >>
                  qpat_x_assum ‘∀f. MEM f (MAP SND es.ctbl) ⇒ inb_of _ _ = [] ∧ _’
                    (qspec_then ‘g’ mp_tac) >> simp[] >> fs[]) >>
            qpat_x_assum ‘∀f g. _ ∧ _ ∧ g ≠ f ⇒ cl cm g ≠ cl cm f’
              (qspecl_then [‘f’, ‘g’] mp_tac) >> simp[]) >>
      qpat_x_assum ‘∀k. k < LENGTH w.chans ∧ _ ⇒ _’ (qspec_then ‘cl cm f’ mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[])
  >- (qpat_x_assum ‘eown _ _’ mp_tac >>
      simp[eown_def, pown_def, promote_def, inb_of_def] >> strip_tac >>
      gvs[ALL_DISTINCT_APPEND, MEM_FILTER] >> rpt conj_tac >>
      TRY (irule ALL_DISTINCT_MAP_FILTER_gen >> simp[] >> NO_TAC) >>
      TRY (strip_tac >> imp_res_tac MEM_MAP_FILTER_IMP >> gvs[] >> NO_TAC) >>
      rpt strip_tac >> imp_res_tac MEM_MAP_FILTER_IMP >> gvs[] >>
      TRY (qpat_x_assum ‘ALOOKUP (_ ++ _) _ = _’ mp_tac >> simp[ALOOKUP_APPEND] >>
           CASE_TAC >> strip_tac >> gvs[]
           >- (first_x_assum drule >> simp[]) >>
           imp_res_tac ALOOKUP_FILTER_IMP >> gvs[] >>
           qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ (∃i. _) ∧ _’ drule >> simp[] >> NO_TAC) >>
      TRY (imp_res_tac ALOOKUP_FILTER_IMP >> gvs[] >>
           qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ (∃i. _) ∧ _’ drule >> simp[] >> NO_TAC) >>
      TRY (gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> NO_TAC) >>
      TRY (gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
           ‘ALOOKUP es.ctbl e = SOME p_2 ∧ ALOOKUP es.ctbl e = SOME p_2'’
             by (conj_tac >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >> gvs[] >> NO_TAC) >>
      imp_res_tac ALOOKUP_FILTER_IMP >> gvs[cstat_of_def] >>
      TRY (qpat_x_assum ‘ALOOKUP (_ ++ _) _ = _’
             (strip_assume_tac o SIMP_RULE (srw_ss()) [ALOOKUP_APPEND, AllCaseEqs()]) >>
           imp_res_tac ALOOKUP_FILTER_IMP >> res_tac >> fs[] >> NO_TAC) >>
      Cases_on ‘ALOOKUP es5.cst f’ >> gvs[ALOOKUP_FILTER_NONE] >>
      ‘ALOOKUP (FILTER (λ(f, c). c ≠ CUp) es5.cst) f = SOME x’
        by (irule ALOOKUP_FILTER_SOME >> fs[]) >> gvs[])
  >> rw[ehs_rel_def] >> TRY (simp[promote_def] >> NO_TAC) >>
  qpat_x_assum ‘ALL_DISTINCT (MAP FST es5.p.b.tbl ++ _)’ (assume_tac o MATCH_MP promote_lookup) >>
  gvs[]
QED

Theorem ALOOKUP_FOLDR_early:
  ∀l c0. ALOOKUP (FOLDR (λ(f, c) l. (f, c) :: ADELKEY f l) c0 l) k =
         case ALOOKUP l k of SOME c => SOME c | NONE => ALOOKUP c0 k
Proof
  Induct >> simp[FORALL_PROD] >> rw[ALOOKUP_ADELKEY]
QED

(* The connects known at once: their outcome taken *)
Theorem cstat_of_apply_early:
  cstat_of (apply_early es) f =
    case ALOOKUP es.early f of SOME c => c | NONE => cstat_of es f
Proof
  simp[apply_early_def, cstat_of_def, ALOOKUP_FOLDR_early] >> CASE_TAC >> simp[]
QED

Theorem apply_early_fields[simp]:
  (apply_early es).p = es.p ∧ (apply_early es).ctbl = es.ctbl ∧
  (apply_early es).settling = es.settling ∧ (apply_early es).early = []
Proof
  simp[apply_early_def]
QED

(* Settling the ready pending connects: only their status changes (up,
   refused, or still pending); L0's fds unchanged *)
Theorem settle_fds_props:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ∧ l0_rely w ⇒
    l0_rely w' ∧ l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧
    es'.p = es.p ∧ es'.ctbl = es.ctbl ∧ es'.settling = es.settling ∧ es'.early = es.early ∧
    ∀f. cstat_of es' f = cstat_of es f ∨ (MEM f fs ∧ (cstat_of es' f = CUp ∨ cstat_of es' f = CRefused))
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘sys_connerr h w = SOME (out, w1, ev)’ >>
  drule_all sys_connerr_l0 >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘settle_fds fs (w1, es1)’ >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  ‘es1.p = es.p ∧ es1.ctbl = es.ctbl ∧ es1.settling = es.settling ∧ es1.early = es.early ∧
   ∀f. cstat_of es1 f = cstat_of es f ∨ (f = h ∧ (cstat_of es1 f = CUp ∨ cstat_of es1 f = CRefused))’
    by (simp[Abbr ‘es1’] >> every_case_tac >> rw[cstat_of_def, ALOOKUP_ADELKEY]) >>
  simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The round's tail
   ------------------------------------------------------------------------ *)

Theorem ev_rel_pb:
  ps'.inb = ps.inb ∧ ps'.eof = ps.eof ∧ ps'.acq = ps.acq ∧ ps'.b.tbl = ps.b.tbl ⇒
  (ev_rel lfd a cm (es with p := ps') w ⇔ ev_rel lfd a cm (es with p := ps) w)
Proof
  simp[ev_rel_def, inb_of_def, cstat_of_def]
QED

Theorem ev_rel_clock[simp]:
  ev_rel lfd a cm es (w with clock := c) ⇔ ev_rel lfd a cm es w
Proof
  simp[ev_rel_def]
QED

Theorem in_fds_pend:
  MEM f (in_fds (fes ++ MAP (λf. (f, 2n)) fs)) ⇔ MEM f (in_fds fes)
Proof
  simp[in_fds_def, FILTER_APPEND, MAP_MAP_o, combinTheory.o_DEF] >>
  ‘FILTER (λ(f, e). ODD e) (MAP (λf. (f, 2n)) fs) = []’
    by (simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP] >> rw[] >> simp[]) >>
  simp[]
QED

(* The tail up to the settling: the poll, the flush, the fetch (its
   arrivals delivered) and the reap *)
Theorem ev_pre_settle:
  l1_polls fess wl = SOME (rv, w1, pevs) ∧
  l1_flush fls (w1, es.p.b) = SOME ((w2, b2), fevs) ∧
  pf_fetch lfd hw fs (w2, es.p with b := b2) = SOME ((w3, ps3), log, gevs) ∧
  l1_reap ps3.b.closing (w3, ps3.b) = SOME ((w4, b4), cevs) ∧
  (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND es.p.b.tbl)) ∧
  ev_rel lfd a cm es w ∧ eown lfd es ∧ l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ∧
  arrs lfd (cm, LENGTH w.chans) log = (as, (cm', k')) ∧
  (∀f j. MEM (f, j) cm' ∧ LENGTH w.chans ≤ j ⇒ ∀used. ¬MEM f used ⇒ w.alloc j used = f) ∧
  k' + 1 < dimword (:64) ⇒
  ev_rel lfd a cm' (es with p := ps3 with <| b := b4; pause := ps3.pause − 1 |>)
    (FOLDL ep_deliver w (MAP (conv a) as)) ∧
  eown lfd (es with p := ps3 with <| b := b4; pause := ps3.pause − 1 |>) ∧
  l0owne lfd w4 (es with p := ps3 with <| b := b4; pause := ps3.pause − 1 |>) ∧
  l0_rely w4 ∧ fds_lt w4 ∧
  ep_grows w (FOLDL ep_deliver w (MAP (conv a) as)) ∧
  k' = LENGTH (FOLDL ep_deliver w (MAP (conv a) as)).chans ∧ b4.nxt = es.p.b.nxt ∧
  b4.tbl = es.p.b.tbl ∧
  ∃new. cm' = new ++ cm ∧ ∀f. MEM f (MAP FST new) ⇒ ¬MEM f (MAP SND es.ctbl)
Proof
  strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >>
  drule_all l1_flush_l0 >> strip_tac >>
  qabbrev_tac ‘es2 = es with p := es.p with b := b2’ >>
  ‘ev_rel lfd a cm es2 w’
    by (simp[Abbr ‘es2’] >> ‘es = es with p := es.p’ by simp[l1e_component_equality] >>
        pop_assum (fn th => ONCE_REWRITE_TAC [th]) >> simp[ev_rel_b]) >>
  ‘eown lfd es2’ by (simp[Abbr ‘es2’] >> irule eown_p >> simp[pown_b] >> gvs[eown_def]) >>
  ‘l0owne lfd w2 es2’
    by (qpat_x_assum ‘l0owne _ _ _’ mp_tac >> simp[Abbr ‘es2’, l0owne_def, l0own_def] >>
        disch_then (MATCH_ACCEPT_TAC o CONJUNCT1)) >>
  ‘l0_rely w2 ∧ fds_lt w2’ by gvs[fds_lt_def] >>
  ‘pf_fetch lfd hw fs (w2, es2.p) = SOME ((w3, ps3), log, gevs)’ by simp[Abbr ‘es2’] >>
  ‘∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND es2.p.b.tbl)’ by simp[Abbr ‘es2’] >>
  drule_all ev_fetch >> strip_tac >>
  ‘es2 with p := ps3 = es with p := ps3’ by simp[Abbr ‘es2’] >>
  qpat_x_assum ‘es2 with p := ps3 = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  ‘ps3.b.tbl = es.p.b.tbl ∧ ps3.b.nxt = es.p.b.nxt ∧ ps3.b.closing = es.p.b.closing’
    by gvs[Abbr ‘es2’] >>
  drule_all l1_reap_l0 >> strip_tac >>
  qabbrev_tac ‘ps4 = ps3 with <| b := b4; pause := ps3.pause − 1 |>’ >>
  ‘pown lfd ps4’
    by (simp[Abbr ‘ps4’] >>
        ‘ps3 with <| b := b4; pause := ps3.pause − 1 |> =
         (ps3 with b := b4) with pause := ps3.pause − 1’ by simp[] >>
        pop_assum SUBST1_TAC >> simp[rel_pause] >>
        irule pown_closing_filter >> simp[] >> gvs[eown_def] >> metis_tac[]) >>
  ‘∀g. g = lfd ∨ MEM g (MAP SND ps3.b.tbl) ∨ MEM g ps3.acq ∨ MEM g (MAP SND es.ctbl) ⇒
       ¬MEM g ps3.b.closing’
    by (qpat_x_assum ‘eown _ (es with p := ps3)’ mp_tac >>
        simp[eown_def, pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  rpt conj_tac
  >- (‘es with p := ps4 = (es with p := ps3) with p := ps4’ by simp[] >>
      pop_assum SUBST1_TAC >> simp[Abbr ‘ps4’] >>
      qmatch_goalsub_abbrev_tac ‘ev_rel _ _ _ (es3 with p := _) _’ >>
      ‘ev_rel lfd a cm' (es3 with p := ps3) (FOLDL ep_deliver w (MAP (conv a) as))’
        by simp[Abbr ‘es3’] >>
      drule_at (Pos last) (iffRL ev_rel_pb) >> disch_then irule >> simp[]) >>
  TRY (‘es with p := ps4 = (es with p := ps3) with p := ps4’ by simp[] >>
       pop_assum SUBST1_TAC >> irule eown_p >> simp[Abbr ‘ps4’] >>
       rpt strip_tac >> gvs[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘l0owne _ w3 _’ mp_tac >>
       simp[l0owne_def, l0own_def, Abbr ‘ps4’] >> rpt strip_tac >> gvs[] >>
       TRY (qpat_x_assum ‘∀g. MEM g (l0_used w3) ∧ ¬MEM g ps3.b.closing ⇒ _’ irule >>
            simp[] >> NO_TAC) >>
       qpat_x_assum ‘∀g. MEM g b4.closing ⇒ _’ drule >> simp[] >> NO_TAC) >>
  TRY (gvs[fds_lt_def] >> rpt strip_tac >> res_tac >> gvs[] >> NO_TAC) >>
  TRY (simp[] >> NO_TAC) >>
  drule arrs_new >> strip_tac >> qexists_tac ‘new’ >> simp[] >>
  qpat_x_assum ‘pf_fetch _ _ _ (w2, es2.p) = _’ assume_tac >>
  drule_all fetch_acq >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  ‘MEM f (l0_used wl)’
    by (qpat_x_assum ‘l0owne _ wl _’ mp_tac >> simp[l0owne_def] >> strip_tac >>
        first_x_assum irule >> simp[]) >>
  qpat_x_assum ‘∀f'. MEM f' (fconns log) ⇒ _’ drule >> simp[]
QED

(* The poll's answer: L1's ready handles are the layer's, and its settled
   handles the layer's *)
Theorem ev_rdy:
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ⇒
  (∀h. (case ALOOKUP hs.tbl h of
        | SOME f => MEM h hs.settling ∧ chan_status w f ≠ SOME Connecting
        | NONE => F) ⇔
       MEM h es.settling ∧
       (case ALOOKUP es.ctbl h of
        | SOME f => cstat_of es f ≠ CPending
        | NONE => ALOOKUP es.p.b.tbl h ≠ NONE)) ∧
  ∀h. (case ALOOKUP es.ctbl h of
       | SOME f => cstat_of es f = CRefused ∨
                   (MEM h es.settling ∧ cstat_of es f ≠ CPending)
       | NONE => MEM h (pf_ready lfd es.p [h]) ∨
                 (MEM h es.settling ∧ ALOOKUP es.p.b.tbl h ≠ NONE)) ⇔
      (case ALOOKUP hs.tbl h of
       | SOME f => ep_readable w f ∨
                   (MEM h hs.settling ∧ chan_status w f ≠ SOME Connecting)
       | NONE => if h = lfd then ep_readable w h else T)
Proof
  strip_tac >>
  ‘lfd ∉ set (MAP FST w.open_fds)’
    by (strip_tac >> gvs[ev_rel_def, eown_def]) >>
  ‘w.listening = [(lfd, a, MAP (cl cm) es.p.acq)]’ by gvs[ev_rel_def] >>
  ‘∀h. ALOOKUP hs.tbl h =
       case ALOOKUP es.p.b.tbl h of SOME f => SOME f | NONE => ALOOKUP es.ctbl h’
    by gvs[ehs_rel_def] >>
  ‘∀h. MEM h hs.settling ⇔ MEM h es.settling ∧ ALOOKUP hs.tbl h ≠ NONE’
    by gvs[ehs_rel_def] >>
  ‘∀h f. ALOOKUP es.p.b.tbl h = SOME f ⇒ ALOOKUP es.ctbl h = NONE’
    by (rpt strip_tac >> gvs[eown_def, ALL_DISTINCT_APPEND, ALOOKUP_NONE] >>
        metis_tac[ALOOKUP_SOME_MEM_FST]) >>
  ‘∀h f. ALOOKUP es.p.b.tbl h = SOME f ⇒
         chan_status w f = SOME Up ∧ (ep_readable w f ⇔ inb_of es.p f ≠ [] ∨ MEM f es.p.eof)’
    by (rpt gen_tac >> strip_tac >> drule_all ev_rel_tbl >> strip_tac >>
        ‘f ≠ lfd’ by (strip_tac >> gvs[eown_def] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >>
        simp[chan_status_def, ep_readable_def]) >>
  ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒
         chan_status w f = SOME (if cstat_of es f = CRefused then Refused else Connecting) ∧
         (ep_readable w f ⇔ cstat_of es f = CRefused) ∧ cstat_of es f ≠ CUp’
    by (rpt gen_tac >> strip_tac >> drule_all ev_rel_ctbl >> strip_tac >>
        ‘f ≠ lfd ∧ cstat_of es f ≠ CUp’
          by (gvs[eown_def, ALL_DISTINCT_APPEND] >> res_tac >> simp[] >>
              strip_tac >> gvs[] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >>
        simp[chan_status_def, ep_readable_def] >> rw[]) >>
  ‘ep_readable w lfd ⇔ es.p.acq ≠ []’
    by (simp[ep_readable_def, ep_chan_of_def] >>
        ‘ALOOKUP w.open_fds lfd = NONE’ by gvs[ALOOKUP_NONE] >> simp[]) >>
  ‘∀h. MEM h (pf_ready lfd es.p [h]) ⇔
       case ALOOKUP es.p.b.tbl h of
       | SOME f => inb_of es.p f ≠ [] ∨ MEM f es.p.eof
       | NONE => if h = lfd then es.p.acq ≠ [] else T’
    by (simp[pf_ready_def] >> rw[] >> CASE_TAC >> simp[]) >>
  conj_tac >> gen_tac >>
  Cases_on ‘ALOOKUP es.p.b.tbl h’ >> Cases_on ‘ALOOKUP es.ctbl h’ >> simp[] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  TRY (Cases_on ‘h = lfd’ >> simp[] >> NO_TAC) >>
  rename1 ‘ALOOKUP es.ctbl h = SOME g’ >>
  qpat_x_assum ‘∀h f. ALOOKUP es.ctbl h = SOME f ⇒ chan_status _ _ = _ ∧ _’ drule >>
  strip_tac >> simp[] >> Cases_on ‘cstat_of es g’ >> gvs[]
QED

Theorem ep_deliver_clock:
  ∀l w. FOLDL ep_deliver (w with clock := c) l = (FOLDL ep_deliver w l) with clock := c
Proof
  Induct >> simp[] >> rpt gen_tac >>
  ‘ep_deliver (w with clock := c) h = (ep_deliver w h) with clock := c’
    by (Cases_on ‘h’ >> rw[ep_deliver_def, upd_chan_def] >> every_case_tac >> simp[] >>
        pairarg_tac >> simp[]) >>
  simp[]
QED

Theorem settling_simps[simp]:
  (ev_rel lfd a cm (es with settling := s) w ⇔ ev_rel lfd a cm es w) ∧
  (ehs_rel hs (es with settling := s) ⇔
     hs.nxt = es.p.b.nxt ∧
     (∀h. ALOOKUP hs.tbl h =
          case ALOOKUP es.p.b.tbl h of SOME f => SOME f | NONE => ALOOKUP es.ctbl h) ∧
     ∀h. MEM h hs.settling ⇔ MEM h s ∧ ALOOKUP hs.tbl h ≠ NONE)
Proof
  simp[ev_rel_def, ehs_rel_def, inb_of_def, cstat_of_def]
QED

Theorem eown_settling_sub:
  eown lfd es ∧ (∀h. MEM h s ⇒ MEM h es.settling) ⇒ eown lfd (es with settling := s)
Proof
  simp[eown_def, cstat_of_def] >> metis_tac[]
QED

(* The settle arrivals of a round: the connects that settled in its tail
   (state es before, es' after) *)
Definition rsettles_def:
  rsettles cm es es' =
    MAP (λ(h, f). Settle (cl cm f) (ALOOKUP es'.ctbl h = NONE))
      (FILTER (λ(h, f). cstat_of es f = CPending ∧
                        (ALOOKUP es'.ctbl h = NONE ∨ cstat_of es' f = CRefused)) es.ctbl)
End

Theorem MAP_FILTER_cong:
  ∀l. (∀x. MEM x l ⇒ (p1 x ⇔ p2 x) ∧ (p2 x ⇒ g1 x = g2 x)) ⇒
      MAP g1 (FILTER p1 l) = MAP g2 (FILTER p2 l)
Proof
  Induct >> rw[] >> gvs[]
QED

Theorem rsettles_settles:
  eown lfd es ∧ es4.ctbl = es.ctbl ∧ es4.cst = es.cst ∧ es5.ctbl = es.ctbl ∧
  (∀f. MEM f (MAP FST new) ⇒ ¬MEM f (MAP SND es.ctbl)) ⇒
  rsettles cm es (promote es5 with settling := s) = settles (new ++ cm) es4 es5
Proof
  strip_tac >> simp[rsettles_def, settles_def, settled_def, promote_fields] >>
  irule MAP_FILTER_cong >> simp[FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  ‘ALL_DISTINCT (MAP FST es.ctbl)’ by gvs[eown_def, ALL_DISTINCT_APPEND] >>
  ‘ALOOKUP es.ctbl p_1 = SOME p_2’ by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
  ‘MEM p_2 (MAP SND es.ctbl)’ by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘cstat_of es4 p_2 = cstat_of es p_2’ by simp[cstat_of_def] >>
  ‘cl (new ++ cm) p_2 = cl cm p_2’ by (simp[cl_append] >> metis_tac[]) >>
  ‘cstat_of (promote es5 with settling := s) p_2 = cstat_of (promote es5) p_2’
    by simp[cstat_of_def] >>
  Cases_on ‘cstat_of es5 p_2 = CUp’
  >- (‘ALOOKUP (FILTER (λ(h, f). cstat_of es5 f ≠ CUp) es.ctbl) p_1 = NONE’
        by (Cases_on ‘ALOOKUP (FILTER (λ(h, f). cstat_of es5 f ≠ CUp) es.ctbl) p_1’ >>
            simp[] >> imp_res_tac ALOOKUP_FILTER_IMP >> gvs[]) >>
      simp[]) >>
  ‘ALOOKUP (FILTER (λ(h, f). cstat_of es5 f ≠ CUp) es.ctbl) p_1 = SOME p_2’
    by (irule ALOOKUP_FILTER_SOME >> simp[]) >>
  drule cstat_of_promote >> simp[] >> strip_tac >>
  Cases_on ‘cstat_of es5 p_2’ >> gvs[]
QED

Theorem l0owne_promote:
  l0owne lfd w es4 ∧ es5.p = es4.p ∧ es5.ctbl = es4.ctbl ∧
  (∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w')) ⇒
  l0owne lfd w' (promote es5 with settling := sl)
Proof
  simp[l0owne_def, l0own_def, promote_fields] >> strip_tac >>
  ‘∀f. f = lfd ∨ MEM f (MAP SND es4.p.b.tbl) ∨ MEM f es4.p.b.closing ∨ MEM f es4.p.acq ∨
       MEM f (MAP SND es4.ctbl) ⇒ MEM f (l0_used w')’
    by (rpt strip_tac >> qpat_x_assum ‘∀g. MEM g (l0_used w) ⇒ _’ irule >> fs[]) >>
  rpt strip_tac >> imp_res_tac MEM_MAP_FILTER_IMP >> gvs[]
QED

(* The round's tail is the layer's poll: time passes in the world, whose
   arrivals are what L1 fetched and the connects that settled *)
Theorem ev_tail:
  etail lfd hw ifs (wl, es) = SOME (rdy, (wl', es'), log, tevs) ∧
  ev_rel lfd a cm es w ∧ eown lfd es ∧ ehs_rel hs es ∧
  l0owne lfd wl es ∧ l0_rely wl ∧ fds_lt wl ∧
  arrs lfd (cm, LENGTH w.chans) log = (as, (cm', k')) ∧
  (∀f j. MEM (f, j) cm' ∧ LENGTH w.chans ≤ j ⇒ ∀used. ¬MEM f used ⇒ w.alloc j used = f) ∧
  k' + 1 < dimword (:64) ∧
  w.env w.clock w.hist = MAP (conv a) as ++ rsettles cm es es' ⇒
  ∃w' hs'. ehpoll lfd hs ifs w = (rdy, w', hs') ∧
    ev_rel lfd a cm' es' w' ∧ eown lfd es' ∧ ehs_rel hs' es' ∧
    l0owne lfd wl' es' ∧ l0_rely wl' ∧ fds_lt wl' ∧
    LENGTH w'.chans = k' ∧ w'.alloc = w.alloc ∧ w'.env = w.env ∧
    w'.clock = w.clock + 1 ∧ w'.hist = w.hist ∧ es'.p.b.nxt = es.p.b.nxt
Proof
  simp[etail_def] >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw es.p ifs ++ MAP (λf. (f, 2n)) (pend_fds es)’ >>
  gvs[AllCaseEqs()] >>
  rename1 ‘l1_polls _ wl = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  rename1 ‘settle_fds _ _ = SOME ((w5, es5), sevs)’ >>
  ‘∀f. MEM f (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv)) ⇒
       f = lfd ∨ MEM f (MAP SND es.p.b.tbl)’
    by (rw[MEM_FILTER, Abbr ‘fes’, in_fds_pend] >> drule in_fds_poll_set >> simp[]) >>
  ‘k' + 1 < dimword (:64)’ by fs[] >>
  drule_all ev_pre_settle >> strip_tac >>
  qabbrev_tac ‘es4 = es with p := ps3 with <|b := b4; pause := ps3.pause − 1|>’ >>
  qabbrev_tac ‘wF = FOLDL ep_deliver w (MAP (conv a) as)’ >>
  drule_all settle_fds_props >> simp[] >> strip_tac >>
  ‘∀f. MEM f (MAP SND es4.ctbl) ∧ cstat_of es4 f ≠ CPending ⇒ cstat_of es5 f = cstat_of es4 f’
    by (rpt strip_tac >>
        ‘cstat_of es4 f = cstat_of es f’ by simp[Abbr ‘es4’, cstat_of_def] >>
        ‘¬MEM f (pend_fds es)’
          by (simp[pend_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[]) >>
        ‘ALOOKUP es4.early f = NONE’
          by (simp[ALOOKUP_NONE] >> strip_tac >> gvs[eown_def] >>
              first_x_assum drule >> simp[]) >>
        qpat_x_assum ‘∀f. cstat_of es5 f = _ ∨ _’ (qspec_then ‘f’ strip_assume_tac) >>
        gvs[MEM_FILTER, cstat_of_apply_early]) >>
  ‘es4.p.b.tbl = es.p.b.tbl ∧ es4.p.b.nxt = es.p.b.nxt ∧ es4.ctbl = es.ctbl ∧
   es4.settling = es.settling ∧ es4.cst = es.cst ∧ es4.early = es.early’
    by simp[Abbr ‘es4’] >>
  ‘ehs_rel hs es4’ by (qpat_x_assum ‘ehs_rel hs es’ mp_tac >> simp[ehs_rel_def] >> fs[]) >>
  drule_all ev_settle >> strip_tac >>
  ‘∀sl. rsettles cm es (promote es5 with settling := sl) = settles (new ++ cm) es4 es5’
    by (gen_tac >> irule rsettles_settles >> simp[] >> qexists_tac ‘lfd’ >> simp[]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum ‘w.env _ _ = _’
    (fn th => simp[ehpoll_def, ep_tick_def, th, FOLDL_APPEND, ep_deliver_clock]) >>
  qabbrev_tac ‘wS = FOLDL ep_deliver wF (settles (new ++ cm) es4 es5)’ >>
  ‘ehs_rel hs (promote es5)’
    by (qpat_x_assum ‘∀hs. ehs_rel hs es4 ⇒ _’ irule >> simp[]) >>
  ‘ev_rel lfd a (new ++ cm) (promote es5) (wS with clock := w.clock + 1)’
    by gvs[Abbr ‘wS’] >>
  qpat_x_assum ‘eown lfd (promote es5)’ assume_tac >>
  drule_all ev_rdy >> strip_tac >>
  conj_tac
  >- (irule filter_cong >> rpt strip_tac >>
      qpat_x_assum ‘∀h. (case ALOOKUP (promote es5).ctbl h of NONE => _ | SOME f => _) ⇔ _’
        (qspec_then ‘x’ mp_tac) >>
      qpat_x_assum ‘∀h. (case ALOOKUP hs.tbl h of NONE => _ | SOME f => _) ⇔ _’
        (qspec_then ‘x’ mp_tac) >>
      rpt (pop_assum kall_tac) >> every_case_tac >> simp[] >> metis_tac[]) >>
  qpat_x_assum ‘ev_rel lfd a cm' es4 wF’ assume_tac >>
  qpat_x_assum ‘eown lfd es4’ assume_tac >>
  drule_all settle_world >> simp[] >> disch_then (qspec_then ‘es5’ strip_assume_tac) >>
  ‘wF.alloc = w.alloc ∧ wF.env = w.env ∧ wF.hist = w.hist’
    by (qpat_x_assum ‘ep_grows w wF’ mp_tac >> simp[ep_grows_def]) >>
  rpt conj_tac
  >- (qpat_x_assum ‘ev_rel _ _ _ (promote es5) (wS with clock := _)’ mp_tac >> simp[])
  >- (irule eown_settling_sub >> fs[MEM_FILTER])
  >- (qpat_x_assum ‘ehs_rel hs es’ mp_tac >> simp[ehs_rel_def, promote_fields] >> fs[])
  >- (gen_tac >>
      qpat_x_assum ‘ehs_rel hs (promote es5)’ (strip_assume_tac o REWRITE_RULE [ehs_rel_def]) >>
      qpat_x_assum ‘∀h. ALOOKUP hs.tbl h = _’ (qspec_then ‘h’ mp_tac) >>
      rpt (pop_assum kall_tac) >> CASE_TAC >> simp[])
  >- (gen_tac >> simp[MEM_FILTER] >>
      qpat_x_assum ‘ehs_rel hs (promote es5)’ (strip_assume_tac o REWRITE_RULE [ehs_rel_def]) >>
      qpat_x_assum ‘∀h. (case ALOOKUP hs.tbl h of NONE => F | SOME f => _) ⇔ _’
        (qspec_then ‘h’ mp_tac) >>
      qpat_x_assum ‘∀h. MEM h hs.settling ⇔ _’ (qspec_then ‘h’ mp_tac) >>
      qpat_x_assum ‘∀h. ALOOKUP hs.tbl h = _’ (qspec_then ‘h’ mp_tac) >>
      rpt (pop_assum kall_tac) >> every_case_tac >> simp[] >> metis_tac[])
  >- (qpat_x_assum ‘l0owne _ w4 _’ assume_tac >>
      drule_at (Pos hd) l0owne_promote >> disch_then irule >> fs[])
  >> rpt conj_tac >> fs[fds_lt_def, promote_fields, Abbr ‘wS’]
QED

(* ------------------------------------------------------------------------
   The endpoint world built from L1's run (R1-safe: a function of the run,
   fixed before the layer runs)
   ------------------------------------------------------------------------ *)

(* Round n's actions, from the state before it *)
Definition eacts_of_def:
  eacts_of lfd hw ifds m w0 n =
    case erounds lfd hw ifds m (w0, einit) n of
    | SOME (h, ws, evs, logs) => eacts lfd hw ws (new_actions (log_of m) h)
    | NONE => NONE
End

(* Round n's connects' fds, in order *)
Definition econ_def:
  econ lfd hw ifds m w0 n =
    case eacts_of lfd hw ifds m w0 n of
    | SOME (rs, evs, ws1) => rfds (SND ws1) rs
    | NONE => []
End

(* What round n fetched *)
Definition elog_def:
  elog lfd hw ifds m w0 n =
    case erounds lfd hw ifds m (w0, einit) (SUC n) of
    | SOME (_, _, _, logs) => EL n logs
    | NONE => []
End

(* The channel map and count before round n *)
Definition ecm_def:
  ecm lfd hw ifds m w0 0 = ([], 0) ∧
  ecm lfd hw ifds m w0 (SUC n) =
    let (cm, k) = ecm lfd hw ifds m w0 n;
        fs = econ lfd hw ifds m w0 n in
      SND (arrs lfd (cnew k fs ++ cm, k + LENGTH fs) (elog lfd hw ifds m w0 n))
End

(* ... and after round n's connects *)
Definition ecm1_def:
  ecm1 lfd hw ifds m w0 n =
    let (cm, k) = ecm lfd hw ifds m w0 n;
        fs = econ lfd hw ifds m w0 n in
      (cnew k fs ++ cm, k + LENGTH fs)
End

Theorem ecm_SUC:
  ecm lfd hw ifds m w0 (SUC n) =
    SND (arrs lfd (ecm1 lfd hw ifds m w0 n) (elog lfd hw ifds m w0 n))
Proof
  simp[ecm_def, ecm1_def] >> pairarg_tac >> simp[]
QED

(* The connects that settled in round n's tail *)
Definition esett_def:
  esett lfd hw ifds m w0 n =
    case (eacts_of lfd hw ifds m w0 n, erounds lfd hw ifds m (w0, einit) (SUC n)) of
    | (SOME (rs, evs, ws1), SOME (h', ws', evs', logs)) =>
        rsettles (FST (ecm1 lfd hw ifds m w0 n)) (SND ws1) (SND ws')
    | _ => []
End

(* The arrivals of tick n: what round n fetched (accepted connections to
   the listener's address a), then the connects that settled *)
Definition earr_def:
  earr lfd a hw ifds m w0 n =
    MAP (conv a) (FST (arrs lfd (ecm1 lfd hw ifds m w0 n) (elog lfd hw ifds m w0 n))) ++
    esett lfd hw ifds m w0 n
End

(* The fd of channel j: the one L1 got (by accept or connect) *)
Definition erun_alloc_def:
  erun_alloc lfd hw ifds m w0 (j : num) (used : word64 list) =
    if ∃n f. MEM (f, j) (FST (ecm lfd hw ifds m w0 n)) then
      let f = @f. ∃n. MEM (f, j) (FST (ecm lfd hw ifds m w0 n)) in
        if MEM f used then lowest_free used else f
    else lowest_free used
End

(* The endpoint world: listener lfd on address a, the calls given, every
   write taken (no backpressure), and the arrivals above *)
Definition pew_def:
  pew lfd a hw ifds m w0 calls =
    <| listening := [(lfd, a, [])]; chans := []; open_fds := []; reserved := [];
       alloc := erun_alloc lfd hw ifds m w0; takes := (λj b n. n); calls := calls;
       env := (λn hist. earr lfd a hw ifds m w0 n); clock := 0; hist := [] |>
End

(* No round's response is a connect that got no socket *)
Definition no_socketless_def:
  no_socketless h ⇔ ∀s. MEM s h ⇒ ¬MEM (EConnected NONE) s.results
End

Theorem erounds_logs:
  ∀n h ws evs logs.
    erounds lfd hw ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
    LENGTH logs = n ∧
    ∀k. k ≤ n ⇒ ∃h' ws' evs'. erounds lfd hw ifds m ws0 k = SOME (h', ws', evs', TAKE k logs)
Proof
  Induct >> simp[erounds_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rw[] >>
  Cases_on ‘k = SUC (LENGTH logs')’
  >- (gvs[erounds_def] >> simp[TAKE_LENGTH_ID_rwt]) >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >> strip_tac >>
  simp[TAKE_APPEND1]
QED

Theorem elog_EL:
  erounds lfd hw ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧ k < n ⇒
  elog lfd hw ifds m w0 k = EL k logs
Proof
  rw[elog_def] >> drule erounds_logs >> strip_tac >>
  first_x_assum (qspec_then ‘SUC k’ mp_tac) >> simp[] >> strip_tac >>
  simp[EL_TAKE]
QED

Theorem cnew_snd:
  MAP SND (cnew k fs) = REVERSE (GENLIST (λi. k + i) (LENGTH fs)) ∧
  MAP FST (cnew k fs) = REVERSE fs
Proof
  simp[cnew_def, MAP_REVERSE, MAP_ZIP]
QED

Theorem ecm_inv:
  ∀n. ALL_DISTINCT (MAP SND (FST (ecm lfd hw ifds m w0 n))) ∧
      EVERY (λj. j < SND (ecm lfd hw ifds m w0 n)) (MAP SND (FST (ecm lfd hw ifds m w0 n)))
Proof
  Induct >> simp[ecm_def] >>
  Cases_on ‘ecm lfd hw ifds m w0 n’ >> rename1 ‘_ = (cm, k)’ >> gvs[] >>
  qabbrev_tac ‘fs = econ lfd hw ifds m w0 n’ >>
  Cases_on ‘arrs lfd (cnew k fs ++ cm, k + LENGTH fs) (elog lfd hw ifds m w0 n)’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >> simp[] >>
  drule arrs_inv >> impl_tac
  >- (simp[cnew_snd, ALL_DISTINCT_APPEND, ALL_DISTINCT_REVERSE, MEM_GENLIST, EVERY_MEM,
           MEM_REVERSE, ALL_DISTINCT_GENLIST] >>
      gvs[EVERY_MEM] >> rw[] >> res_tac >> simp[] >>
      strip_tac >> res_tac >> simp[]) >>
  simp[]
QED

Theorem ecm_step:
  ∀n. ∃new'. FST (ecm lfd hw ifds m w0 (SUC n)) = new' ++ FST (ecm lfd hw ifds m w0 n) ∧
             FST (ecm lfd hw ifds m w0 (SUC n)) =
               (new' ++ FST (ecm lfd hw ifds m w0 n))
Proof
  gen_tac >> simp[ecm_def] >>
  Cases_on ‘ecm lfd hw ifds m w0 n’ >> simp[] >>
  qabbrev_tac ‘fs = econ lfd hw ifds m w0 n’ >>
  Cases_on ‘arrs lfd (cnew r fs ++ q, r + LENGTH fs) (elog lfd hw ifds m w0 n)’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >> simp[] >> drule arrs_suffix >> rw[] >>
  qexists_tac ‘new ++ cnew r fs’ >> simp[]
QED

Theorem ecm_mono:
  ∀d n. ∃new. FST (ecm lfd hw ifds m w0 (n + d)) = new ++ FST (ecm lfd hw ifds m w0 n)
Proof
  Induct >> simp[] >> gen_tac >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  qspecl_then [‘n + d’] strip_assume_tac ecm_step >>
  qexists_tac ‘new' ++ new’ >>
  ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> ASM_REWRITE_TAC[]
QED

Theorem ecm_unique:
  MEM (f, j) (FST (ecm lfd hw ifds m w0 n)) ∧ MEM (g, j) (FST (ecm lfd hw ifds m w0 n')) ⇒
  f = g
Proof
  strip_tac >>
  qspecl_then [‘n'’, ‘n’] strip_assume_tac ecm_mono >>
  rename1 ‘FST (ecm _ _ _ _ _ (n + n')) = new1 ++ _’ >>
  qspecl_then [‘n’, ‘n'’] strip_assume_tac ecm_mono >>
  rename1 ‘FST (ecm _ _ _ _ _ (n' + n)) = new2 ++ _’ >>
  ‘n' + n = n + n'’ by simp[] >>
  ‘ALL_DISTINCT (MAP SND (FST (ecm lfd hw ifds m w0 (n + n'))))’ by simp[ecm_inv] >>
  ‘MEM (f, j) (FST (ecm lfd hw ifds m w0 (n + n'))) ∧
   MEM (g, j) (FST (ecm lfd hw ifds m w0 (n + n')))’ by metis_tac[MEM_APPEND] >>
  qspecl_then [‘FST (ecm lfd hw ifds m w0 (n + n'))’, ‘f’, ‘g’, ‘j’] mp_tac snd_unique >> simp[]
QED

Theorem erun_alloc_eq:
  MEM (f, j) (FST (ecm lfd hw ifds m w0 n)) ∧ ¬MEM f used ⇒
  erun_alloc lfd hw ifds m w0 j used = f
Proof
  strip_tac >>
  ‘(@g. ∃n. MEM (g, j) (FST (ecm lfd hw ifds m w0 n))) = f’
    by (SELECT_ELIM_TAC >> metis_tac[ecm_unique]) >>
  rw[erun_alloc_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   R1-safe: the run
   ------------------------------------------------------------------------ *)

(* One round of the layer's run, unfolded *)
Theorem ehround_step:
  ehacts_tot lfd (ehst lfd ifds m w0 n)
    (new_actions (log_of m) (ehhist lfd ifds m w0 n)) = (rs, (w1, hs1)) ∧
  ehpoll lfd hs1 (ifds (ehhist lfd ifds m w0 n)) w1 = (rdy, w2, hs2) ⇒
  ehhist lfd ifds m w0 (SUC n) = ehhist lfd ifds m w0 n ++ [ssnap rdy rs] ∧
  ehst lfd ifds m w0 (SUC n) = (w2, hs2)
Proof
  strip_tac >> simp[ehhist_def, ehst_def, ehrounds_def] >>
  Cases_on ‘ehrounds lfd ifds m w0 n’ >> rename1 ‘_ = (h, st)’ >> PairCases_on ‘st’ >>
  gvs[ehhist_def, ehst_def]
QED

Theorem no_socketless_APPEND:
  no_socketless (h ++ h') ⇔ no_socketless h ∧ no_socketless h'
Proof
  simp[no_socketless_def] >> metis_tac[]
QED

(* MAIN (R1-safe), for a run looked at up to round N: in ANY L0 world, the
   prefetching L1 with connects running the computation m has exactly the
   history of the endpoint handle layer running m in the endpoint world pew
   built from L1's own run, round by round, provided no connect got no
   socket; the relation and the invariants hold throughout *)
Theorem l1ep_refines_ehl_upto:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ N ⇒ SND (ecm lfd hw ifds m w0 n') + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    n ≤ N ∧ erounds lfd hw ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
    no_socketless h ⇒
    ehhist lfd ifds m (pew lfd a hw ifds m w0 calls) n = h ∧
    ehs_rel (SND (ehst lfd ifds m (pew lfd a hw ifds m w0 calls) n)) (SND ws) ∧
    ev_rel lfd a (FST (ecm lfd hw ifds m w0 n)) (SND ws)
      (FST (ehst lfd ifds m (pew lfd a hw ifds m w0 calls) n)) ∧
    LENGTH (FST (ehst lfd ifds m (pew lfd a hw ifds m w0 calls) n)).chans =
      SND (ecm lfd hw ifds m w0 n) ∧
    (FST (ehst lfd ifds m (pew lfd a hw ifds m w0 calls) n)).alloc =
      erun_alloc lfd hw ifds m w0 ∧
    (FST (ehst lfd ifds m (pew lfd a hw ifds m w0 calls) n)).env =
      (λn hist. earr lfd a hw ifds m w0 n) ∧
    (FST (ehst lfd ifds m (pew lfd a hw ifds m w0 calls) n)).clock = n ∧
    (FST (ehst lfd ifds m (pew lfd a hw ifds m w0 calls) n)).hist = [] ∧
    eown lfd (SND ws) ∧ l0owne lfd (FST ws) (SND ws) ∧
    l0_rely (FST ws) ∧ fds_lt (FST ws)
Proof
  strip_tac >> Induct
  >- (simp[erounds_def, ehhist_def, ehst_def, ehrounds_def, ecm_def, pew_def] >>
      rw[] >> simp[einit_def, pinit_def, l1init_def, ehinit_def, ehs_rel_def, ev_rel_def,
                   eown_def, pown_def, l0owne_def, l0own_def, inb_of_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ‘n ≤ N ∧ no_socketless h'’ by gvs[no_socketless_APPEND] >>
  qpat_x_assum ‘∀h ws evs logs. _’ (qspecl_then [‘h'’, ‘ws'’, ‘evs'’, ‘logs'’] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ ws' _ = SOME (rs, aevs, ws1)’ >>
  PairCases_on ‘ws'’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws’ >> fs[] >>
  qabbrev_tac ‘W0 = pew lfd a hw ifds m w0 calls’ >>
  Cases_on ‘ehst lfd ifds m W0 n’ >> rename1 ‘_ = (w, hs)’ >> fs[] >>
  Cases_on ‘ecm lfd hw ifds m w0 n’ >> rename1 ‘ecm _ _ _ _ _ n = (cm, k)’ >> fs[] >>
  ‘eacts_of lfd hw ifds m w0 n = SOME (rs, aevs, (ws10, ws11))’ by simp[eacts_of_def] >>
  ‘econ lfd hw ifds m w0 n = rfds ws11 rs’ by simp[econ_def] >>
  ‘elog lfd hw ifds m w0 n = log’
    by (‘LENGTH logs' = n’
          by (qpat_x_assum ‘erounds _ _ _ _ _ n = _’ assume_tac >>
              drule erounds_logs >> simp[]) >>
        qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule elog_EL >> disch_then (qspec_then ‘n’ mp_tac) >> simp[EL_APPEND2]) >>
  ‘ecm1 lfd hw ifds m w0 n = (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs))’
    by simp[ecm1_def] >>
  qabbrev_tac ‘fs = rfds ws11 rs’ >>
  Cases_on ‘arrs lfd (cnew k fs ++ cm, k + LENGTH fs) log’ >> rename1 ‘_ = (as, ck)’ >>
  PairCases_on ‘ck’ >> rename1 ‘arrs _ _ _ = (as, cm', k')’ >>
  ‘ecm lfd hw ifds m w0 (SUC n) = (cm', k')’ by simp[ecm_SUC] >>
  ‘∃new. cm' = new ++ (cnew k fs ++ cm)’ by (drule arrs_suffix >> simp[]) >>
  ‘∀f j. MEM (f, j) cm' ⇒ ∀used. ¬MEM f used ⇒ erun_alloc lfd hw ifds m w0 j used = f’
    by (rpt strip_tac >> irule erun_alloc_eq >> simp[] >> qexists_tac ‘SUC n’ >>
        qpat_x_assum ‘ecm _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        REWRITE_TAC [pairTheory.FST] >> first_assum ACCEPT_TAC) >>
  ‘¬MEM (EConnected NONE) rs’
    by (qpat_x_assum ‘no_socketless (_ ++ [_])’ mp_tac >>
        simp[no_socketless_APPEND, no_socketless_def, ssnap_def]) >>
  ‘∀f j. MEM (f, j) (cnew (LENGTH w.chans) (rfds ws11 rs)) ⇒
         ∀used. ¬MEM f used ⇒ w.alloc j used = f’
    by (rpt strip_tac >>
        qpat_x_assum ‘w.alloc = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘∀f j. MEM (f, j) cm' ⇒ _’ irule >> simp[] >>
        qpat_x_assum ‘cm' = _’ SUBST1_TAC >> simp[MEM_APPEND] >>
        qpat_x_assum ‘MEM _ (cnew _ _)’ mp_tac >> fs[Abbr ‘fs’]) >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule_all ev_acts >> strip_tac >>
  rename1 ‘ehacts lfd (w, hs) _ = SOME (rs, (w1, hs1))’ >>
  ‘LENGTH w1.chans = k + LENGTH fs’ by simp[Abbr ‘fs’, rfds_length] >>
  ‘cnew (LENGTH w.chans) (rfds ws11 rs) = cnew k fs’ by simp[Abbr ‘fs’] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  ‘arrs lfd (cnew k fs ++ cm, LENGTH w1.chans) log = (as, (cm', k'))’ by simp[] >>
  ‘∀f j. MEM (f, j) cm' ∧ LENGTH w1.chans ≤ j ⇒ ∀used. ¬MEM f used ⇒ w1.alloc j used = f’
    by (rpt strip_tac >> qpat_x_assum ‘w1.alloc = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘w.alloc = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘∀f j. MEM (f, j) cm' ⇒ _’ irule >> simp[]) >>
  ‘k' + 1 < dimword (:64)’
    by (qpat_x_assum ‘∀n'. n' ≤ N ⇒ _’ (qspec_then ‘SUC n’ mp_tac) >> simp[]) >>
  ‘esett lfd hw ifds m w0 n = rsettles (cnew k fs ++ cm) ws11 ws1’
    by simp[esett_def] >>
  ‘w1.env w1.clock w1.hist = MAP (conv a) as ++ rsettles (cnew k fs ++ cm) ws11 ws1’
    by (simp[earr_def] >> fs[]) >>
  qpat_x_assum ‘etail _ _ _ _ = _’ assume_tac >>
  drule_all ev_tail >> strip_tac >>
  rename1 ‘ehpoll lfd hs1 _ w1 = (rdy, w2, hs2)’ >>
  ‘ehacts_tot lfd (ehst lfd ifds m W0 n) (new_actions (log_of m) (ehhist lfd ifds m W0 n)) =
   (rs, (w1, hs1))’ by simp[ehacts_tot_def] >>
  drule_all ehround_step >> strip_tac >> simp[] >> fs[] >>
  qpat_x_assum ‘ev_rel _ _ cm' ws1 w2’ mp_tac >>
  qpat_x_assum ‘cm' = _’ (fn th => rewrite_tac[th]) >>
  rewrite_tac[APPEND_ASSOC]
QED
