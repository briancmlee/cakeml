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
