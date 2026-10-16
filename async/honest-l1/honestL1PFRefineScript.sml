(*
  R1-safe for the prefetching L1 (design/36 §6): L1 (honestL1PFModel) in
  ANY L0 world refines close-v2's handle layer (asyncHLModel) in a
  version-2 world built from L1's own run.

  The version-2 world's state mirrors L1's buffers:
   - client j is the j-th connection L1 accepted (the fetch log's j-th
     FConn); cm maps each such fd to its client (the latest one: fds are
     reused);
   - an open handle's client has incoming = the fd's inbox and
     peer_closed = the fd's EOF;
   - the listener's pending clients are L1's accept queue;
   - the open fds are the handles' fds, which are the kernel's (alloc
     returns the kernel's fd).
  This theory proves one round of L1 matches one round of the handle
  layer (pdo_hdo for an action; then the tail); the run and the world's
  schedule follow.
*)
Theory honestL1PFRefine
Ancestors
  honestL0WorldProps
  honestL1PFModel honestL1Model honestL1Steps honestL1Inv honestL0Rely honestL0World honestL0
  asyncHLModel
  socketV2FFI socketV2Events socketV2Fair ffiSpikeSocketFFI asyncM3World asyncCore
  asyncLevel1 llist alist
Libs
  preamble

(* ------------------------------------------------------------------------
   The relation
   ------------------------------------------------------------------------ *)

(* The client of fd f *)
Definition cl_def:
  cl (cm : (word64 # num) list) f = case ALOOKUP cm f of SOME j => j | NONE => 0
End

(* The version-2 world s mirrors L1's state ps (with client map cm) *)
Definition pv_rel_def:
  pv_rel lfd cm ps s ⇔
    s.listening = [(lfd, MAP (cl cm) ps.acq)] ∧ s.reserved = [] ∧
    ALL_DISTINCT (MAP FST s.open_fds) ∧
    (∀f. MEM f (MAP FST s.open_fds) ⇔ MEM f (MAP SND ps.b.tbl)) ∧
    ALL_DISTINCT (MAP SND cm) ∧ EVERY (λj. j < LENGTH s.clients) (MAP SND cm) ∧
    (∀h f. ALOOKUP ps.b.tbl h = SOME f ⇒
       MEM f (MAP FST cm) ∧ ALOOKUP s.open_fds f = SOME (cl cm f) ∧
       (EL (cl cm f) s.clients).incoming = inb_of ps f ∧
       ((EL (cl cm f) s.clients).peer_closed ⇔ MEM f ps.eof)) ∧
    (∀f. MEM f ps.acq ⇒
       MEM f (MAP FST cm) ∧
       (EL (cl cm f) s.clients).incoming = [] ∧ ¬(EL (cl cm f) s.clients).peer_closed ∧
       ∀used. ¬MEM f used ⇒ s.alloc (cl cm f) used = f)
End

(* L1's own invariant: its fds are distinct, its handles distinct and
   issued, and only open handles' fds have input *)
Definition pown_def:
  pown lfd ps ⇔
    ALL_DISTINCT (lfd :: MAP SND ps.b.tbl ++ ps.b.closing ++ ps.acq) ∧
    ALL_DISTINCT (MAP FST ps.b.tbl) ∧
    (∀h f. ALOOKUP ps.b.tbl h = SOME f ⇒ ∃i. i < ps.b.nxt ∧ h = l1hdl lfd i) ∧
    (∀f. inb_of ps f ≠ [] ∨ MEM f ps.eof ⇒ MEM f (MAP SND ps.b.tbl))
End

(* The handle layer's state is L1's tables *)
Definition hs_of_def:
  hs_of ps = <| tbl := ps.b.tbl; nxt := ps.b.nxt |>
End

(* ------------------------------------------------------------------------
   Lemmas
   ------------------------------------------------------------------------ *)

Theorem cl_inj:
  ALL_DISTINCT (MAP SND cm) ∧ MEM f (MAP FST cm) ∧ MEM g (MAP FST cm) ∧
  cl cm f = cl cm g ⇒ f = g
Proof
  rw[cl_def] >>
  ‘∃j. ALOOKUP cm f = SOME j’ by (Cases_on ‘ALOOKUP cm f’ >> gvs[ALOOKUP_NONE]) >>
  ‘∃k. ALOOKUP cm g = SOME k’ by (Cases_on ‘ALOOKUP cm g’ >> gvs[ALOOKUP_NONE]) >>
  gvs[] >>
  imp_res_tac ALOOKUP_MEM >>
  spose_not_then assume_tac >>
  ‘∃i1 i2. i1 < LENGTH cm ∧ i2 < LENGTH cm ∧ EL i1 cm = (f, j) ∧ EL i2 cm = (g, j)’
    by metis_tac[MEM_EL] >>
  ‘i1 ≠ i2’ by (strip_tac >> gvs[]) >>
  gvs[EL_ALL_DISTINCT_EL_EQ] >>
  first_x_assum (qspecl_then [‘i1’, ‘i2’] mp_tac) >> simp[EL_MAP]
QED

Theorem ALOOKUP_SOME_MEM_SND:
  ALOOKUP l k = SOME v ⇒ MEM v (MAP SND l)
Proof
  rw[] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]
QED

Theorem ALOOKUP_SOME_MEM_FST:
  ALOOKUP l k = SOME v ⇒ MEM k (MAP FST l)
Proof
  rw[] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[FST]
QED

(* A distinct list inside the image of count n has at most n elements *)
Theorem tbl_length_le:
  ALL_DISTINCT (MAP FST tbl) ∧
  (∀h f. ALOOKUP tbl h = SOME f ⇒ ∃i. i < n ∧ h = g i) ⇒
  LENGTH tbl ≤ n
Proof
  rw[] >>
  ‘set (MAP FST tbl) ⊆ IMAGE g (count n)’
    by (rw[SUBSET_DEF, MEM_MAP] >> rename1 ‘MEM p tbl’ >> PairCases_on ‘p’ >>
        ‘ALOOKUP tbl p0 ≠ NONE’ by (simp[ALOOKUP_NONE, MEM_MAP] >> metis_tac[FST]) >>
        Cases_on ‘ALOOKUP tbl p0’ >> gvs[] >> res_tac >> metis_tac[]) >>
  ‘CARD (set (MAP FST tbl)) ≤ CARD (IMAGE g (count n))’
    by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (IMAGE g (count n)) ≤ n’ by metis_tac[CARD_IMAGE, CARD_COUNT, FINITE_COUNT] >>
  gvs[ALL_DISTINCT_CARD_LIST_TO_SET]
QED

Theorem hdln_suc_lt:
  hdln (w2n (lfd:word64)) n < dimword (:64) ⇒ n + 1 < dimword (:64)
Proof
  rw[hdln_def] >> Cases_on ‘lfd’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

Theorem l1do_write_tbl:
  l1do lfd (w, st) (Write h bs) = SOME (r, (w', st'), evs) ⇒
  r = Wrote ∧ st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧ st'.closing = st.closing
Proof
  rw[l1do_def, AllCaseEqs()] >> gvs[set_outbox_def] >>
  Cases_on ‘l0_res_of out’ >> gvs[after_send_def, set_outbox_def] >> rw[]
QED

Theorem pv_rel_b:
  b'.tbl = ps.b.tbl ⇒ (pv_rel lfd cm (ps with b := b') s ⇔ pv_rel lfd cm ps s)
Proof
  simp[pv_rel_def, inb_of_def]
QED

Theorem pown_b:
  b'.tbl = ps.b.tbl ∧ b'.nxt = ps.b.nxt ∧ b'.closing = ps.b.closing ⇒
  (pown lfd (ps with b := b') ⇔ pown lfd ps)
Proof
  simp[pown_def, inb_of_def]
QED

Theorem EL_LUPDATE_outgoing[simp]:
  (EL i (LUPDATE ((EL j l) with outgoing := x) j l)).incoming = (EL i l).incoming ∧
  (EL i (LUPDATE ((EL j l) with outgoing := x) j l)).peer_closed = (EL i l).peer_closed
Proof
  rw[EL_LUPDATE] >> rw[]
QED

Theorem pdo_write:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs) ⇒
  ∃s' hevs. hdo lfd (s, hs_of ps) (Write h bs) = SOME (r, (s', hs_of ps'), hevs) ∧
            pv_rel lfd cm ps' s' ∧ pown lfd ps'
Proof
  rw[pdo_def] >> pairarg_tac >> gvs[] >>
  rename1 ‘l1do _ _ _ = SOME (r, (w', b'), evs)’ >>
  drule l1do_write_tbl >> strip_tac >> gvs[] >>
  ‘hs_of (ps with b := b') = hs_of ps’ by simp[hs_of_def] >>
  simp[pv_rel_b, pown_b] >>
  simp[hdo_def, hs_of_def] >>
  Cases_on ‘ALOOKUP ps.b.tbl h’ >> simp[] >>
  rename1 ‘ALOOKUP _ h = SOME f’ >>
  ‘ALOOKUP s.open_fds f = SOME (cl cm f) ∧ cl cm f < LENGTH s.clients’
    by (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >> simp[pv_rel_def] >> strip_tac >>
        first_x_assum drule >> strip_tac >> simp[] >>
        gvs[EVERY_MEM, cl_def] >>
        Cases_on ‘ALOOKUP cm f’ >> gvs[ALOOKUP_NONE] >>
        metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  simp[sock_write2_def, client_of_def, update_client_def] >>
  qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >>
  simp[pv_rel_def] >> metis_tac[]
QED

Theorem open_fds_length:
  pv_rel lfd cm ps s ∧ pown lfd ps ⇒ LENGTH s.open_fds = LENGTH ps.b.tbl
Proof
  rw[pv_rel_def, pown_def] >>
  ‘set (MAP FST s.open_fds) = set (MAP SND ps.b.tbl)’ by simp[EXTENSION] >>
  ‘ALL_DISTINCT (MAP SND ps.b.tbl)’ by gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET, LENGTH_MAP]
QED

Theorem pdo_accept:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧
  pdo lfd (w, ps) (Accept l) = SOME (r, (w', ps'), evs) ⇒
  ∃s' hevs. hdo lfd (s, hs_of ps) (Accept l) = SOME (r, (s', hs_of ps'), hevs) ∧
            pv_rel lfd cm ps' s' ∧ pown lfd ps'
Proof
  rw[pdo_def] >> Cases_on ‘ps.acq’ >> gvs[]
  >- (‘ALOOKUP s.listening l = SOME []’ by gvs[pv_rel_def] >>
      simp[hdo_def, sock_accept2_def]) >>
  rename1 ‘ps.acq = f :: q’ >>
  ‘LENGTH ps.b.tbl ≤ ps.b.nxt’
    by (irule tbl_length_le >> gvs[pown_def] >> metis_tac[]) >>
  ‘ps.b.nxt + 1 < dimword (:64)’ by (irule hdln_suc_lt >> qexists_tac ‘l’ >> simp[]) >>
  drule_all open_fds_length >> strip_tac >>
  ‘f ≠ l ∧ ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f q ∧ ¬MEM f ps.b.closing’
    by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘inb_of ps f = [] ∧ ¬MEM f ps.eof’ by (gvs[pown_def] >> metis_tac[]) >>
  ‘¬MEM f (used_fds s)’ by gvs[used_fds_def, pv_rel_def] >>
  ‘s.alloc (cl cm f) (used_fds s) = f’ by gvs[pv_rel_def] >>
  ‘LENGTH (used_fds s) < dimword (:64)’ by gvs[used_fds_def, pv_rel_def] >>
  simp[hdo_def, sock_accept2_def] >>
  ‘ALOOKUP s.listening l = SOME (cl cm f :: MAP (cl cm) q)’ by gvs[pv_rel_def] >>
  simp[hs_of_def] >>
  conj_tac
  >- (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >>
      simp[pv_rel_def, AFUPDKEY_def, inb_of_def] >> strip_tac >>
      gvs[inb_of_def] >> rw[] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  qpat_x_assum ‘pown _ _’ mp_tac >>
  simp[pown_def, inb_of_def] >> strip_tac >> gvs[inb_of_def] >>
  ‘hdln (w2n l) ps.b.nxt < dimword (:64)’ by simp[] >>
  rpt conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (strip_tac >>
      ‘ALOOKUP ps.b.tbl (hdl l ps.b.nxt) ≠ NONE’ by simp[ALOOKUP_NONE] >>
      Cases_on ‘ALOOKUP ps.b.tbl (hdl l ps.b.nxt)’ >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      ‘hdl l i ≠ hdl l ps.b.nxt’ by (irule hdl_fresh >> simp[]) >> gvs[]) >>
  rw[] >- (qexists_tac ‘ps.b.nxt’ >> simp[]) >>
  first_x_assum drule >> strip_tac >> qexists_tac ‘i’ >> simp[]
QED

Theorem l1_close_b:
  l1_close f (w, b) = SOME ((w', b'), evs) ⇒
  b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧ b'.closing = FILTER ($≠ f) b.closing
Proof
  rw[l1_close_def, AllCaseEqs()] >> simp[forget_def, set_outbox_def]
QED

Theorem alookup_snd_inj:
  ALL_DISTINCT (MAP FST l) ∧ ALL_DISTINCT (MAP SND l) ∧
  ALOOKUP l h = SOME f ∧ ALOOKUP l h' = SOME f ⇒ h = h'
Proof
  Induct_on ‘l’ >> simp[FORALL_PROD] >> rw[] >> gvs[] >>
  metis_tac[ALOOKUP_SOME_MEM_SND]
QED

Theorem ADELKEY_not_MEM:
  ¬MEM k (MAP FST l) ⇒ ADELKEY k l = l
Proof
  Induct_on ‘l’ >> simp[FORALL_PROD, ADELKEY_def] >> rw[] >>
  gvs[ADELKEY_def]
QED

Theorem MEM_SND_ADELKEY:
  ALL_DISTINCT (MAP FST l) ∧ ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l h = SOME f ⇒
  (MEM g (MAP SND (ADELKEY h l)) ⇔ MEM g (MAP SND l) ∧ g ≠ f)
Proof
  Induct_on ‘l’ >> simp[FORALL_PROD] >> rw[] >> gvs[]
  >- (simp[Once ADELKEY_def] >> simp[GSYM ADELKEY_def, ADELKEY_not_MEM] >>
      metis_tac[])
  >> simp[Once ADELKEY_def] >> simp[GSYM ADELKEY_def] >>
  imp_res_tac ALOOKUP_SOME_MEM_SND >> metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_FST_ADELKEY:
  ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP FST (ADELKEY k l))
Proof
  simp[ADELKEY_def] >> Induct_on ‘l’ >> simp[FORALL_PROD] >> rw[] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem pv_rel_tbl:
  pv_rel lfd cm ps s ∧ ALOOKUP ps.b.tbl h = SOME f ⇒
  client_of s f = SOME (cl cm f) ∧ cl cm f < LENGTH s.clients ∧
  ALOOKUP s.open_fds f = SOME (cl cm f) ∧ MEM f (MAP FST cm) ∧
  (EL (cl cm f) s.clients).incoming = inb_of ps f ∧
  ((EL (cl cm f) s.clients).peer_closed ⇔ MEM f ps.eof)
Proof
  simp[pv_rel_def] >> strip_tac >> first_x_assum drule >> strip_tac >>
  ‘cl cm f < LENGTH s.clients’
    by (gvs[EVERY_MEM, cl_def] >> Cases_on ‘ALOOKUP cm f’ >> gvs[ALOOKUP_NONE] >>
        metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  simp[client_of_def]
QED

Theorem set_inb_fields[simp]:
  (set_inb f x ps).b = ps.b ∧ (set_inb f x ps).acq = ps.acq ∧
  (set_inb f x ps).eof = ps.eof ∧ (set_inb f x ps).pause = ps.pause ∧
  inb_of (set_inb f x ps) g = if g = f then x else inb_of ps g
Proof
  rw[set_inb_def, inb_of_def, ALOOKUP_ADELKEY] >> rw[]
QED

(* fds of open handles and queued fds have distinct clients *)
Theorem cl_tbl_ne:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ ALOOKUP ps.b.tbl h = SOME f ⇒
  (∀h' f'. ALOOKUP ps.b.tbl h' = SOME f' ∧ f' ≠ f ⇒ cl cm f' ≠ cl cm f) ∧
  (∀f'. MEM f' ps.acq ⇒ cl cm f' ≠ cl cm f)
Proof
  strip_tac >>
  ‘∀g. (∃h. ALOOKUP ps.b.tbl h = SOME g) ∨ MEM g ps.acq ⇒ MEM g (MAP FST cm)’
    by (gvs[pv_rel_def] >> metis_tac[]) >>
  ‘ALL_DISTINCT (MAP SND cm)’ by gvs[pv_rel_def] >>
  ‘MEM f (MAP SND ps.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
  rw[] >> strip_tac
  >- metis_tac[cl_inj] >>
  ‘f' = f’ by metis_tac[cl_inj] >>
  gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem MEM_FST_ADELKEY:
  MEM g (MAP FST (ADELKEY k l)) ⇔ MEM g (MAP FST l) ∧ g ≠ k
Proof
  simp[ADELKEY_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_SND_ADELKEY:
  ALL_DISTINCT (MAP SND l) ⇒ ALL_DISTINCT (MAP SND (ADELKEY k l))
Proof
  simp[ADELKEY_def] >> Induct_on ‘l’ >> simp[FORALL_PROD] >> rw[] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* The handle layer's auto-close at EOF, against L1's *)
Theorem read_eof_rel:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ ALOOKUP ps.b.tbl h = SOME f ∧
  inb_of ps f = [] ∧
  ps'.b.tbl = ADELKEY h ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ∧ ps'.acq = ps.acq ∧
  ps'.inb = ps.inb ∧ ps'.eof = FILTER ($≠ f) ps.eof ∧
  (ps'.b.closing = FILTER ($≠ f) ps.b.closing ∨ ps'.b.closing = f :: ps.b.closing) ⇒
  pv_rel lfd cm ps' (s with open_fds := ADELKEY f s.open_fds) ∧ pown lfd ps'
Proof
  strip_tac >> (
  ‘ALL_DISTINCT (MAP FST ps.b.tbl) ∧ ALL_DISTINCT (MAP SND ps.b.tbl) ∧
   lfd ≠ f ∧ ¬MEM f ps.b.closing ∧ ¬MEM f ps.acq ∧ ¬MEM lfd (MAP SND ps.b.tbl)’
    by (‘MEM f (MAP SND ps.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
        gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘∀g. MEM g (MAP SND (ADELKEY h ps.b.tbl)) ⇔ MEM g (MAP SND ps.b.tbl) ∧ g ≠ f’
    by metis_tac[MEM_SND_ADELKEY] >>
  ‘inb_of ps' = inb_of ps’ by simp[FUN_EQ_THM, inb_of_def] >>
  conj_tac
  >- (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >>
      simp[pv_rel_def, MEM_FST_ADELKEY, ALL_DISTINCT_MAP_FST_ADELKEY,
           ALOOKUP_ADELKEY, MEM_FILTER] >>
      strip_tac >> rw[] >>
      gvs[ALOOKUP_ADELKEY, AllCaseEqs()] >>
      metis_tac[alookup_snd_inj]) >>
  qpat_x_assum ‘pown _ _’ mp_tac >>
  simp[pown_def, ALOOKUP_ADELKEY, ALL_DISTINCT_MAP_FST_ADELKEY, MEM_FILTER] >>
  strip_tac >>
  ‘ALL_DISTINCT (MAP SND (ADELKEY h ps.b.tbl))’
    by simp[ALL_DISTINCT_MAP_SND_ADELKEY] >>
  gvs[ALL_DISTINCT_APPEND, MEM_FILTER, FILTER_ALL_DISTINCT] >> metis_tac[])
QED

Theorem pdo_read:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧
  pdo lfd (w, ps) (Read h n) = SOME (r, (w', ps'), evs) ⇒
  ∃s' hevs. hdo lfd (s, hs_of ps) (Read h n) = SOME (r, (s', hs_of ps'), hevs) ∧
            pv_rel lfd cm ps' s' ∧ pown lfd ps'
Proof
  rpt strip_tac >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
  simp[pdo_def] >> strip_tac >>
  simp[hdo_def, hs_of_def] >>
  Cases_on ‘ALOOKUP ps.b.tbl h’ >> gvs[] >>
  rename1 ‘ALOOKUP _ h = SOME f’ >>
  drule_all pv_rel_tbl >> strip_tac >>
  simp[sock_read2_def] >>
  Cases_on ‘inb_of ps f = []’ >> gvs[]
  >- (Cases_on ‘MEM f ps.eof’ >> gvs[]
      >- (simp[sock_close2_def] >>
          ‘r = Got (SOME []) ∧ ps'.b.tbl = ADELKEY h ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ∧
           ps'.acq = ps.acq ∧ ps'.inb = ps.inb ∧ ps'.eof = FILTER ($≠ f) ps.eof ∧
           (ps'.b.closing = FILTER ($≠ f) ps.b.closing ∨
            ps'.b.closing = f :: ps.b.closing)’
            by (qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> gvs[] >>
                Cases_on ‘l1_close f (w, ps.b with tbl := ADELKEY h ps.b.tbl)’ >>
                gvs[] >> rename1 ‘l1_close _ _ = SOME x’ >> PairCases_on ‘x’ >>
                gvs[] >> drule l1_close_b >> simp[]) >>
          gvs[] >> irule read_eof_rel >> simp[] >> metis_tac[]) >>
      simp[hs_of_def]) >>
  ‘∃x xs. TAKE n (inb_of ps f) = x :: xs’
    by (Cases_on ‘inb_of ps f’ >> gvs[] >> Cases_on ‘n’ >> gvs[]) >>
  simp[] >>
  drule_all cl_tbl_ne >> strip_tac >>
  conj_tac
  >- (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >>
      simp[pv_rel_def, update_client_def, EL_LUPDATE] >> strip_tac >>
      rw[] >> gvs[] >> res_tac >> gvs[]) >>
  qpat_x_assum ‘pown _ _’ mp_tac >> simp[pown_def] >> rw[] >>
  Cases_on ‘f' = f’ >> gvs[] >> metis_tac[ALOOKUP_SOME_MEM_SND]
QED

Theorem pdo_hdo:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  ∃s' hevs. hdo lfd (s, hs_of ps) a = SOME (r, (s', hs_of ps'), hevs) ∧
            pv_rel lfd cm ps' s' ∧ pown lfd ps'
Proof
  Cases_on ‘a’ >> metis_tac[pdo_accept, pdo_read, pdo_write]
QED

Theorem pacts_hacts:
  ∀acts w ps s rs evs w' ps'.
    pv_rel lfd cm ps s ∧ pown lfd ps ∧
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    ∃s' hevs. hacts lfd (s, hs_of ps) acts = SOME (rs, hevs, (s', hs_of ps')) ∧
              pv_rel lfd cm ps' s' ∧ pown lfd ps'
Proof
  Induct >> simp[pacts_def, hacts_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all pdo_hdo >> strip_tac >> simp[] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The L0 side: the fds L1 holds stay open, and an accepted fd is fresh
   ------------------------------------------------------------------------ *)

(* The fds L1 holds are open in the L0 world *)
Definition l0own_def:
  l0own lfd w ps ⇔
    ∀f. f = lfd ∨ MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ∨ MEM f ps.acq ⇒
        MEM f (l0_used w)
End

Theorem pause_simps[simp]:
  pf_ready lfd (ps with pause := x) hs = pf_ready lfd ps hs ∧
  hs_of (ps with pause := x) = hs_of ps
Proof
  simp[pf_ready_def, hs_of_def, inb_of_def]
QED

Theorem rel_pause[simp]:
  (pv_rel lfd cm (ps with pause := x) s ⇔ pv_rel lfd cm ps s) ∧
  (pown lfd (ps with pause := x) ⇔ pown lfd ps) ∧
  (l0own lfd w (ps with pause := x) ⇔ l0own lfd w ps)
Proof
  simp[pv_rel_def, pown_def, l0own_def, inb_of_def]
QED

Theorem rel_hup[simp]:
  (pv_rel lfd cm (hup_step hfs ob log ps) s ⇔ pv_rel lfd cm ps s) ∧
  (pown lfd (hup_step hfs ob log ps) ⇔ pown lfd ps) ∧
  (l0own lfd w (hup_step hfs ob log ps) ⇔ l0own lfd w ps) ∧
  hs_of (hup_step hfs ob log ps) = hs_of ps ∧
  inb_of (hup_step hfs ob log ps) f = inb_of ps f
Proof
  simp[pv_rel_def, pown_def, l0own_def, hs_of_def, inb_of_def]
QED

Theorem lowest_fd_fresh:
  fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ⇒ ¬MEM (lowest_fd w) (l0_used w)
Proof
  rw[lowest_fd_def, fds_lt_def] >>
  numLib.LEAST_ELIM_TAC >> conj_tac
  >- (qexists_tac ‘2 ** 31’ >> strip_tac >> first_x_assum drule >> simp[]) >>
  rw[]
QED

Theorem used_upd_lchan[simp]:
  l0_used (upd_lchan j g w) = l0_used w
Proof
  simp[upd_lchan_def, l0_used_def]
QED

Theorem used_FOLDL_upd_lchan[simp]:
  ∀q w. l0_used (FOLDL (λw j. upd_lchan j g w) w q) = l0_used w
Proof
  Induct >> simp[]
QED

Theorem ops_used:
  (l0_accept l w = (r, w') ⇒
     (∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w')) ∧
     ∀k. r = Ok k ⇒ ∃f. k = w2n f ∧ f = lowest_fd w) ∧
  (l0_recv f n w = (r, d, w') ⇒ l0_used w' = l0_used w) ∧
  (l0_send f bs w = (r, w') ⇒ l0_used w' = l0_used w) ∧
  (l0_close f w = (r, w') ⇒ ∀g. g ≠ f ∧ MEM g (l0_used w) ⇒ MEM g (l0_used w'))
Proof
  rpt conj_tac
  >- (simp[l0_accept_def] >> rpt (CASE_TAC >> gvs[]) >>
      rw[] >> gvs[l0_used_def, AFUPDKEY_MAP_FST, l0_alloc_def, fail_def, AllCaseEqs()])
  >- (rw[l0_recv_def, AllCaseEqs()] >> gvs[])
  >- (rw[l0_send_def, AllCaseEqs()] >> gvs[])
  >> rw[l0_close_def, close_fd_def, AllCaseEqs()] >> gvs[] >>
  gvs[l0_used_def, MEM_FST_ADELKEY, MEM_FILTER, MEM_MAP, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem used_tick[simp]:
  l0_used (l0_tick n w) = l0_used w ∧ (l0_tick n w).fd_limit = w.fd_limit
Proof
  simp[l0_tick_def] >>
  ‘∀as w. (FOLDL l0_deliver w as).fd_limit = w.fd_limit’
    by (Induct >> simp[]) >> simp[]
QED

Theorem used_ticks[simp]:
  ∀k w. l0_used (l0_ticks n k w) = l0_used w
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem l0_do_used:
  l0_do n conf alen w = SOME (out, w', ev) ⇒
  ((n = «sys_recv» ∨ n = «sys_send» ∨ n = «sys_poll») ⇒ l0_used w' = l0_used w) ∧
  (n = «sys_accept» ⇒ ∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w')) ∧
  (n = «sys_close» ⇒ ∀g. g ≠ bytes_fd conf ∧ MEM g (l0_used w) ⇒ MEM g (l0_used w'))
Proof
  rw[l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac ops_used >> gvs[]
QED

Theorem sys_accept_fresh:
  l0_rely w ∧ fds_lt w ∧
  sys_accept l w = SOME (out, w', ev) ∧ l0_res_of out = Ok k ⇒
  ¬MEM (n2w k) (l0_used w)
Proof
  rw[sys_accept_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  ‘l0_rely (l0_tick «sys_accept» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_all l0_accept_res >> strip_tac >>
  gvs[l0_res_of_enc] >>
  imp_res_tac ops_used >> gvs[] >>
  ‘lowest_fd (l0_tick «sys_accept» w) = lowest_fd w’ by simp[lowest_fd_def] >>
  ‘w.fd_limit ≤ 2 ** 31’ by gvs[l0_rely_def] >>
  drule_all lowest_fd_fresh >> simp[]
QED

(* ------------------------------------------------------------------------
   The fetch: what L1 fetched arrives in the version-2 world
   ------------------------------------------------------------------------ *)

(* The arrivals of a fetch log, given the client map cm and the number of
   clients k so far; and the client map and count after *)
Definition arrs_def:
  arrs lfd (cm, k) [] = ([], (cm, k)) ∧
  arrs lfd (cm, k) (FConn f :: l) =
    (let (as, ck) = arrs lfd ((f, k) :: cm, k + 1) l in (Connect2 lfd :: as, ck)) ∧
  arrs lfd (cm, k) (FData f bs :: l) =
    (let (as, ck) = arrs lfd (cm, k) l in (Data2 (cl cm f) bs :: as, ck)) ∧
  arrs lfd (cm, k) (FEof f :: l) =
    (let (as, ck) = arrs lfd (cm, k) l in (Eof2 (cl cm f) :: as, ck)) ∧
  arrs lfd (cm, k) (FReset f :: l) =
    (let (as, ck) = arrs lfd (cm, k) l in (Eof2 (cl cm f) :: as, ck))
End

(* The client count grows by the log's accepted connections (FConn) *)
Theorem arrs_count:
  ∀l cm k as cm' k'.
    arrs lfd (cm, k) l = (as, (cm', k')) ⇒
    k' = k + LENGTH (FILTER (λx. ∃g. x = FConn g) l)
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> PairCases_on ‘ck’ >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Delivering arrivals keeps the world's allocation *)
Theorem deliver2_alloc[simp]:
  (deliver2 s a).alloc = s.alloc ∧ (deliver2 s a).reserved = s.reserved ∧
  (deliver2 s a).open_fds = s.open_fds
Proof
  Cases_on ‘a’ >> rw[deliver2_def, update_client_def]
QED

Theorem sys_accept_adds:
  sys_accept l w = SOME (out, w', ev) ∧ l0_rely w ∧ l0_res_of out = Ok k ⇒
  MEM (n2w k) (l0_used w')
Proof
  rw[sys_accept_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  ‘l0_rely (l0_tick «sys_accept» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_all l0_accept_res >> strip_tac >> gvs[l0_res_of_enc] >>
  gvs[l0_accept_def, AllCaseEqs(), fail_def, l0_alloc_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), fail_def, l0_used_def]
QED

(* One fetch step on the listener *)
Theorem fetch_accept_rel:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ l0_rely w ∧ fds_lt w ∧
  wants_input lfd hw ps lfd ∧ sys_accept lfd w = SOME (out, w1, ev) ∧
  (case l0_res_of out of
   | Ok k => (ps with acq := ps.acq ++ [n2w k], [FConn (n2w k)])
   | Fail e _ => ((if e = E_MFILE then ps with pause := pf_backoff else ps), []))
    = (ps1, fl) ∧
  arrs lfd (cm, LENGTH s.clients) fl = (as, (cm1, k1)) ∧
  (∀f. MEM (f, LENGTH s.clients) cm1 ⇒ ∀used. ¬MEM f used ⇒ s.alloc (LENGTH s.clients) used = f) ⇒
  pv_rel lfd cm1 ps1 (FOLDL deliver2 s as) ∧ pown lfd ps1 ∧ l0own lfd w1 ps1 ∧
  k1 = LENGTH (FOLDL deliver2 s as).clients ∧
  ps1.b.tbl = ps.b.tbl ∧ ps1.b.nxt = ps.b.nxt ∧ ps1.b.closing = ps.b.closing ∧
  ps1.inb = ps.inb ∧ ps1.eof = ps.eof
Proof
  strip_tac >>
  ‘ps.acq = [] ∧ ps.pause = 0’ by gvs[wants_input_def] >>
  ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)’
    by (gvs[sys_accept_def] >> drule l0_do_used >> simp[]) >>
  Cases_on ‘l0_res_of out’ >> gvs[arrs_def]
  >- (rename1 ‘l0_res_of out = Ok k’ >>
      drule_all sys_accept_fresh >> strip_tac >>
      drule_all sys_accept_adds >> strip_tac >>
      qabbrev_tac ‘f : word64 = n2w k’ >>
      ‘f ≠ lfd ∧ ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing’
        by (gvs[l0own_def] >> metis_tac[]) >>
      ‘EVERY (λj. j < LENGTH s.clients) (MAP SND cm) ∧ ALL_DISTINCT (MAP SND cm)’
        by gvs[pv_rel_def] >>
      ‘¬MEM (LENGTH s.clients) (MAP SND cm)’
        by (strip_tac >> gvs[EVERY_MEM] >> res_tac >> gvs[]) >>
      ‘cl ((f, LENGTH s.clients) :: cm) f = LENGTH s.clients’ by simp[cl_def] >>
      ‘∀g. g ≠ f ⇒ cl ((f, LENGTH s.clients) :: cm) g = cl cm g’ by simp[cl_def] >>
      simp[deliver2_def] >>
      ‘ALOOKUP s.listening lfd = SOME []’ by gvs[pv_rel_def] >>
      simp[] >> rpt conj_tac
      >- (qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >>
          simp[pv_rel_def, AFUPDKEY_def, inb_of_def] >> strip_tac >>
          gvs[AFUPDKEY_def, EL_APPEND1, EL_APPEND2, EVERY_MEM] >> rw[] >>
          TRY (simp[empty_conn_def] >> NO_TAC) >>
          TRY (res_tac >> simp[] >> NO_TAC) >>
          ‘f' ≠ f’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
          first_x_assum drule >> strip_tac >>
          ‘cl cm f' < LENGTH s.clients’
            by (simp[cl_def] >> Cases_on ‘ALOOKUP cm f'’ >> gvs[ALOOKUP_NONE] >>
                metis_tac[ALOOKUP_SOME_MEM_SND]) >>
          gvs[EL_APPEND1])
      >- (gvs[pown_def, inb_of_def, ALL_DISTINCT_APPEND] >> metis_tac[])
      >> gvs[l0own_def] >> metis_tac[]) >>
  rw[] >> gvs[l0own_def] >> metis_tac[]
QED

(* Changing one open connection's buffers is updating its client *)
Theorem pv_rel_update_client:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ ALOOKUP ps.b.tbl h = SOME f ∧
  ps1.b = ps.b ∧ ps1.acq = ps.acq ∧
  (∀g. g ≠ f ⇒ inb_of ps1 g = inb_of ps g ∧ (MEM g ps1.eof ⇔ MEM g ps.eof)) ∧
  (gc (EL (cl cm f) s.clients)).incoming = inb_of ps1 f ∧
  ((gc (EL (cl cm f) s.clients)).peer_closed ⇔ MEM f ps1.eof) ⇒
  pv_rel lfd cm ps1 (update_client (cl cm f) gc s)
Proof
  strip_tac >> drule_all cl_tbl_ne >> strip_tac >>
  ‘cl cm f < LENGTH s.clients’ by (drule_all pv_rel_tbl >> simp[]) >>
  qpat_x_assum ‘pv_rel _ _ _ _’ mp_tac >>
  simp[pv_rel_def, update_client_def, EL_LUPDATE] >> strip_tac >>
  rw[] >> gvs[] >> res_tac >> gvs[] >>
  Cases_on ‘f' = f’ >> gvs[]
QED

Theorem tbl_alookup_exists:
  ALL_DISTINCT (MAP FST tbl) ∧ MEM f (MAP SND tbl) ⇒ ∃h. ALOOKUP tbl h = SOME f
Proof
  rw[MEM_MAP] >> rename1 ‘MEM p tbl’ >> PairCases_on ‘p’ >>
  qexists_tac ‘p0’ >> irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[]
QED

(* One fetch step on a connection fd f *)
Theorem fetch_recv_rel:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ l0_rely w ∧ fds_lt w ∧
  wants_input lfd hw ps f ∧ f ≠ lfd ∧ MEM f (MAP SND ps.b.tbl) ∧
  sys_recv f pf_chunk w = SOME (out, w1, ev) ∧
  (case l0_res_of out of
   | Ok k =>
       if 0 < k then (set_inb f (TAKE k (DROP 13 out)) ps,
                      [FData f (TAKE k (DROP 13 out))])
       else (ps with eof := f :: ps.eof, [FEof f])
   | Fail e _ =>
       if l1_transient e then (ps, [])
       else (ps with eof := f :: ps.eof, [FReset f])) = (ps1, fl) ∧
  arrs lfd (cm, LENGTH s.clients) fl = (as, (cm1, k1)) ⇒
  pv_rel lfd cm1 ps1 (FOLDL deliver2 s as) ∧ pown lfd ps1 ∧ l0own lfd w1 ps1 ∧
  cm1 = cm ∧ k1 = LENGTH (FOLDL deliver2 s as).clients ∧
  ps1.b = ps.b ∧ ps1.acq = ps.acq
Proof
  strip_tac >>
  ‘∃h. ALOOKUP ps.b.tbl h = SOME f’
    by (irule tbl_alookup_exists >> gvs[pown_def]) >>
  drule_all pv_rel_tbl >> strip_tac >>
  ‘inb_of ps f = [] ∧ ¬MEM f ps.eof’ by gvs[wants_input_def] >>
  ‘l0_used w1 = l0_used w’ by (gvs[sys_recv_def] >> drule l0_do_used >> simp[]) >>
  ‘l0own lfd w1 ps1’ by (gvs[l0own_def, AllCaseEqs()] >> rw[] >> gvs[]) >>
  Cases_on ‘l0_res_of out’ >> gvs[]
  >- (Cases_on ‘0 < n’ >> gvs[arrs_def, deliver2_def] >> (rpt conj_tac
       >- (drule pv_rel_update_client >> rpt (disch_then drule) >>
           disch_then irule >> simp[] >> rw[inb_of_def] >> gvs[inb_of_def])
       >- (qpat_x_assum ‘pown _ _’ mp_tac >> simp[pown_def] >> rw[] >>
           gvs[] >> Cases_on ‘f' = f’ >> gvs[] >>
           first_x_assum irule >> fs[inb_of_def])
       >> simp[update_client_def])) >>
  Cases_on ‘l1_transient e’ >> gvs[arrs_def, deliver2_def] >> (rpt conj_tac
       >- (drule pv_rel_update_client >> rpt (disch_then drule) >>
           disch_then irule >> simp[] >> rw[inb_of_def] >> gvs[inb_of_def])
       >- (qpat_x_assum ‘pown _ _’ mp_tac >> simp[pown_def] >> rw[] >>
           gvs[] >> Cases_on ‘f' = f’ >> gvs[] >>
           first_x_assum irule >> fs[inb_of_def])
       >> simp[update_client_def])
QED


Theorem arrs_APPEND:
  ∀l1 cm k l2.
    arrs lfd (cm, k) (l1 ++ l2) =
      let (as1, (cm1, k1)) = arrs lfd (cm, k) l1;
          (as2, ck2) = arrs lfd (cm1, k1) l2 in (as1 ++ as2, ck2)
Proof
  Induct >> simp[arrs_def] >- (rw[] >> pairarg_tac >> simp[]) >>
  Cases >> rw[arrs_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem arrs_k_mono:
  ∀l cm k as cm' k'. arrs lfd (cm, k) l = (as, (cm', k')) ⇒ k ≤ k'
Proof
  Induct >> simp[arrs_def] >> Cases >> rw[arrs_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem arrs_suffix:
  ∀l cm k as cm' k'. arrs lfd (cm, k) l = (as, (cm', k')) ⇒ ∃new. cm' = new ++ cm
Proof
  Induct >> simp[arrs_def] >> Cases >> rw[arrs_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> rw[] >> metis_tac[APPEND, APPEND_ASSOC, CONS_APPEND]
QED

Theorem l0_do_rely:
  l0_rely w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒ l0_rely w'
Proof
  rw[] >> imp_res_tac l0_do_env >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]
QED

Theorem FOLDL_APP:
  ∀l1 e. FOLDL f e (l1 ++ l2) = FOLDL f (FOLDL f e l1) l2
Proof
  Induct >> simp[]
QED

Theorem FOLDL_deliver2_alloc[simp]:
  ∀as s. (FOLDL deliver2 s as).alloc = s.alloc ∧
         LENGTH s.clients ≤ LENGTH (FOLDL deliver2 s as).clients
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘deliver2 s h’ strip_assume_tac) >>
  ‘LENGTH s.clients ≤ LENGTH (deliver2 s h).clients’
    by (Cases_on ‘h’ >> rw[deliver2_def, update_client_def]) >> simp[]
QED

(* The fetched arrivals are effective (socketV2Fair's step_ok2) *)
Theorem step_ok2_APPEND:
  ∀as1 s. step_ok2 s (as1 ++ as2) ⇔ step_ok2 s as1 ∧ step_ok2 (FOLDL deliver2 s as1) as2
Proof
  Induct >> simp[step_ok2_def] >> metis_tac[]
QED

Theorem fetch_accept_ok:
  pv_rel lfd cm ps s ∧
  (case l0_res_of out of
   | Ok k => (ps with acq := ps.acq ++ [n2w k], [FConn (n2w k)])
   | Fail e _ => ((if e = E_MFILE then ps with pause := pf_backoff else ps), []))
    = (ps1, fl) ∧
  arrs lfd (cm, LENGTH s.clients) fl = (as, (cm1, k1)) ∧
  LENGTH (FOLDL deliver2 s as).clients + 1 < dimword (:64) ⇒
  step_ok2 s as
Proof
  Cases_on ‘l0_res_of out’ >> rw[] >> gvs[arrs_def, step_ok2_def, arrival_ok2_def] >>
  gvs[pv_rel_def, deliver2_def, AFUPDKEY_def]
QED

Theorem fetch_recv_ok:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧
  wants_input lfd hw ps f ∧ f ≠ lfd ∧ MEM f (MAP SND ps.b.tbl) ∧
  (case l0_res_of out of
   | Ok k =>
       if 0 < k then (set_inb f (TAKE k (DROP 13 out)) ps,
                      [FData f (TAKE k (DROP 13 out))])
       else (ps with eof := f :: ps.eof, [FEof f])
   | Fail e _ =>
       if l1_transient e then (ps, [])
       else (ps with eof := f :: ps.eof, [FReset f])) = (ps1, fl) ∧
  arrs lfd (cm, LENGTH s.clients) fl = (as, (cm1, k1)) ⇒
  step_ok2 s as
Proof
  strip_tac >>
  ‘∃h. ALOOKUP ps.b.tbl h = SOME f’
    by (irule tbl_alookup_exists >> gvs[pown_def]) >>
  drule_all pv_rel_tbl >> strip_tac >>
  ‘¬MEM f ps.eof’ by gvs[wants_input_def] >>
  Cases_on ‘l0_res_of out’ >> gvs[]
  >- (Cases_on ‘0 < n’ >> gvs[arrs_def, step_ok2_def, arrival_ok2_def]) >>
  Cases_on ‘l1_transient e’ >> gvs[arrs_def, step_ok2_def, arrival_ok2_def]
QED

val fetch_tail_tac =
  rename1 ‘pf_fetch _ _ fs (w1, ps1) = SOME ((w2, ps2), log2, evs2)’ >>
  Cases_on ‘arrs lfd (cm, LENGTH s.clients) fl’ >> rename1 ‘_ = (as1, ck1)’ >>
  PairCases_on ‘ck1’ >>
  Cases_on ‘arrs lfd (ck10, ck11) log2’ >> rename1 ‘_ = (as2, ck2)’ >>
  PairCases_on ‘ck2’ >>
  qpat_x_assum ‘arrs _ _ (_ ++ _) = _’ mp_tac >> simp[arrs_APPEND] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_assum ‘arrs _ (ck10, ck11) _ = _’ (strip_assume_tac o MATCH_MP arrs_suffix) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ‘∀g. MEM (g, LENGTH s.clients) ck10 ⇒
       ∀used. ¬MEM g used ⇒ s.alloc (LENGTH s.clients) used = g’
    by (rw[] >> qpat_assum ‘∀f j. _’ irule >> simp[]);

Theorem fetch_rel:
  ∀fs w ps cm s w' ps' log evs as cm' k'.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    arrs lfd (cm, LENGTH s.clients) log = (as, (cm', k')) ∧
    pv_rel lfd cm ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ l0_rely w ∧ fds_lt w ∧
    (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND ps.b.tbl)) ∧
    (∀f j. MEM (f, j) cm' ∧ LENGTH s.clients ≤ j ⇒
           ∀used. ¬MEM f used ⇒ s.alloc j used = f) ∧
    k' + 1 < dimword (:64) ⇒
    step_ok2 s as ∧
    pv_rel lfd cm' ps' (FOLDL deliver2 s as) ∧ pown lfd ps' ∧ l0own lfd w' ps' ∧
    l0_rely w' ∧ fds_lt w' ∧ k' = LENGTH (FOLDL deliver2 s as).clients ∧
    ps'.b.tbl = ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt ∧ ps'.b.closing = ps.b.closing
Proof
  Induct >- simp[pf_fetch_def, arrs_def, step_ok2_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl)’ >>
      Cases_on ‘pf_fetch lfd hw fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
      PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
      fetch_tail_tac >>
      ‘l0_rely w1’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule_all l0_do_rely >> simp[]) >>
      ‘fds_lt w1’ by (drule_all sys_accept_fds_lt >> simp[]) >>
      qpat_assum ‘arrs _ (ck10, ck11) _ = _’ (assume_tac o MATCH_MP arrs_k_mono) >>
      drule_all fetch_accept_rel >> strip_tac >>
      ‘step_ok2 s as1’
        by (irule fetch_accept_ok >> gvs[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘ck10’, ‘FOLDL deliver2 s as1’,
                                   ‘w2’, ‘ps2’, ‘log2’, ‘evs2’, ‘as2’, ‘new ++ ck10’, ‘ck21’] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (gvs[] >> NO_TAC)
          >> FIRST [rw[] >> qpat_assum ‘∀f j. _’ irule >> simp[] >>
                  irule LESS_EQ_TRANS >>
                  qexists_tac ‘LENGTH (FOLDL deliver2 s as1).clients’ >> simp[],
                  rw[] >> gvs[] >> metis_tac[]]) >>
      strip_tac >> gvs[FOLDL_APP, step_ok2_APPEND]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl)’ >>
  Cases_on ‘pf_fetch lfd hw fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  fetch_tail_tac >>
  ‘l0_rely w1’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        drule_all l0_do_rely >> simp[]) >>
  ‘l0_used w1 = l0_used w ∧ w1.fd_limit = w.fd_limit’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        imp_res_tac l0_do_env >> drule l0_do_used >> simp[]) >>
  ‘fds_lt w1’ by gvs[fds_lt_def] >>
  ‘MEM f (MAP SND ps.b.tbl)’
    by (qpat_x_assum ‘∀f'. f' = f ∨ _ ⇒ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
  drule_all fetch_recv_rel >> strip_tac >>
  ‘step_ok2 s as1’ by (irule fetch_recv_ok >> gvs[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘ck10’, ‘FOLDL deliver2 s as1’,
                               ‘w2’, ‘ps2’, ‘log2’, ‘evs2’, ‘as2’, ‘new ++ ck10’, ‘ck21’] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (gvs[] >> NO_TAC)
      >> FIRST [rw[] >> qpat_assum ‘∀f j. _’ irule >> simp[] >>
                  irule LESS_EQ_TRANS >>
                  qexists_tac ‘LENGTH (FOLDL deliver2 s as1).clients’ >> simp[],
                  rw[] >> gvs[] >> metis_tac[]]) >>
  strip_tac >> gvs[FOLDL_APP, step_ok2_APPEND]
QED

(* ------------------------------------------------------------------------
   The poll, the flush and the reap
   ------------------------------------------------------------------------ *)

Theorem l1_polls_l0:
  ∀fess w rv w' evs.
    l1_polls fess w = SOME (rv, w', evs) ∧ l0_rely w ⇒
    l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧ l0_rely w'
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> gvs[sys_poll_def] >>
  imp_res_tac l0_do_env >> imp_res_tac l0_do_used >> imp_res_tac l0_do_rely >>
  first_x_assum drule_all >> simp[]
QED

Theorem after_send_b:
  (after_send f r b).tbl = b.tbl ∧ (after_send f r b).nxt = b.nxt ∧
  (after_send f r b).closing = b.closing
Proof
  Cases_on ‘r’ >> rw[after_send_def, set_outbox_def]
QED

Theorem l1_flush_l0:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒
    l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧ l0_rely w' ∧
    b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧ b'.closing = b.closing
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[sys_send_def] >>
  imp_res_tac l0_do_env >> imp_res_tac l0_do_used >> imp_res_tac l0_do_rely >>
  first_x_assum drule_all >> simp[after_send_b]
QED

Theorem close_used_sub:
  l0_close f w = (r, w') ⇒ ∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)
Proof
  rw[l0_close_def, close_fd_def, AllCaseEqs()] >> gvs[] >>
  gvs[l0_used_def, MEM_FST_ADELKEY, MEM_FILTER, MEM_MAP, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem sys_close_used_sub:
  sys_close f w = SOME (out, w', ev) ⇒ ∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)
Proof
  rw[sys_close_def, l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  imp_res_tac close_used_sub >> gvs[]
QED

Theorem MEM_SND_ADELKEY_sub:
  MEM g (MAP SND (ADELKEY k l)) ⇒ MEM g (MAP SND l)
Proof
  simp[ADELKEY_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem l1_close_l0:
  l1_close f (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒
  (∀g. g ≠ f ∧ MEM g (l0_used w) ⇒ MEM g (l0_used w')) ∧
  (∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)) ∧
  w'.fd_limit = w.fd_limit ∧ l0_rely w' ∧
  b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧ b'.closing = FILTER ($≠ f) b.closing
Proof
  rw[l1_close_def, AllCaseEqs()] >> imp_res_tac sys_close_used_sub >>
  gvs[sys_close_def, forget_def, set_outbox_def] >>
  imp_res_tac l0_do_env >> imp_res_tac l0_do_used >> imp_res_tac l0_do_rely >> gvs[]
QED

Theorem l1_reap_l0:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒
    (∀g. MEM g (l0_used w) ∧ ¬MEM g fs ⇒ MEM g (l0_used w')) ∧
    (∀g. MEM g b'.closing ⇒ MEM g b.closing ∧ (MEM g (l0_used w) ⇒ MEM g (l0_used w'))) ∧
    (∃P. b'.closing = FILTER P b.closing) ∧
    (∀g. MEM g (l0_used w') ⇒ MEM g (l0_used w)) ∧
    w'.fd_limit = w.fd_limit ∧ l0_rely w' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt
Proof
  Induct >> simp[l1_reap_def]
  >- (rw[] >> qexists_tac ‘K T’ >> simp[FILTER_T, combinTheory.K_DEF]) >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (rename1 ‘l1_close h (w, b) = SOME (ws, _)’ >> PairCases_on ‘ws’ >>
       rename1 ‘l1_close h (w, b) = SOME ((w1, b1), evs1)’ >>
       drule_all l1_close_l0 >> strip_tac >>
       first_x_assum drule_all >> strip_tac >> gvs[] >>
       conj_tac >- (rw[] >> gvs[MEM_FILTER] >> metis_tac[MEM_FILTER]) >>
       qexists_tac ‘λx. h ≠ x ∧ P x’ >>
       simp[rich_listTheory.FILTER_FILTER] >>
       AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem l1do_write_l0:
  l1do lfd (w, b) (Write h bs) = SOME (r, (w', b'), evs) ∧ l0_rely w ⇒
  l0_used w' = l0_used w ∧ w'.fd_limit = w.fd_limit ∧ l0_rely w'
Proof
  rw[l1do_def, AllCaseEqs()] >> gvs[sys_send_def] >>
  imp_res_tac l0_do_env >> imp_res_tac l0_do_used >> imp_res_tac l0_do_rely >> gvs[]
QED

Theorem read_close_l0:
  ALOOKUP ps.b.tbl c = SOME f ∧
  l1_close f (w, ps.b with tbl := ADELKEY c ps.b.tbl) = SOME ((w', b'), evs) ∧
  l0_rely w ∧ fds_lt w ∧ l0own lfd w ps ∧ pown lfd ps ⇒
  l0_rely w' ∧ fds_lt w' ∧ l0own lfd w' (ps with <| b := b'; eof := X |>)
Proof
  strip_tac >> drule_all l1_close_l0 >> strip_tac >>
  ‘ALL_DISTINCT (MAP FST ps.b.tbl) ∧ ALL_DISTINCT (MAP SND ps.b.tbl) ∧
   f ≠ lfd ∧ ¬MEM f ps.b.closing ∧ ¬MEM f ps.acq’
    by (‘MEM f (MAP SND ps.b.tbl)’ by metis_tac[ALOOKUP_SOME_MEM_SND] >>
        gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  gvs[fds_lt_def, l0own_def, MEM_FILTER] >> rw[] >>
  qpat_x_assum ‘∀g. g ≠ f ∧ _ ⇒ _’ irule >> metis_tac[MEM_SND_ADELKEY]
QED

(* The actions keep the L0-side invariants *)
Theorem pdo_l0:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧
  l0_rely w ∧ fds_lt w ∧ l0own lfd w ps ∧ pown lfd ps ⇒
  l0_rely w' ∧ fds_lt w' ∧ l0own lfd w' ps'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- (gvs[AllCaseEqs()] >> gvs[l0own_def] >> metis_tac[])
  >- (gvs[AllCaseEqs()] >>
      TRY (PairCases_on ‘z’ >> gvs[] >> drule_all read_close_l0 >> simp[] >> NO_TAC) >>
      gvs[l0own_def] >> rw[] >> first_x_assum irule >>
      metis_tac[MEM_SND_ADELKEY_sub, ALOOKUP_SOME_MEM_SND])
  >> pairarg_tac >> gvs[] >> rename1 ‘l1do _ _ _ = SOME (r, (w', b'), evs)’ >>
  drule_all l1do_write_l0 >> drule l1do_write_tbl >> rw[] >>
  gvs[fds_lt_def, l0own_def] >> metis_tac[]
QED

Theorem pacts_l0:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
    l0_rely w ∧ fds_lt w ∧ l0own lfd w ps ∧ pv_rel lfd cm ps s ∧ pown lfd ps ⇒
    l0_rely w' ∧ fds_lt w' ∧ l0own lfd w' ps'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all pdo_l0 >> strip_tac >> drule_all pdo_hdo >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The snapshot: the handle layer's ready handles are L1's
   ------------------------------------------------------------------------ *)

Theorem in_fds_poll_set:
  MEM f (in_fds (pf_poll_set lfd hw ps hs)) ⇒
  f = lfd ∨ MEM f (MAP SND ps.b.tbl)
Proof
  simp[in_fds_def, pf_poll_set_def, MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_FLAT] >>
  rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
  Cases_on ‘ALOOKUP ps.b.tbl h’ >> gvs[]
  >- (Cases_on ‘h = lfd ∧ wants_input lfd hw ps lfd’ >> gvs[]) >>
  rename1 ‘ALOOKUP _ h = SOME g’ >>
  Cases_on ‘wants_input lfd hw ps g’ >> Cases_on ‘outbox_of ps.b g = []’ >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[]
QED

Theorem pv_rel_future[simp]:
  pv_rel lfd cm ps (s with future := x) ⇔ pv_rel lfd cm ps s
Proof
  simp[pv_rel_def]
QED

Theorem FOLDL_deliver2_future:
  ∀as s. FOLDL deliver2 (s with future := x) as = (FOLDL deliver2 s as) with future := x
Proof
  Induct >> simp[] >> rpt gen_tac >>
  ‘deliver2 (s with future := x) h = (deliver2 s h) with future := x’
    by (Cases_on ‘h’ >> rw[deliver2_def, update_client_def]) >>
  simp[]
QED

Theorem filter_cong:
  ∀l. (∀x. MEM x l ⇒ (P x ⇔ Q x)) ⇒ FILTER P l = FILTER Q l
Proof
  Induct >> rw[] >> gvs[]
QED

Theorem is_ready2_lfd:
  pv_rel lfd cm ps s ∧ pown lfd ps ⇒ (is_ready2 s lfd ⇔ ps.acq ≠ [])
Proof
  strip_tac >>
  ‘ALOOKUP s.open_fds lfd = NONE’
    by (gvs[pv_rel_def, pown_def, ALOOKUP_NONE] >> metis_tac[]) >>
  gvs[is_ready2_def, client_of_def, pv_rel_def]
QED

Theorem is_ready2_tbl:
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ ALOOKUP ps.b.tbl h = SOME f ⇒
  (is_ready2 s f ⇔ inb_of ps f ≠ [] ∨ MEM f ps.eof)
Proof
  strip_tac >> drule_all pv_rel_tbl >> strip_tac >>
  ‘f ≠ lfd’ by (gvs[pown_def] >> metis_tac[ALOOKUP_SOME_MEM_SND]) >>
  ‘ALOOKUP s.listening f = NONE’ by gvs[pv_rel_def] >>
  simp[is_ready2_def]
QED

Theorem hpoll_fds_mem:
  MEM h hs ⇒
  (ALOOKUP hz.tbl h = SOME f ⇒ MEM f (hpoll_fds lfd hz hs)) ∧
  (ALOOKUP hz.tbl lfd = NONE ∧ h = lfd ⇒ MEM lfd (hpoll_fds lfd hz hs))
Proof
  rw[hpoll_fds_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists_tac ‘h’ >> simp[]
QED

Theorem ready_eq:
  pv_rel lfd cm ps s ∧ pown lfd ps ⇒
  hready lfd (hs_of ps) (FILTER (is_ready2 s) (hpoll_fds lfd (hs_of ps) hs)) hs =
  pf_ready lfd ps hs
Proof
  strip_tac >> simp[hready_def, pf_ready_def, hs_of_def] >>
  irule filter_cong >> rpt strip_tac >>
  Cases_on ‘ALOOKUP ps.b.tbl x’ >> simp[MEM_FILTER]
  >- (Cases_on ‘x = lfd’ >> simp[] >>
      drule_all is_ready2_lfd >> simp[] >> strip_tac >>
      simp[hpoll_fds_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      eq_tac >> rw[] >> qexists_tac ‘lfd’ >> gvs[]) >>
  drule_all is_ready2_tbl >> simp[] >> strip_tac >>
  simp[hpoll_fds_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  eq_tac >> rw[] >> gvs[] >> qexists_tac ‘x’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The round's tail: L1's poll, flush, fetch and reap are the handle
   layer's poll, whose step of the schedule is what L1 fetched
   ------------------------------------------------------------------------ *)

Theorem pown_closing_filter:
  pown lfd ps ∧ b'.tbl = ps.b.tbl ∧ b'.nxt = ps.b.nxt ∧
  b'.closing = FILTER P ps.b.closing ⇒ pown lfd (ps with b := b')
Proof
  rw[pown_def, inb_of_def] >>
  gvs[ALL_DISTINCT_APPEND, MEM_FILTER, FILTER_ALL_DISTINCT] >> metis_tac[]
QED

Theorem tail_rel:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ l0_rely w ∧ fds_lt w ∧
  arrs lfd (cm, LENGTH s.clients) log = (as, (cm', k')) ∧
  (∀f j. MEM (f, j) cm' ∧ LENGTH s.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s.alloc j used = f) ∧
  LHD s.future = SOME as ∧ k' + 1 < dimword (:64) ⇒
  step_ok2 s as ∧
  ∃s'. hpoll lfd (hs_of ps) hs s = (rdy, s') ∧
       pv_rel lfd cm' ps' s' ∧ pown lfd ps' ∧ l0own lfd w' ps' ∧ l0_rely w' ∧
       fds_lt w' ∧ hs_of ps' = hs_of ps ∧ k' = LENGTH s'.clients ∧
       s'.alloc = s.alloc ∧ s'.future = THE (LTL s.future)
Proof
  simp[pf_tail_def] >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw ps hs’ >>
  Cases_on ‘l1_polls (poll_chunks fes) w’ >> gvs[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘l1_polls _ _ = SOME (rv, w1, pevs)’ >> gvs[] >>
  Cases_on ‘l1_flush (writable_fds rv) (w1, ps.b)’ >> gvs[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >> gvs[] >>
  qmatch_asmsub_abbrev_tac ‘pf_fetch _ _ fs (w2, ps2)’ >>
  Cases_on ‘pf_fetch lfd hw fs (w2, ps2)’ >> gvs[] >> rename1 ‘_ = SOME z’ >>
  PairCases_on ‘z’ >> rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3f), log3, gevs)’ >> gvs[] >>
  qabbrev_tac ‘ps3 = hup_step (hup_fds rv) (outbox_of ps.b) log3 ps3f’ >>
  ‘ps3f.b.closing = ps3.b.closing ∧ ps3f.pause = ps3.pause’ by simp[Abbr ‘ps3’] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  Cases_on ‘l1_reap ps3.b.closing (w3, ps3.b)’ >> gvs[] >> rename1 ‘_ = SOME u’ >>
  PairCases_on ‘u’ >> rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >> gvs[] >>
  drule_all l1_polls_l0 >> strip_tac >>
  drule_all l1_flush_l0 >> strip_tac >>
  ‘pv_rel lfd cm ps2 s ∧ pown lfd ps2 ∧ l0own lfd w2 ps2 ∧ fds_lt w2’
    by (simp[Abbr ‘ps2’, pv_rel_b, pown_b] >> gvs[l0own_def, fds_lt_def] >> metis_tac[]) >>
  ‘∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND ps2.b.tbl)’
    by (simp[Abbr ‘fs’, Abbr ‘ps2’, MEM_FILTER] >> rw[] >>
        gvs[Abbr ‘fes’] >> drule in_fds_poll_set >> simp[]) >>
  ‘l0_rely w2’ by simp[] >>
  ‘k' + 1 < dimword (:64)’ by simp[] >>
  drule_all fetch_rel >> strip_tac >>
  ‘pv_rel lfd cm' ps3 (FOLDL deliver2 s as) ∧ pown lfd ps3 ∧ l0own lfd w3 ps3 ∧
   ps3.b.tbl = ps3f.b.tbl ∧ ps3.b.nxt = ps3f.b.nxt ∧ ps3.b.closing = ps3f.b.closing ∧
   ps3.pause = ps3f.pause’ by simp[Abbr ‘ps3’] >>
  drule_all l1_reap_l0 >> strip_tac >>
  ‘pown lfd (ps3 with b := b4)’ by (irule pown_closing_filter >> simp[] >> metis_tac[]) >>
  ‘pv_rel lfd cm' (ps3 with b := b4) (FOLDL deliver2 s as)’ by simp[pv_rel_b] >>
  simp[hpoll_def, sock_poll2_def, tick2_def, FOLDL_deliver2_future] >>
  ‘hs_of (ps3 with b := b4) = hs_of ps’ by gvs[hs_of_def, Abbr ‘ps2’] >>
  ‘ps3 with <| b := b4; pause := ps3f.pause − 1 |> =
   (ps3 with b := b4) with pause := ps3f.pause − 1’ by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[] >> rpt conj_tac
  >- (qpat_x_assum ‘hs_of _ = hs_of ps’ (SUBST1_TAC o SYM) >>
      irule ready_eq >> simp[] >> qexists_tac ‘cm'’ >> simp[])
  >- (‘∀g. g = lfd ∨ MEM g (MAP SND ps3.b.tbl) ∨ MEM g ps3.acq ⇒
           ¬MEM g ps3.b.closing’ by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
      gvs[l0own_def] >> metis_tac[])
  >> gvs[fds_lt_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem hdo_world:
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ⇒
  s'.future = s.future ∧ s'.alloc = s.alloc ∧ LENGTH s'.clients = LENGTH s.clients
Proof
  Cases_on ‘a’ >>
  rw[hdo_def, sock_accept2_def, sock_read2_def, sock_write2_def, sock_close2_def,
     update_client_def, AllCaseEqs()] >> gvs[]
QED

Theorem hacts_world:
  ∀acts s hs rs evs s' hs'.
    hacts lfd (s, hs) acts = SOME (rs, evs, (s', hs')) ⇒
    s'.future = s.future ∧ s'.alloc = s.alloc ∧ LENGTH s'.clients = LENGTH s.clients
Proof
  Induct >> simp[hacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘hdo _ _ _ = SOME (r1, st1, evs1)’ >> PairCases_on ‘st1’ >>
  drule hdo_world >> first_x_assum drule >> simp[]
QED

Theorem round_rel:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ l0own lfd w ps ∧ l0_rely w ∧ fds_lt w ∧
  arrs lfd (cm, LENGTH s.clients) log = (as, (cm', k')) ∧
  (∀f j. MEM (f, j) cm' ∧ LENGTH s.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s.alloc j used = f) ∧
  LHD s.future = SOME as ∧ k' + 1 < dimword (:64) ⇒
  ∃rs hevs s1 s2.
    hacts lfd (s, hs_of ps) acts = SOME (rs, hevs, (s1, hs_of ps')) ∧
    snap = ssnap (FST (hpoll lfd (hs_of ps') hs s1)) rs ∧
    SND (hpoll lfd (hs_of ps') hs s1) = s2 ∧
    pv_rel lfd cm' ps' s2 ∧ pown lfd ps' ∧ l0own lfd w' ps' ∧ l0_rely w' ∧
    fds_lt w' ∧ k' = LENGTH s2.clients ∧ s2.alloc = s.alloc ∧
    s2.future = THE (LTL s.future) ∧ step_ok2 s1 as
Proof
  simp[pround_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, ws1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, (w1, ps1))’ >>
  rename1 ‘pf_tail _ _ _ _ = SOME (rdy, _, _, tevs)’ >>
  drule_all pacts_hacts >> strip_tac >>
  drule_all pacts_l0 >> strip_tac >>
  drule hacts_world >> strip_tac >>
  ‘LHD s'.future = SOME as’ by simp[] >>
  ‘∀f j. MEM (f, j) cm' ∧ LENGTH s'.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s'.alloc j used = f’ by gvs[] >>
  ‘arrs lfd (cm, LENGTH s'.clients) log = (as, (cm', k'))’ by gvs[] >>
  ‘k' + 1 < dimword (:64)’ by simp[] >>
  drule_all tail_rel >> strip_tac >>
  qexistsl_tac [‘rs’, ‘hevs’, ‘s'’] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The version-2 world built from L1's run
   ------------------------------------------------------------------------ *)

(* What round n fetched *)
Definition plog_def:
  plog lfd hw ifds m w0 n =
    case prounds lfd hw ifds m (w0, pinit) (SUC n) of
    | SOME (_, _, _, logs) => EL n logs
    | NONE => []
End

(* The client map and count before round n *)
Definition pcm_def:
  pcm lfd hw ifds m w0 0 = ([], 0) ∧
  pcm lfd hw ifds m w0 (SUC n) =
    SND (arrs lfd (pcm lfd hw ifds m w0 n) (plog lfd hw ifds m w0 n))
End

(* The arrivals of round n's step of the schedule *)
Definition parr_def:
  parr lfd hw ifds m w0 n =
    FST (arrs lfd (pcm lfd hw ifds m w0 n) (plog lfd hw ifds m w0 n))
End

(* The kernel's fd for client j: free, it is the fd of the world's choice;
   otherwise (never in the run) the lowest free fd *)
Definition run_alloc_def:
  run_alloc lfd hw ifds m w0 (j : num) (used : word64 list) =
    if ∃n f. MEM (f, j) (FST (pcm lfd hw ifds m w0 n)) then
      let f = @f. ∃n. MEM (f, j) (FST (pcm lfd hw ifds m w0 n)) in
        if MEM f used then lowest_free used else f
    else lowest_free used
End

(* The version-2 world *)
Definition psk_def:
  psk lfd hw ifds m w0 =
    <| listening := [(lfd, [])]; clients := []; open_fds := []; reserved := [];
       alloc := run_alloc lfd hw ifds m w0;
       future := LGENLIST (parr lfd hw ifds m w0) NONE |>
End

Theorem prounds_logs:
  ∀n h ws evs logs.
    prounds lfd hw ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
    LENGTH logs = n ∧
    ∀k. k ≤ n ⇒ ∃h' ws' evs'. prounds lfd hw ifds m ws0 k = SOME (h', ws', evs', TAKE k logs)
Proof
  Induct >> simp[prounds_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rw[] >>
  Cases_on ‘k = SUC (LENGTH logs')’
  >- (gvs[prounds_def] >> simp[TAKE_LENGTH_ID_rwt]) >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >> strip_tac >>
  simp[TAKE_APPEND1]
QED

Theorem plog_EL:
  prounds lfd hw ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ∧ k < n ⇒
  plog lfd hw ifds m w0 k = EL k logs
Proof
  rw[plog_def] >> drule prounds_logs >> strip_tac >>
  first_x_assum (qspec_then ‘SUC k’ mp_tac) >> simp[] >> strip_tac >>
  simp[EL_TAKE]
QED

Theorem arrs_inv:
  ∀l cm k as cm' k'.
    arrs lfd (cm, k) l = (as, (cm', k')) ∧
    ALL_DISTINCT (MAP SND cm) ∧ EVERY (λj. j < k) (MAP SND cm) ⇒
    ALL_DISTINCT (MAP SND cm') ∧ EVERY (λj. j < k') (MAP SND cm') ∧ k ≤ k' ∧
    ∃new. cm' = new ++ cm ∧ EVERY (λj. k ≤ j) (MAP SND new)
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  first_x_assum drule >>
  impl_tac
  >- (simp[] >> fs[EVERY_MEM] >> rw[]
      >- (strip_tac >> res_tac >> fs[])
      >> res_tac >> simp[]) >>
  strip_tac >> gvs[] >>
  conj_tac >- (REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> first_assum ACCEPT_TAC) >>
  fs[EVERY_MEM] >> rw[] >> res_tac >> simp[]
QED

Theorem pcm_inv:
  ∀n. ALL_DISTINCT (MAP SND (FST (pcm lfd hw ifds m w0 n))) ∧
      EVERY (λj. j < SND (pcm lfd hw ifds m w0 n)) (MAP SND (FST (pcm lfd hw ifds m w0 n)))
Proof
  Induct >> simp[pcm_def] >>
  Cases_on ‘pcm lfd hw ifds m w0 n’ >> gvs[] >>
  Cases_on ‘arrs lfd (q, r) (plog lfd hw ifds m w0 n)’ >> rename1 ‘_ = (as, ck)’ >>
  PairCases_on ‘ck’ >> drule_all arrs_inv >> simp[]
QED

Theorem pcm_step:
  ∀n. ∃new'. FST (pcm lfd hw ifds m w0 (SUC n)) = new' ++ FST (pcm lfd hw ifds m w0 n)
Proof
  gen_tac >> simp[pcm_def] >>
  Cases_on ‘pcm lfd hw ifds m w0 n’ >> simp[] >>
  Cases_on ‘arrs lfd (q, r) (plog lfd hw ifds m w0 n)’ >> rename1 ‘_ = (as, ck)’ >>
  PairCases_on ‘ck’ >> simp[] >> drule arrs_suffix >> simp[]
QED

Theorem pcm_mono:
  ∀d n. ∃new. FST (pcm lfd hw ifds m w0 (n + d)) = new ++ FST (pcm lfd hw ifds m w0 n)
Proof
  Induct >> simp[] >> gen_tac >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  qspecl_then [‘n + d’] strip_assume_tac pcm_step >>
  qexists_tac ‘new' ++ new’ >>
  ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> ASM_REWRITE_TAC[]
QED

Theorem snd_unique:
  ∀l f g j. ALL_DISTINCT (MAP SND l) ∧ MEM (f, j) l ∧ MEM (g, j) l ⇒ f = g
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP] >> metis_tac[SND]
QED

Theorem pcm_unique:
  MEM (f, j) (FST (pcm lfd hw ifds m w0 n)) ∧
  MEM (g, j) (FST (pcm lfd hw ifds m w0 n')) ⇒ f = g
Proof
  strip_tac >>
  Cases_on ‘n ≤ n'’
  >- (‘∃d. n' = n + d’ by (qexists_tac ‘n' - n’ >> simp[]) >>
      qspecl_then [‘d’, ‘n’] strip_assume_tac pcm_mono >>
      ‘ALL_DISTINCT (MAP SND (FST (pcm lfd hw ifds m w0 (n + d))))’ by simp[pcm_inv] >>
      ‘MEM (f, j) (FST (pcm lfd hw ifds m w0 (n + d)))’ by gvs[] >>
      ‘MEM (g, j) (FST (pcm lfd hw ifds m w0 (n + d)))’ by gvs[] >>
      qspecl_then [‘FST (pcm lfd hw ifds m w0 (n + d))’, ‘f’, ‘g’, ‘j’] mp_tac snd_unique >>
      simp[]) >>
  ‘∃d. n = n' + d’ by (qexists_tac ‘n - n'’ >> simp[]) >>
  qspecl_then [‘d’, ‘n'’] strip_assume_tac pcm_mono >>
  ‘ALL_DISTINCT (MAP SND (FST (pcm lfd hw ifds m w0 (n' + d))))’ by simp[pcm_inv] >>
  ‘MEM (f, j) (FST (pcm lfd hw ifds m w0 (n' + d)))’ by gvs[] >>
  ‘MEM (g, j) (FST (pcm lfd hw ifds m w0 (n' + d)))’ by gvs[] >>
  qspecl_then [‘FST (pcm lfd hw ifds m w0 (n' + d))’, ‘f’, ‘g’, ‘j’] mp_tac snd_unique >>
  simp[]
QED

Theorem run_alloc_eq:
  MEM (f, j) (FST (pcm lfd hw ifds m w0 n)) ∧ ¬MEM f used ⇒
  run_alloc lfd hw ifds m w0 j used = f
Proof
  strip_tac >>
  ‘(@g. ∃n. MEM (g, j) (FST (pcm lfd hw ifds m w0 n))) = f’
    by (SELECT_ELIM_TAC >> metis_tac[pcm_unique]) >>
  rw[run_alloc_def] >> metis_tac[]
QED

Theorem run_alloc_ok:
  alloc_ok (run_alloc lfd hw ifds m w0)
Proof
  rw[alloc_ok_def] >>
  ‘¬MEM (lowest_free used) used’
    by (mp_tac (Q.INST [‘l’ |-> ‘used’] lowest_n_bound) >> simp[lowest_free_def]) >>
  rw[run_alloc_def]
QED

(* ------------------------------------------------------------------------
   R1-safe: the run
   ------------------------------------------------------------------------ *)

(* One round of the handle layer's run, unfolded *)
Theorem hround_step:
  hacts_tot lfd (hst lfd ifds m s0 n) (hacts_of lfd ifds m s0 n) = (rs, evs, (s1, hs1)) ⇒
  hhist lfd ifds m s0 (SUC n) =
    hhist lfd ifds m s0 n ++
      [ssnap (FST (hpoll lfd hs1 (ifds (hhist lfd ifds m s0 n)) s1)) rs] ∧
  hst lfd ifds m s0 (SUC n) = (SND (hpoll lfd hs1 (ifds (hhist lfd ifds m s0 n)) s1), hs1)
Proof
  strip_tac >>
  ONCE_REWRITE_TAC[hhist_def, hst_def] >>
  REWRITE_TAC[hrounds_SUC] >>
  simp[GSYM hhist_def, GSYM hst_def]
QED

(* MAIN (R1-safe): in ANY L0 world, the prefetching L1 running the
   computation m has exactly the history of close-v2's handle layer running
   m in the version-2 world psk built from L1's own run, round by round; the
   relation pv_rel (L1's buffers are the world's state) and the invariants
   hold throughout *)
(* As l1pf_refines_hl, with the bound on the client count only for the
   rounds up to N (for a run looked at up to round N) *)
Theorem l1pf_refines_hl_upto:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ N ⇒ SND (pcm lfd hw ifds m w0 n') + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    n ≤ N ∧ prounds lfd hw ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ⇒
    hhist lfd ifds m (psk lfd hw ifds m w0) n = h ∧
    SND (hst lfd ifds m (psk lfd hw ifds m w0) n) = hs_of (SND ws) ∧
    pv_rel lfd (FST (pcm lfd hw ifds m w0 n)) (SND ws)
      (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)) ∧
    LENGTH (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)).clients =
      SND (pcm lfd hw ifds m w0 n) ∧
    (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)).alloc = run_alloc lfd hw ifds m w0 ∧
    (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)).future =
      LGENLIST (λi. parr lfd hw ifds m w0 (n + i)) NONE ∧
    pown lfd (SND ws) ∧ l0own lfd (FST ws) (SND ws) ∧
    l0_rely (FST ws) ∧ fds_lt (FST ws)
Proof
  strip_tac >> Induct
  >- (simp[prounds_def, hhist_def, hst_def, hrounds_def, pcm_def, psk_def] >>
      rw[] >> simp[hs_of_def, pinit_def, l1init_def, hinit_def, pv_rel_def,
                   pown_def, l0own_def, inb_of_def] >>
      AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘prounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [prounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘prounds _ _ _ _ _ n = SOME (h0, ws0, evs0, logs0)’ >>
  rename1 ‘pround _ _ _ _ _ = SOME (snap, ws1, log, revs)’ >>
  ‘n ≤ N’ by simp[] >>
  first_x_assum drule_all >> strip_tac >>
  ‘hacts_of lfd ifds m (psk lfd hw ifds m w0) n = new_actions (log_of m) h0’
    by simp[hacts_of_def] >>
  PairCases_on ‘ws0’ >> rename1 ‘prounds _ _ _ _ _ n = SOME (h0, (w, ps), evs0, logs0)’ >>
  PairCases_on ‘ws1’ >> rename1 ‘pround _ _ _ _ _ = SOME (snap, (w', ps'), log, revs)’ >>
  gvs[] >>
  Cases_on ‘hst lfd ifds m (psk lfd hw ifds m w0) n’ >> rename1 ‘_ = (s, hs)’ >> gvs[] >>
  ‘plog lfd hw ifds m w0 n = log’
    by (drule prounds_logs >> strip_tac >>
        qpat_x_assum ‘prounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule plog_EL >> disch_then (qspec_then ‘n’ mp_tac) >>
        simp[EL_APPEND2]) >>
  Cases_on ‘pcm lfd hw ifds m w0 n’ >> rename1 ‘pcm _ _ _ _ _ n = (cm, k)’ >> gvs[] >>
  Cases_on ‘arrs lfd (cm, LENGTH s.clients) (plog lfd hw ifds m w0 n)’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >>
  ‘pcm lfd hw ifds m w0 (SUC n) = (ck0, ck1) ∧ parr lfd hw ifds m w0 n = as’
    by simp[pcm_def, parr_def] >>
  ‘∀f j. MEM (f, j) ck0 ∧ LENGTH s.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s.alloc j used = f’
    by (rw[] >> irule run_alloc_eq >> simp[] >> qexists_tac ‘SUC n’ >> simp[]) >>
  ‘LHD s.future = SOME as’ by simp[] >>
  ‘ck1 + 1 < dimword (:64)’
    by (qpat_assum ‘∀n'. _ ≤ N ⇒ SND (pcm _ _ _ _ _ n') + 1 < _’ (mp_tac o Q.SPEC ‘SUC n’) >>
        qpat_assum ‘pcm _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        simp[]) >>
  drule_all round_rel >> strip_tac >>
  ‘hacts_tot lfd (hst lfd ifds m (psk lfd hw ifds m w0) n)
     (hacts_of lfd ifds m (psk lfd hw ifds m w0) n) = (rs, hevs, (s1, hs_of ps'))’
    by simp[hacts_tot_def] >>
  drule hround_step >> strip_tac >> simp[] >>
  gvs[] >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, ADD_CLAUSES]
QED

Theorem l1pf_refines_hl:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    prounds lfd hw ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ⇒
    hhist lfd ifds m (psk lfd hw ifds m w0) n = h ∧
    SND (hst lfd ifds m (psk lfd hw ifds m w0) n) = hs_of (SND ws) ∧
    pv_rel lfd (FST (pcm lfd hw ifds m w0 n)) (SND ws)
      (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)) ∧
    LENGTH (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)).clients =
      SND (pcm lfd hw ifds m w0 n) ∧
    (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)).alloc = run_alloc lfd hw ifds m w0 ∧
    (FST (hst lfd ifds m (psk lfd hw ifds m w0) n)).future =
      LGENLIST (λi. parr lfd hw ifds m w0 (n + i)) NONE ∧
    pown lfd (SND ws) ∧ l0own lfd (FST ws) (SND ws) ∧
    l0_rely (FST ws) ∧ fds_lt (FST ws)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPEC ‘n’ (Q.GEN ‘N’ l1pf_refines_hl_upto)) >>
  impl_tac >- fs[] >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The world is well formed: alloc_ok and sched_wf2

   sched_wf2 is about the world LEFT ALONE (ticks2).  It agrees with the
   handle layer's world on all that step_ok2 reads (the listeners, the
   counts, which clients have closed, the future), because the program's
   actions change none of these.
   ------------------------------------------------------------------------ *)

Definition wagree_def:
  wagree (s : sockets2) (t : sockets2) ⇔
    MAP FST s.listening = MAP FST t.listening ∧
    LENGTH s.reserved = LENGTH t.reserved ∧
    MAP (λc. c.peer_closed) s.clients = MAP (λc. c.peer_closed) t.clients ∧
    s.future = t.future
End

Theorem wagree_refl[simp]:
  wagree s s
Proof
  simp[wagree_def]
QED

Theorem wagree_sym:
  wagree s t ⇔ wagree t s
Proof
  simp[wagree_def] >> metis_tac[]
QED

Theorem wagree_trans:
  wagree s t ∧ wagree t u ⇒ wagree s u
Proof
  simp[wagree_def]
QED

Theorem wagree_len:
  wagree s t ⇒ LENGTH s.clients = LENGTH t.clients ∧
               LENGTH s.listening = LENGTH t.listening ∧
               (∀l. ALOOKUP s.listening l = NONE ⇔ ALOOKUP t.listening l = NONE) ∧
               (∀j. j < LENGTH s.clients ⇒
                    (EL j s.clients).peer_closed = (EL j t.clients).peer_closed)
Proof
  simp[wagree_def] >> strip_tac >>
  ‘LENGTH (MAP (λc. c.peer_closed) s.clients) = LENGTH (MAP (λc. c.peer_closed) t.clients)’
    by ASM_REWRITE_TAC[] >>
  ‘LENGTH (MAP FST s.listening) = LENGTH (MAP FST t.listening)’ by ASM_REWRITE_TAC[] >>
  gvs[ALOOKUP_NONE] >> rw[] >>
  ‘EL j (MAP (λc. c.peer_closed) s.clients) = EL j (MAP (λc. c.peer_closed) t.clients)’
    by ASM_REWRITE_TAC[] >>
  gvs[EL_MAP]
QED

Theorem MAP_peer_LUPDATE:
  (g (EL j l)).peer_closed = (EL j l).peer_closed ⇒
  MAP (λc. c.peer_closed) (LUPDATE (g (EL j l)) j l) = MAP (λc. c.peer_closed) l
Proof
  rw[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[]
QED

Theorem deliver2_agree:
  wagree s t ⇒ wagree (deliver2 s a) (deliver2 t a)
Proof
  strip_tac >> drule wagree_len >> strip_tac >>
  Cases_on ‘a’ >> simp[deliver2_def] >> rw[] >> gvs[] >>
  gvs[wagree_def, update_client_def, AFUPDKEY_MAP_FST] >>
  rw[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem step_ok2_agree:
  ∀as s t. wagree s t ⇒ (step_ok2 s as ⇔ step_ok2 t as)
Proof
  Induct >> simp[step_ok2_def] >> rpt strip_tac >>
  qpat_assum ‘wagree s t’ (strip_assume_tac o MATCH_MP wagree_len) >>
  ‘LENGTH s.reserved = LENGTH t.reserved’ by gvs[wagree_def] >>
  drule deliver2_agree >> disch_then (qspec_then ‘h’ assume_tac) >>
  first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on ‘h’ >> simp[arrival_ok2_def] >> metis_tac[]
QED

Theorem hdo_agree:
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ⇒ wagree s' s
Proof
  Cases_on ‘a’ >>
  rw[hdo_def, sock_accept2_def, sock_read2_def, sock_write2_def, sock_close2_def,
     update_client_def, AllCaseEqs()] >>
  gvs[wagree_def, AFUPDKEY_MAP_FST] >>
  rw[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[]
QED

Theorem hacts_agree:
  ∀acts s hs rs evs s' hs'.
    hacts lfd (s, hs) acts = SOME (rs, evs, (s', hs')) ⇒ wagree s' s
Proof
  Induct >> simp[hacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘hdo _ _ _ = SOME (r1, st1, evs1)’ >> PairCases_on ‘st1’ >>
  drule hdo_agree >> first_x_assum drule >> metis_tac[wagree_trans]
QED

Theorem hacts_tot_agree:
  hacts_tot lfd (s, hs) acts = (rs, evs, (s', hs')) ⇒ wagree s' s
Proof
  simp[hacts_tot_def] >> Cases_on ‘hacts lfd (s, hs) acts’ >> simp[] >>
  rename1 ‘hacts _ _ _ = SOME y’ >> PairCases_on ‘y’ >> rw[] >>
  drule hacts_agree >> simp[]
QED

Theorem tick2_agree:
  wagree s t ⇒ wagree (tick2 s) (tick2 t)
Proof
  strip_tac >> ‘s.future = t.future’ by gvs[wagree_def] >>
  simp[tick2_def] >> CASE_TAC >> simp[] >>
  ‘∀as s t. wagree s t ⇒ wagree (FOLDL deliver2 s as) (FOLDL deliver2 t as)’
    by (Induct >> simp[] >> metis_tac[deliver2_agree]) >>
  first_x_assum irule >> gvs[wagree_def]
QED

Theorem ticks2_SUC':
  ∀n s. ticks2 (SUC n) s = tick2 (ticks2 n s)
Proof
  Induct >> simp[ticks2_def] >> metis_tac[ticks2_def]
QED

Theorem future_FOLDL_deliver2[simp]:
  ∀as s. (FOLDL deliver2 s as).future = s.future
Proof
  Induct >> simp[] >> rpt gen_tac >>
  ‘(deliver2 s h).future = s.future’ by (Cases_on ‘h’ >> rw[deliver2_def, update_client_def]) >>
  simp[]
QED

Theorem ticks2_future:
  ∀n. (ticks2 n (psk lfd hw ifds m w0)).future =
      LGENLIST (λi. parr lfd hw ifds m w0 (n + i)) NONE
Proof
  Induct
  >- (simp[ticks2_def, psk_def] >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]) >>
  simp[ticks2_SUC', tick2_def] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, ADD_CLAUSES]
QED

(* The world left alone agrees with the handle layer's, every round *)
Theorem agree_run:
  ∀n. wagree (ticks2 n s0) (FST (hst lfd ifds m s0 n))
Proof
  Induct >- simp[ticks2_def, hst_def, hrounds_def] >>
  Cases_on ‘hacts_tot lfd (hst lfd ifds m s0 n) (hacts_of lfd ifds m s0 n)’ >>
  rename1 ‘_ = (rs, r2)’ >> PairCases_on ‘r2’ >>
  drule hround_step >> strip_tac >>
  simp[ticks2_SUC', hpoll_def, sock_poll2_def] >>
  Cases_on ‘hst lfd ifds m s0 n’ >> gvs[] >>
  drule hacts_tot_agree >> strip_tac >>
  irule tick2_agree >> metis_tac[wagree_trans, wagree_sym]
QED

(* The world built from L1's run is well formed: every arrival of its
   schedule is effective when it arrives *)
Theorem psk_sched_wf2:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ⇒
  sched_wf2 (psk lfd hw ifds m w0)
Proof
  strip_tac >> simp[sched_wf2_def, next_step2_def, ticks2_future] >> gen_tac >>
  qspecl_then [‘parr lfd hw ifds m w0 n’, ‘ticks2 n (psk lfd hw ifds m w0)’,
               ‘FST (hst lfd ifds m (psk lfd hw ifds m w0) n)’] mp_tac step_ok2_agree >>
  simp[agree_run] >> disch_then kall_tac >>
  Cases_on ‘prounds lfd hw ifds m (w0, pinit) (SUC n)’
  >- (simp[parr_def, plog_def] >> Cases_on ‘pcm lfd hw ifds m w0 n’ >>
      simp[arrs_def, step_ok2_def]) >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  qpat_assum ‘prounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [prounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘prounds _ _ _ _ _ n = SOME (h0, ws0, evs0, logs0)’ >>
  rename1 ‘pround _ _ _ _ _ = SOME (snap, ws1, log, revs)’ >>
  drule_all l1pf_refines_hl >> strip_tac >>
  ‘hacts_of lfd ifds m (psk lfd hw ifds m w0) n = new_actions (log_of m) h0’
    by simp[hacts_of_def] >>
  PairCases_on ‘ws0’ >> rename1 ‘prounds _ _ _ _ _ n = SOME (h0, (w, ps), evs0, logs0)’ >>
  PairCases_on ‘ws1’ >> rename1 ‘pround _ _ _ _ _ = SOME (snap, (w', ps'), log, revs)’ >>
  gvs[] >>
  Cases_on ‘hst lfd ifds m (psk lfd hw ifds m w0) n’ >> rename1 ‘_ = (s, hs)’ >> gvs[] >>
  ‘plog lfd hw ifds m w0 n = log’
    by (drule prounds_logs >> strip_tac >>
        qpat_x_assum ‘prounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule plog_EL >> disch_then (qspec_then ‘n’ mp_tac) >>
        simp[EL_APPEND2]) >>
  Cases_on ‘pcm lfd hw ifds m w0 n’ >> rename1 ‘pcm _ _ _ _ _ n = (cm, k)’ >> gvs[] >>
  Cases_on ‘arrs lfd (cm, LENGTH s.clients) (plog lfd hw ifds m w0 n)’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >>
  ‘pcm lfd hw ifds m w0 (SUC n) = (ck0, ck1) ∧ parr lfd hw ifds m w0 n = as’
    by simp[pcm_def, parr_def] >>
  ‘∀f j. MEM (f, j) ck0 ∧ LENGTH s.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s.alloc j used = f’
    by (rw[] >> irule run_alloc_eq >> simp[] >> qexists_tac ‘SUC n’ >> simp[]) >>
  ‘LHD s.future = SOME as’ by simp[] >>
  ‘ck1 + 1 < dimword (:64)’
    by (qpat_assum ‘∀n'. SND (pcm _ _ _ _ _ n') + 1 < _’ (mp_tac o Q.SPEC ‘SUC n’) >>
        qpat_assum ‘pcm _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        simp[]) >>
  drule_all round_rel >> strip_tac >>
  drule hacts_agree >> strip_tac >>
  qspecl_then [‘as’, ‘s1’, ‘s’] mp_tac step_ok2_agree >> simp[]
QED

(* The world built from L1's run satisfies the hypotheses of the
   version-2 server theorems (EchoSpec2's server_world2) *)
Theorem psk_server_world:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ⇒
  (psk lfd hw ifds m w0).listening = [(lfd, [])] ∧
  (psk lfd hw ifds m w0).clients = [] ∧ (psk lfd hw ifds m w0).open_fds = [] ∧
  alloc_ok (psk lfd hw ifds m w0).alloc ∧ sched_wf2 (psk lfd hw ifds m w0)
Proof
  strip_tac >> simp[psk_def, run_alloc_ok] >>
  drule_all psk_sched_wf2 >> simp[psk_def]
QED
