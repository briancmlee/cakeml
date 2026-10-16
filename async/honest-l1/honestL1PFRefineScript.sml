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
  honestL1PFModel honestL1Model honestL1Steps honestL1Inv honestL0Rely honestL0World honestL0
  asyncHLModel
  socketV2FFI socketV2Events ffiSpikeSocketFFI asyncM3World asyncCore asyncLevel1
  llist alist
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
  (set_inb f x ps).eof = ps.eof ∧
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
   | Fail e _ => (ps with b := ps.b with exhausted := (e = E_MFILE ∨ e = E_NFILE), []))
    = (ps1, fl) ∧
  arrs lfd (cm, LENGTH s.clients) fl = (as, (cm1, k1)) ∧
  (∀f. MEM (f, LENGTH s.clients) cm1 ⇒ ∀used. ¬MEM f used ⇒ s.alloc (LENGTH s.clients) used = f) ⇒
  pv_rel lfd cm1 ps1 (FOLDL deliver2 s as) ∧ pown lfd ps1 ∧ l0own lfd w1 ps1 ∧
  k1 = LENGTH (FOLDL deliver2 s as).clients ∧
  ps1.b.tbl = ps.b.tbl ∧ ps1.b.nxt = ps.b.nxt ∧ ps1.b.closing = ps.b.closing ∧
  ps1.inb = ps.inb ∧ ps1.eof = ps.eof
Proof
  strip_tac >>
  ‘ps.acq = [] ∧ ¬ps.b.exhausted’ by gvs[wants_input_def] >>
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
  rpt conj_tac
  >- (‘(ps with b := ps.b with exhausted := (e = E_MFILE ∨ e = E_NFILE)).b.tbl = ps.b.tbl’
        by simp[] >> simp[pv_rel_b])
  >- (simp[pown_b])
  >> gvs[l0own_def] >> metis_tac[]
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

