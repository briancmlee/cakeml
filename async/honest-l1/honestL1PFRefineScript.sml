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
  honestL1PFModel honestL1Model honestL1Steps honestL0World honestL0 asyncHLModel
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
