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
  honestL1Model honestL1Inv honestL1PFModel honestL1PFInv
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

(* Handles below the bound are distinct *)
Theorem l1hdl_11:
  l1hdln (w2n lfd) i < dimword (:64) ∧ l1hdln (w2n lfd) j < dimword (:64) ⇒
  (l1hdl lfd i = l1hdl lfd j ⇔ i = j)
Proof
  rw[l1hdl_def, l1hdln_def] >> rw[] >> fs[]
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
  ‘l1hdln (w2n lfd) j < dimword (:64) ∧ l1hdln (w2n lfd) i < dimword (:64)’
    by (gvs[own_ok_def, l1hdln_def] >> rw[] >> fs[]) >>
  ‘i = j’ by metis_tac[l1hdl_11] >> gvs[]
QED
