(*
  Route (d), the output half (design/46): per episode j, what the spec
  says j sent, then the bytes L1 holds for j's fd, are what the server
  wrote through handle j; exactly, while j is live (its handle in the
  table, its fd not gone), and a prefix once L1 has started dropping
  (afterwards nothing reaches j's fd any more).

  TRACKED NEAR-DUPLICATE (design/46): this mirrors honest-ffi's out_rel /
  l1pf_round_sent_upto (honestL1PFOut) per episode instead of per client.
  Delete once the episode <-> v2-client bridge exists and echo is
  re-derived through out_rel.
*)
Theory honestEchoL0Out
Ancestors
  alist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestL1PFRefine
Libs
  preamble

(* Episode j's fd, as the spec's fold has it *)
Definition epfd_def:
  epfd (opn : (word64 # num) list) j = ALOOKUP (MAP (λ(f, i). (i, f)) opn) j
End

Theorem epfd_iff:
  ep_ok (k, opn) ⇒ (epfd opn j = SOME f ⇔ ALOOKUP opn f = SOME j)
Proof
  rw[ep_ok_def, epfd_def] >>
  ‘MAP FST (MAP (λ(f, i). (i, f)) opn) = MAP SND opn’
    by (qid_spec_tac ‘opn’ >> Induct >> simp[FORALL_PROD]) >>
  ‘ALL_DISTINCT (MAP FST (MAP (λ(f, i). (i, f)) opn))’ by simp[] >>
  eq_tac >> strip_tac >> imp_res_tac ALOOKUP_MEM >>
  irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[MEM_MAP, EXISTS_PROD]
QED

(* The bytes L1 holds for episode j: its fd's outbox, while L1 holds the
   fd for j (in the table under j's handle, or closing) *)
Definition obp_def:
  obp lfd ps opn j =
    case epfd opn j of
    | SOME f => if ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f ∨ MEM f ps.b.closing
                then outbox_of ps.b f else []
    | NONE => []
End

Definition live_def:
  live lfd ps j ⇔ ∃f. ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f ∧ ¬MEM f ps.b.gone
End

(* L1's outboxes: only held fds have an outbox entry or are gone, and a
   gone fd has an empty outbox *)
Definition okb_def:
  okb (b : l1st) ⇔
    ∀f. (MEM f (MAP FST b.outbox) ∨ MEM f b.gone ⇒ MEM f (MAP SND b.tbl) ∨ MEM f b.closing) ∧
        (MEM f b.gone ⇒ outbox_of b f = [])
End

Theorem outbox_of_key:
  outbox_of b f ≠ [] ⇒ MEM f (MAP FST b.outbox)
Proof
  rw[outbox_of_def] >> every_case_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
  simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* A fd with output, or gone, is held *)
Theorem okb_held:
  okb b ∧ (outbox_of b f ≠ [] ∨ MEM f b.gone) ⇒ MEM f (MAP SND b.tbl) ∨ MEM f b.closing
Proof
  rw[okb_def] >> metis_tac[outbox_of_key]
QED

Theorem MEM_FST_ADELKEY[simp]:
  MEM g (MAP FST (ADELKEY k l)) ⇔ g ≠ k ∧ MEM g (MAP FST l)
Proof
  rw[ADELKEY_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

Theorem MEM_FST_set_outbox:
  MEM g (MAP FST (set_outbox f x b).outbox) ⇒ g = f ∨ MEM g (MAP FST b.outbox)
Proof
  rw[set_outbox_def, ADELKEY_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

(* The bytes an action writes through handle hd *)
Definition wr_def:
  wr hd (Write h bs : sact) = (if h = hd then bs else []) ∧
  wr hd (Read h n : sact) = [] ∧
  wr hd (Accept l : sact) = []
End

Theorem hwritten_wr:
  ∀tr. hwritten hd tr = FLAT (MAP (wr hd o FST) tr)
Proof
  Induct >> fs[hwritten_def] >> Cases >> Cases_on ‘q’ >> fs[wr_def]
QED

(* The output invariant for episode j: snt the bytes the spec says j sent,
   hwt the bytes the server wrote through j's handle *)
Definition oi_def:
  oi lfd ps opn snt hwt j ⇔
    snt ++ obp lfd ps opn j ≼ hwt ∧
    (live lfd ps j ⇒ snt ++ obp lfd ps opn j = hwt) ∧
    (ps.b.nxt ≤ j ⇒ snt = [] ∧ hwt = [] ∧ obp lfd ps opn j = [])
End

Theorem isPREFIX_APPEND_L:
  a ++ b ≼ c ⇒ a ≼ c
Proof
  rw[] >> irule isPREFIX_TRANS >> qexists_tac ‘a ++ b’ >> simp[]
QED

Theorem oi_drop:
  oi lfd ps opn snt hwt j ∧ sn ++ obp lfd ps' opn' j ≼ obp lfd ps opn j ∧
  ¬live lfd ps' j ∧ ps.b.nxt ≤ ps'.b.nxt ∧
  (ps.b.nxt ≤ j ⇒ sn = [] ∧ obp lfd ps' opn' j = [] ∧ wb = [])  ∧
  (ps'.b.nxt ≤ j ⇒ ps.b.nxt ≤ j) ⇒
  oi lfd ps' opn' (snt ++ sn) (hwt ++ wb) j
Proof
  rw[oi_def] >> gvs[] >>
  irule isPREFIX_TRANS >> qexists_tac ‘hwt’ >> simp[] >>
  irule isPREFIX_TRANS >> qexists_tac ‘snt ++ obp lfd ps opn j’ >>
  simp_tac std_ss [GSYM APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPENDS] >> simp[]
QED

(* Writes dropped for an episode not live leave its invariant *)
Theorem oi_drop_write:
  oi lfd ps opn snt hwt j ∧ ¬live lfd ps j ∧ (ps.b.nxt ≤ j ⇒ wb = []) ⇒
  oi lfd ps opn snt (hwt ++ wb) j
Proof
  rw[oi_def] >> gvs[] >>
  irule isPREFIX_TRANS >> qexists_tac ‘hwt’ >> simp[]
QED

Theorem outbox_of_set_outbox[simp]:
  outbox_of (set_outbox f bs b) g = if g = f then bs else outbox_of b g
Proof
  rw[outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >> rw[]
QED

Theorem set_outbox_fields[local,simp]:
  (set_outbox f bs b).tbl = b.tbl ∧ (set_outbox f bs b).nxt = b.nxt ∧
  (set_outbox f bs b).closing = b.closing ∧ (set_outbox f bs b).gone = b.gone
Proof
  simp[set_outbox_def]
QED

Theorem after_send_fields2[simp]:
  (after_send f r b).tbl = b.tbl ∧ (after_send f r b).nxt = b.nxt ∧
  (after_send f r b).closing = b.closing
Proof
  rw[after_send_def] >> every_case_tac >> simp[]
QED

Theorem after_send_other:
  g ≠ f ⇒ outbox_of (after_send f r b) g = outbox_of b g ∧
          (MEM g (after_send f r b).gone ⇔ MEM g b.gone) ∧
          (after_send f r b).tbl = b.tbl ∧ (after_send f r b).nxt = b.nxt ∧
          (after_send f r b).closing = b.closing
Proof
  rw[after_send_def] >> every_case_tac >> rw[MEM_FILTER, outbox_of_def]
QED

(* An operation on fd f only leaves every other episode's bytes and
   liveness *)
Theorem obp_other:
  b'.tbl = ps.b.tbl ∧ b'.closing = ps.b.closing ∧
  (∀g. g ≠ f ⇒ outbox_of b' g = outbox_of ps.b g ∧ (MEM g b'.gone ⇔ MEM g ps.b.gone)) ∧
  (∀g. epfd opn j = SOME g ⇒ g ≠ f) ∧
  (∀g. ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME g ⇒ g ≠ f) ⇒
  obp lfd (ps with b := b') opn j = obp lfd ps opn j ∧
  (live lfd (ps with b := b') j ⇔ live lfd ps j)
Proof
  rw[obp_def, live_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

(* D25: a handle below a bound under 2^64 exists *)
Theorem hdln_bound:
  i < n ∧ n < 18446744073709551616 ⇒ hdln (w2n (lfd : word64)) i < 18446744073709551616
Proof
  rw[hdln_def]
QED

val HB = fn n => (simp[] >> irule hdln_bound >> qexists_tac n >> fs[]);

(* Episode j's handle holds j's fd *)
Theorem own_epfd:
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
  ALOOKUP ps.b.tbl (l1hdl lfd i) = SOME f ⇒
  ∃i'. i' < ps.b.nxt ∧ l1hdl lfd i = l1hdl lfd i' ∧ epfd opn i' = SOME f ∧
       ALOOKUP opn f = SOME i'
Proof
  strip_tac >> drule_all own_tbl_lookup >> strip_tac >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  qexists_tac ‘j’ >> simp[] >> metis_tac[epfd_iff]
QED

Theorem okb_set_outbox:
  okb b ∧ (MEM f (MAP SND b.tbl) ∨ MEM f b.closing) ∧ (MEM f b.gone ⇒ x = []) ⇒
  okb (set_outbox f x b)
Proof
  rw[okb_def] >> rw[] >> gvs[] >>
  TRY (drule MEM_FST_set_outbox >> strip_tac >> gvs[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem okb_after_send:
  okb b ∧ (MEM f (MAP SND b.tbl) ∨ MEM f b.closing) ⇒ okb (after_send f r b)
Proof
  rw[after_send_def] >> every_case_tac >> gvs[]
  >- (irule okb_set_outbox >> fs[] >> strip_tac >> fs[okb_def])
  >> gvs[okb_def, MEM_FILTER, outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem oi_b:
  ps'.b = ps.b ⇒ (oi lfd ps' = oi lfd ps)
Proof
  rw[FUN_EQ_THM, oi_def, obp_def, live_def]
QED

(* A write: through a live handle, its bytes join the episode's (sent at
   once in part or in whole, or queued); otherwise it is dropped *)
Theorem pdo_write_out:
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧ okb ps.b ∧
  (∀j. hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒
       wr (l1hdl lfd j) (Write h bs) = []) ⇒
  okb ps'.b ∧ ps'.b.nxt = ps.b.nxt ∧ l0_ep_st (k, opn) evs = (k, opn) ∧
  ∀j snt hwt. hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
    oi lfd ps' opn (snt ++ ep_sn j (k, opn) evs) (hwt ++ wr (l1hdl lfd j) (Write h bs)) j
Proof
  strip_tac >> drule_all pdo_write_in >>
  disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >> simp[] >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  reverse (Cases_on ‘∃f. ALOOKUP ps.b.tbl h = SOME f ∧ ¬MEM f ps.b.gone’)
  >- ((* dropped *)
      ‘ps'.b = ps.b ∧ evs = []’
        by (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
            simp[pdo_def, l1do_def] >> every_case_tac >> gvs[] >> rw[] >> gvs[]) >>
      ‘oi lfd ps' = oi lfd ps’ by (irule oi_b >> simp[]) >>
      simp[ep_fold_def] >> rpt strip_tac >>
      simp[wr_def] >> rw[] >> irule oi_drop_write >> fs[live_def] >>
      rpt strip_tac >> qpat_x_assum ‘∀j'. _ ⇒ wr _ _ = _’ (qspec_then ‘j’ mp_tac) >>
      fs[wr_def]) >>
  gvs[] >>
  drule_all own_tbl_lookup >> strip_tac >> rename1 ‘h = l1hdl lfd i’ >>
  ‘i < k’ by gvs[own_ok_def] >>
  ‘epfd opn i = SOME f’ by metis_tac[epfd_iff] >>
  ‘hdln (w2n lfd) i < dimword (:64)’ by HB ‘ps.b.nxt’ >>
  ‘MEM f (MAP SND ps.b.tbl)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘∀j. hdln (w2n lfd) j < dimword (:64) ∧ j ≠ i ⇒
       l1hdl lfd j ≠ l1hdl lfd i ∧ (∀g. epfd opn j = SOME g ⇒ g ≠ f) ∧
       (∀g. ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME g ⇒ g ≠ f)’
    by (rpt gen_tac >> strip_tac >>
        ‘l1hdl lfd j ≠ l1hdl lfd i’ by simp[hdl_eq_iff] >> simp[] >> conj_tac
        >- (strip_tac >> ‘ALOOKUP opn f = SOME j’ by metis_tac[epfd_iff] >> gvs[]) >>
        rpt strip_tac >> gvs[] >>
        ‘ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f’ by simp[] >>
        drule_all own_tbl_lookup >> strip_tac >> rename1 ‘l1hdl lfd j = l1hdl lfd i'’ >>
        ‘i' = i’ by gvs[] >> gvs[] >>
        ‘hdln (w2n lfd) j < dimword (:64) ∧ hdln (w2n lfd) i < dimword (:64)’ by simp[] >>
        qpat_x_assum ‘l1hdl _ _ = _’ mp_tac >> simp[hdl_eq_iff]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  Cases_on ‘outbox_of ps.b f = []’ >> simp[]
  >- ((* sent at once *)
      simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      drule_all sys_send_event >> strip_tac >>
      conj_tac
      >- (irule okb_after_send >> simp[] >> irule okb_set_outbox >> simp[]) >>
      rpt strip_tac >> simp[ep_fold_def] >>
      reverse (Cases_on ‘j = i’)
      >- (first_x_assum drule_all >> strip_tac >>
          ‘ALOOKUP opn f ≠ SOME j’ by gvs[] >>
          simp[wr_def] >>
          ‘obp lfd (ps with b := after_send f (l0_res_of out) (set_outbox f bs ps.b)) opn j =
           obp lfd ps opn j ∧
           (live lfd (ps with b := after_send f (l0_res_of out) (set_outbox f bs ps.b)) j ⇔
            live lfd ps j)’
            by (irule obp_other >> simp[] >> qexists_tac ‘f’ >> rw[] >>
                fs[after_send_other]) >>
          gvs[oi_def]) >>
      gvs[wr_def, oi_def, obp_def, live_def] >>
      Cases_on ‘l0_res_of out’ >> gvs[after_send_def] >>
      rw[] >> gvs[outbox_of_def] >>
      simp_tac std_ss [GSYM APPEND_ASSOC, TAKE_DROP] >> simp[]) >>
  (* queued behind the outbox *)
  strip_tac >> gvs[] >> conj_tac
  >- (irule okb_set_outbox >> simp[]) >>
  rpt strip_tac >> simp[ep_fold_def] >>
  reverse (Cases_on ‘j = i’)
  >- (first_x_assum drule_all >> strip_tac >> simp[wr_def] >>
      ‘obp lfd (ps with b := set_outbox f (outbox_of ps.b f ++ bs) ps.b) opn j =
       obp lfd ps opn j ∧
       (live lfd (ps with b := set_outbox f (outbox_of ps.b f ++ bs) ps.b) j ⇔
        live lfd ps j)’
        by (irule obp_other >> simp[] >> qexists_tac ‘f’ >> rw[]) >>
      gvs[oi_def]) >>
  gvs[wr_def, oi_def, obp_def, live_def]
QED

Theorem okb_acc:
  okb b ⇒ okb (b with <| tbl := x :: b.tbl; nxt := n |>)
Proof
  simp[okb_def, outbox_of_def] >> rpt strip_tac >> res_tac >> simp[]
QED

(* An accept hands out the pending fd's handle: its episode, unwritten
   and with nothing queued, becomes live *)
Theorem pdo_accept_out:
  pdo lfd (w, ps) (Accept l) = SOME (r, (w', ps'), evs) ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧ okb ps.b ⇒
  okb ps'.b ∧ ps.b.nxt ≤ ps'.b.nxt ∧ evs = [] ∧
  ∀j snt hwt. hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
    oi lfd ps' opn snt hwt j
Proof
  strip_tac >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
  simp[pdo_def] >> Cases_on ‘ps.acq’ >> simp[] >> rw[] >> simp[] >>
  rename1 ‘ps.acq = f :: q’ >>
  ‘ALOOKUP opn f = SOME ps.b.nxt’
    by (gvs[own_ok_def] >> first_x_assum (qspec_then ‘0’ mp_tac) >> simp[]) >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  ‘¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.b.closing’
    by (gvs[own_ok_def] >> conj_tac >>
        strip_tac >> gvs[MEM_MAP, EXISTS_PROD] >> res_tac >> gvs[]) >>
  ‘outbox_of ps.b f = [] ∧ ¬MEM f ps.b.gone’ by metis_tac[okb_held] >>
  ‘ps.b.nxt < k’ by gvs[own_ok_def] >>
  ‘hdln (w2n l) ps.b.nxt < dimword (:64)’ by fs[] >>
  TRY (irule okb_acc >> simp[] >> NO_TAC) >>
  Cases_on ‘j = ps.b.nxt’
  >- (gvs[oi_def, obp_def, live_def, outbox_of_def] >>
      ‘epfd opn ps.b.nxt = SOME f’ by metis_tac[epfd_iff] >> gvs[]) >>
  ‘hdl l j ≠ hdl l ps.b.nxt’ by simp[hdl_eq_iff] >>
  gvs[oi_def, obp_def, live_def, outbox_of_def]
QED

(* An operation that leaves episode j's fd, handle entry and that fd's
   buffers leaves j's bytes and liveness *)
Theorem obp_frame:
  epfd opn' j = epfd opn j ∧
  ALOOKUP ps'.b.tbl (l1hdl lfd j) = ALOOKUP ps.b.tbl (l1hdl lfd j) ∧
  (∀g. epfd opn j = SOME g ∨ ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME g ⇒
       (MEM g ps'.b.closing ⇔ MEM g ps.b.closing) ∧
       outbox_of ps'.b g = outbox_of ps.b g ∧ (MEM g ps'.b.gone ⇔ MEM g ps.b.gone)) ⇒
  obp lfd ps' opn' j = obp lfd ps opn j ∧ (live lfd ps' j ⇔ live lfd ps j)
Proof
  rw[obp_def, live_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem MEM_SND_ADELKEY_other[local]:
  (∀g. MEM (h, g) tbl ⇒ g = f) ∧ g ≠ f ⇒
  (MEM g (MAP SND (ADELKEY h tbl)) ⇔ MEM g (MAP SND tbl))
Proof
  rw[ADELKEY_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

Theorem epfd_ADELKEY:
  ep_ok (k, opn) ∧ epfd (ADELKEY f opn) j = SOME g ⇒ epfd opn j = SOME g ∧ g ≠ f
Proof
  strip_tac >> ‘ep_ok (k, ADELKEY f opn)’ by metis_tac[ep_ok_ADELKEY] >>
  ‘ALOOKUP (ADELKEY f opn) g = SOME j’ by metis_tac[epfd_iff] >>
  gvs[ALOOKUP_ADELKEY] >> metis_tac[epfd_iff]
QED

Theorem epfd_ADELKEY_other:
  ep_ok (k, opn) ∧ ALOOKUP opn f = SOME i ∧ j ≠ i ⇒ epfd (ADELKEY f opn) j = epfd opn j
Proof
  strip_tac >> ‘ep_ok (k, ADELKEY f opn)’ by metis_tac[ep_ok_ADELKEY] >>
  Cases_on ‘epfd opn j’
  >- (Cases_on ‘epfd (ADELKEY f opn) j’ >> simp[] >> metis_tac[epfd_ADELKEY, NOT_SOME_NONE]) >>
  ‘ALOOKUP opn x = SOME j’ by metis_tac[epfd_iff] >>
  ‘x ≠ f’ by (strip_tac >> gvs[]) >>
  ‘ALOOKUP (ADELKEY f opn) x = SOME j’ by simp[ALOOKUP_ADELKEY] >>
  metis_tac[epfd_iff]
QED

Theorem okb_flushing:
  okb b ∧ (∀g. MEM (h, g) b.tbl ⇒ g = f) ⇒
  okb (b with <| tbl := ADELKEY h b.tbl; closing := f :: b.closing |>)
Proof
  simp[okb_def] >> rpt strip_tac >> Cases_on ‘f' = f’ >> simp[] >>
  ‘MEM f' (MAP SND (ADELKEY h b.tbl)) ⇔ MEM f' (MAP SND b.tbl)’
    by (irule MEM_SND_ADELKEY_other >> simp[] >> qexists_tac ‘f’ >> simp[]) >>
  gvs[outbox_of_def] >> first_x_assum (qspec_then ‘f'’ mp_tac) >> simp[outbox_of_def]
QED

Theorem okb_closed:
  okb b ∧ (∀g. MEM (h, g) b.tbl ⇒ g = f) ⇒
  okb (forget f (b with tbl := ADELKEY h b.tbl))
Proof
  simp[okb_def, forget_def, MEM_FILTER] >> rpt strip_tac >> Cases_on ‘f' = f’ >>
  gvs[outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >>
  ‘MEM f' (MAP SND (ADELKEY h b.tbl)) ⇔ MEM f' (MAP SND b.tbl)’
    by (irule MEM_SND_ADELKEY_other >> simp[] >> qexists_tac ‘f’ >> simp[]) >>
  first_x_assum (qspec_then ‘f'’ mp_tac) >> simp[outbox_of_def]
QED

(* A read: it moves no bytes out; at EOF it takes the handle away (the fd
   still flushing, or closed) *)
Theorem pdo_read_out:
  pdo lfd (w, ps) (Read h n) = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧ okb ps.b ⇒
  okb ps'.b ∧ ps'.b.nxt = ps.b.nxt ∧
  ∀j snt hwt. hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
    oi lfd ps' (SND (l0_ep_st (k, opn) evs)) (snt ++ ep_sn j (k, opn) evs) hwt j
Proof
  strip_tac >> ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
  Cases_on ‘ALOOKUP ps.b.tbl h’ >> simp[]
  >- (strip_tac >> gvs[ep_fold_def, set_inb_def] >> rpt strip_tac >>
      qmatch_goalsub_abbrev_tac ‘oi lfd PS’ >> ‘PS.b = ps.b’ by gvs[Abbr ‘PS’] >>
      drule oi_b >> disch_then (qspec_then ‘lfd’ SUBST1_TAC) >> simp[]) >>
  rename1 ‘ALOOKUP ps.b.tbl h = SOME f’ >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[ep_fold_def, set_inb_def] >> rpt strip_tac >>
      qmatch_goalsub_abbrev_tac ‘oi lfd PS’ >> ‘PS.b = ps.b’ by gvs[Abbr ‘PS’] >>
      drule oi_b >> disch_then (qspec_then ‘lfd’ SUBST1_TAC) >> simp[]) >>
  reverse IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[ep_fold_def, set_inb_def] >> rpt strip_tac >>
      qmatch_goalsub_abbrev_tac ‘oi lfd PS’ >> ‘PS.b = ps.b’ by gvs[Abbr ‘PS’] >>
      drule oi_b >> disch_then (qspec_then ‘lfd’ SUBST1_TAC) >> simp[]) >>
  (* EOF *)
  drule_all own_tbl_lookup >> strip_tac >> rename1 ‘h = l1hdl lfd i’ >>
  ‘i < k’ by gvs[own_ok_def] >>
  ‘epfd opn i = SOME f’ by metis_tac[epfd_iff] >>
  ‘hdln (w2n lfd) i < dimword (:64)’ by HB ‘ps.b.nxt’ >>
  ‘∀g. MEM (h, g) ps.b.tbl ⇒ g = f’ by metis_tac[own_tbl_entry_fd] >>
  ‘∀j. hdln (w2n lfd) j < dimword (:64) ∧ j ≠ i ⇒
       l1hdl lfd j ≠ l1hdl lfd i ∧ (∀g. epfd opn j = SOME g ⇒ g ≠ f) ∧
       (∀g. ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME g ⇒ g ≠ f)’
    by (rpt gen_tac >> strip_tac >>
        ‘l1hdl lfd j ≠ l1hdl lfd i’ by simp[hdl_eq_iff] >> simp[] >> conj_tac
        >- (strip_tac >> ‘ALOOKUP opn f = SOME j’ by metis_tac[epfd_iff] >> gvs[]) >>
        rpt strip_tac >> gvs[] >>
        ‘ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f’ by simp[] >>
        drule_all own_tbl_lookup >> strip_tac >> rename1 ‘l1hdl lfd j = l1hdl lfd i'’ >>
        ‘i' = i’ by gvs[] >> gvs[] >>
        ‘hdln (w2n lfd) j < dimword (:64) ∧ hdln (w2n lfd) i < dimword (:64)’ by simp[] >>
        qpat_x_assum ‘l1hdl _ _ = _’ mp_tac >> simp[hdl_eq_iff]) >>
  IF_CASES_TAC >> simp[]
  >- ((* EOF and nothing to flush: the fd is closed *)
      ‘outbox_of ps.b f = []’ by (gvs[okb_def] >> metis_tac[]) >>
      simp[PULL_EXISTS] >> rpt gen_tac >> PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      drule_all sys_close_event >> strip_tac >>
      conj_tac >- (irule okb_closed >> gvs[]) >>
      simp[ep_fold_def, forget_def] >>
      rpt strip_tac >>
      qmatch_goalsub_abbrev_tac ‘oi lfd PS OPN’ >>
      ‘OPN = opn ∨ OPN = ADELKEY f opn’
        by (simp[Abbr ‘OPN’, l0_ep_step_def] >> every_case_tac >> gvs[]) >>
      (Cases_on ‘j = i’
       >- (qpat_x_assum ‘j = i’ SUBST_ALL_TAC >>
           ‘¬live lfd PS i ∧ obp lfd PS OPN i = []’
             by (simp[Abbr ‘PS’, obp_def, live_def, ALOOKUP_ADELKEY] >>
                 every_case_tac >> gvs[MEM_FILTER] >>
                 drule_all epfd_ADELKEY >> strip_tac >> gvs[]) >>
           gvs[oi_def] >> conj_tac
           >- (imp_res_tac isPREFIX_APPEND_L >> fs[]) >>
           gvs[Abbr ‘PS’]) >>
       first_x_assum drule_all >> strip_tac >>
       ‘epfd OPN j = epfd opn j’ by (gvs[] >> metis_tac[epfd_ADELKEY_other]) >>
       ‘obp lfd PS OPN j = obp lfd ps opn j ∧ (live lfd PS j ⇔ live lfd ps j)’
         by (irule obp_frame >> simp[Abbr ‘PS’, ALOOKUP_ADELKEY, MEM_FILTER] >>
             simp[outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >> metis_tac[]) >>
       gvs[oi_def, Abbr ‘PS’])) >>
  (* EOF with bytes to flush: the fd closes later *)
  strip_tac >> gvs[ep_fold_def] >>
  conj_tac >- (irule okb_flushing >> gvs[]) >>
  rpt strip_tac >> qmatch_goalsub_abbrev_tac ‘oi lfd PS’ >>
  Cases_on ‘j = i’
  >- (gvs[] >>
      ‘¬live lfd PS i ∧ obp lfd PS opn i = obp lfd ps opn i’
        by simp[Abbr ‘PS’, obp_def, live_def, ALOOKUP_ADELKEY, outbox_of_def] >>
      gvs[oi_def, Abbr ‘PS’]) >>
  first_x_assum drule_all >> strip_tac >>
  ‘obp lfd PS opn j = obp lfd ps opn j ∧ (live lfd PS j ⇔ live lfd ps j)’
    by (irule obp_frame >> simp[Abbr ‘PS’, ALOOKUP_ADELKEY, outbox_of_def] >> metis_tac[]) >>
  gvs[oi_def, Abbr ‘PS’]
QED

(* MAIN, one action *)
Theorem pdo_out:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧ okb ps.b ∧
  (∀j. hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒ wr (l1hdl lfd j) a = []) ⇒
  okb ps'.b ∧ ps.b.nxt ≤ ps'.b.nxt ∧
  ∀j snt hwt. hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
    oi lfd ps' (SND (l0_ep_st (k, opn) evs)) (snt ++ ep_sn j (k, opn) evs)
       (hwt ++ wr (l1hdl lfd j) a) j
Proof
  Cases_on ‘a’ >> strip_tac
  >- (drule_all pdo_accept_out >> strip_tac >> gvs[wr_def, ep_fold_def])
  >- (drule_all pdo_read_out >> strip_tac >> gvs[wr_def])
  >> drule_all pdo_write_out >> strip_tac >> gvs[]
QED

(* MAIN, the round's actions *)
Theorem pacts_out:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ∧ okb ps.b ∧
    (∀j. hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒
         FLAT (MAP (wr (l1hdl lfd j)) acts) = []) ⇒
    okb ps'.b ∧ ps.b.nxt ≤ ps'.b.nxt ∧
    ∀j snt hwt. hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
      oi lfd ps' (SND (l0_ep_st (k, opn) evs)) (snt ++ ep_sn j (k, opn) evs)
         (hwt ++ FLAT (MAP (wr (l1hdl lfd j)) acts)) j
Proof
  Induct >> simp[pacts_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 ‘pdo lfd (w, ps) a = SOME (r, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule pdo_out >> simp[] >>
  disch_then (qspecl_then [‘opn’, ‘k’] mp_tac) >> simp[] >> strip_tac >>
  ‘ps.b.nxt < dimword (:64)’ by fs[] >>
  ‘ws11.b.nxt + naccepts acts < dimword (:64)’
    by (drule pdo_nxt_acc >>
        ‘naccepts (a :: acts) = naccepts [a] + naccepts acts’ by (Cases_on ‘a’ >> simp[]) >>
        fs[]) >>
  drule_all pdo_in >> strip_tac >>
  ‘l0_rely ws10’ by metis_tac[pdo_rely] >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> rename1 ‘_ = (k1, opn1)’ >> gvs[] >>
  first_x_assum (qspecl_then [‘ws10’, ‘ws11’, ‘rs'’, ‘evs'’, ‘w'’, ‘ps'’, ‘opn1’] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]) >>
  strip_tac >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >>
  simp[ep_fold_APPEND]
QED

(* A stage that only moves queued bytes out (or drops them) *)
Theorem oi_shift:
  oi lfd ps opn snt hwt j ∧ sn ++ obp lfd ps' opn' j ≼ obp lfd ps opn j ∧
  (live lfd ps' j ⇒ live lfd ps j ∧ sn ++ obp lfd ps' opn' j = obp lfd ps opn j) ∧
  ps'.b.nxt = ps.b.nxt ⇒
  oi lfd ps' opn' (snt ++ sn) hwt j
Proof
  rw[oi_def] >> gvs[]
  >- (irule isPREFIX_TRANS >> qexists_tac ‘snt ++ obp lfd ps opn j’ >>
      simp_tac std_ss [GSYM APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPENDS] >> simp[]) >>
  gvs[]
QED

(* A fd L1 holds (in the table or closing) is one episode's, whose
   bytes are its outbox *)
Theorem held_episode:
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
  (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing) ⇒
  ∃i. i < ps.b.nxt ∧ ALOOKUP opn f = SOME i ∧
      obp lfd ps opn i = outbox_of ps.b f ∧
      (∀j. hdln (w2n lfd) j < dimword (:64) ∧ ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f ⇒
           i = j)
Proof
  strip_tac >> ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  ‘∃i. i < ps.b.nxt ∧ ALOOKUP opn f = SOME i ∧ obp lfd ps opn i = outbox_of ps.b f’
    by (‘ps.b.nxt < dimword (:64)’ by fs[] >>
        (Cases_on ‘MEM f ps.b.closing’
         >- (qpat_x_assum ‘own_ok _ _ _’ mp_tac >> simp[own_ok_def] >> strip_tac >>
             first_x_assum drule >> strip_tac >> qexists_tac ‘j’ >> simp[] >>
             ‘epfd opn j = SOME f’ by metis_tac[epfd_iff] >> simp[obp_def]) >>
         ‘MEM f (MAP SND ps.b.tbl)’ by gvs[] >>
         gvs[MEM_MAP, EXISTS_PROD] >> rename1 ‘MEM (h, f) ps.b.tbl’ >>
         ‘∃i. i < ps.b.nxt ∧ h = l1hdl lfd i ∧ ALOOKUP opn f = SOME i’
           by (qpat_x_assum ‘own_ok _ _ _’ mp_tac >> simp[own_ok_def] >> strip_tac >>
               first_x_assum drule >> strip_tac >> metis_tac[]) >>
         qexists_tac ‘i’ >> gvs[] >>
         ‘∃g. ALOOKUP ps.b.tbl (hdl lfd i) = SOME g’
           by (Cases_on ‘ALOOKUP ps.b.tbl (hdl lfd i)’ >>
               gvs[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
         ‘ALOOKUP ps.b.tbl (l1hdl lfd i) = SOME g ∧ MEM (l1hdl lfd i, f) ps.b.tbl’ by simp[] >>
         ‘ps.b.nxt < dimword (:64)’ by fs[] >>
         drule_all own_tbl_entry_fd >> strip_tac >> gvs[] >>
         ‘epfd opn i = SOME f’ by metis_tac[epfd_iff] >> simp[obp_def])) >>
  qexists_tac ‘i’ >> simp[] >> rpt strip_tac >>
  drule_all own_tbl_lookup >> strip_tac >>
  ‘j' = i’ by gvs[] >> gvs[] >>
  ‘i < k’ by gvs[own_ok_def] >>
  ‘hdln (w2n lfd) i < dimword (:64)’ by HB ‘ps.b.nxt’ >>
  ‘hdl lfd j = hdl lfd i ⇔ j = i’ by (irule hdl_eq_iff >> fs[]) >> gvs[]
QED

(* One send from an outbox *)
Theorem send_out:
  sys_send f (outbox_of b f) w = SOME (out, w1, ev) ∧ l0_rely w ∧ okb b ∧
  outbox_of b f ≠ [] ∧ ¬MEM f b.gone ∧
  own_ok lfd (k, opn) (ps with b := b) ∧ b.nxt < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ∧ oi lfd (ps with b := b) opn snt hwt j ⇒
  okb (after_send f (l0_res_of out) b) ∧ l0_ep_step (k, opn) ev = (k, opn) ∧
  oi lfd (ps with b := after_send f (l0_res_of out) b) opn
     (snt ++ ep_sn j (k, opn) [ev]) hwt j
Proof
  strip_tac >> drule_all sys_send_event >> strip_tac >>
  ‘MEM f (MAP SND b.tbl) ∨ MEM f b.closing’ by metis_tac[okb_held] >>
  ‘okb (after_send f (l0_res_of out) b)’ by (irule okb_after_send >> simp[]) >>
  simp[l0_ep_step_def] >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  mp_tac (Q.INST [‘ps’ |-> ‘ps with b := b’] held_episode) >> simp[] >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘epfd opn i = SOME f’
    by (drule epfd_iff >> disch_then (qspecl_then [‘i’, ‘f’] (fn th => rewrite_tac[th])) >>
        first_assum ACCEPT_TAC) >>
  ‘ep_sn j (k, opn) [ev] = if i = j then l0_event_sent f ev else []’
    by (rewrite_tac[ep_fold_def] >> qpat_x_assum ‘send_fd ev = _’ (fn th => rewrite_tac[th]) >>
        simp_tac std_ss [optionTheory.option_case_def, APPEND_NIL] >>
        qpat_x_assum ‘ALOOKUP opn f = SOME i’ (fn th => rewrite_tac[th, optionTheory.SOME_11])) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  (* per disjunct of the held fd *)
  (reverse (Cases_on ‘j = i’)
  >- (‘ALOOKUP opn f ≠ SOME j’ by gvs[] >> simp[] >>
      ‘obp lfd (ps with b := after_send f (l0_res_of out) b) opn j =
       obp lfd (ps with b := b) opn j ∧
       (live lfd (ps with b := after_send f (l0_res_of out) b) j ⇔
        live lfd (ps with b := b) j)’
        by (mp_tac (Q.INST [‘ps’ |-> ‘ps with b := b’, ‘b'’ |-> ‘after_send f (l0_res_of out) b’]
                      obp_other) >>
            simp[] >> disch_then irule >> rpt conj_tac
            >- (rpt strip_tac >> fs[after_send_other])
            >- (strip_tac >> first_x_assum (qspec_then ‘j’ mp_tac) >> fs[])
            >> strip_tac >> drule_then (qspecl_then [‘j’, ‘f’] mp_tac) epfd_iff >> fs[]) >>
      gvs[oi_def]) >>
  gvs[] >> irule oi_shift >> qexistsl [‘opn’, ‘ps with b := b’] >> simp[] >>
  ‘obp lfd (ps with b := after_send f (l0_res_of out) b) opn i =
   outbox_of (after_send f (l0_res_of out) b) f’
    by (qpat_x_assum ‘obp _ _ _ _ = outbox_of _ _’ mp_tac >> simp[obp_def] >>
        rw[] >> gvs[]) >>
  simp[live_def] >>
  Cases_on ‘l0_res_of out’ >> gvs[after_send_def] >> rw[] >> gvs[] >>
  disj1_tac >>
  ‘ALOOKUP (ps with b := b).b.tbl (l1hdl lfd i) = SOME f'’ by simp[] >>
  drule_all own_tbl_lookup >> strip_tac >>
  qmatch_asmsub_rename_tac ‘l1hdl lfd i = l1hdl lfd jj’ >>
  ‘jj < k’ by gvs[own_ok_def] >>
  ‘hdln (w2n lfd) jj < dimword (:64) ∧ hdln (w2n lfd) i < dimword (:64)’
    by (conj_tac >> HB ‘b.nxt’) >>
  ‘hdl lfd i = hdl lfd jj ⇔ i = jj’ by (irule hdl_eq_iff >> simp[]) >>
  gvs[] >> metis_tac[own_fd_unique])
QED

(* The flush: what a send takes leaves the outbox *)
Theorem l1_flush_out:
  ∀fs w b w' b' evs snt.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ okb b ∧
    own_ok lfd (k, opn) (ps with b := b) ∧ b.nxt < dimword (:64) ∧
    hdln (w2n lfd) j < dimword (:64) ∧ oi lfd (ps with b := b) opn snt hwt j ⇒
    okb b' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧ b'.closing = b.closing ∧
    oi lfd (ps with b := b') opn (snt ++ ep_sn j (k, opn) evs) hwt j
Proof
  Induct >> simp[l1_flush_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  ‘b.nxt < dimword (:64) ∧ hdln (w2n lfd) j < dimword (:64)’ by fs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 ‘sys_send h _ w = SOME (out, w1, ev)’ >>
  ‘b.nxt < dimword (:64) ∧ hdln (w2n lfd) j < dimword (:64)’ by fs[] >>
  drule_all send_out >> strip_tac >>
  ‘l0_rely w1’ by (gvs[sys_send_def] >> metis_tac[l0_do_rely]) >>
  ‘own_ok lfd (k, opn) (ps with b := after_send h (l0_res_of out) b)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := after_send h (l0_res_of out) b’,
                        ‘ps’ |-> ‘ps with b := b’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[]) >>
  ‘(after_send h (l0_res_of out) b).nxt < 18446744073709551616’
    by (‘(after_send h (l0_res_of out) b).nxt = b.nxt’
          by (rw[after_send_def] >> every_case_tac >> simp[set_outbox_def]) >> fs[]) >>
  first_x_assum drule_all >> strip_tac >> gvs[ep_fold_def]
QED

(* The fd in the table under handle j is episode j's *)
Theorem tbl_epfd:
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ∧ ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME g ⇒
  epfd opn j = SOME g
Proof
  strip_tac >> drule_all own_tbl_lookup >> strip_tac >>
  qmatch_asmsub_rename_tac ‘l1hdl lfd j = l1hdl lfd jj’ >>
  ‘jj < k ∧ ep_ok (k, opn)’ by gvs[own_ok_def] >>
  ‘hdln (w2n lfd) jj < dimword (:64)’ by HB ‘ps.b.nxt’ >>
  ‘hdl lfd j = hdl lfd jj ⇔ j = jj’ by (irule hdl_eq_iff >> fs[]) >>
  gvs[] >> drule_then (qspecl_then [‘j’, ‘g’] mp_tac) epfd_iff >> simp[]
QED

(* The hung-up policy only drops outboxes *)
Theorem stall_out:
  okb ps.b ∧ own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
  okb (stall_step hfs ob log ps).b ∧ oi lfd (stall_step hfs ob log ps) opn snt hwt j
Proof
  strip_tac >>
  qspecl_then [‘hfs’, ‘ob’, ‘log’, ‘ps’] strip_assume_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_b) >>
  qabbrev_tac ‘ps' = stall_step hfs ob log ps’ >>
  conj_tac
  >- (‘∀g. MEM g (MAP FST ps'.b.outbox) ⇒ MEM g (MAP FST ps.b.outbox)’
        by (gvs[] >> metis_tac[FOLDL_drop_out]) >>
      gvs[okb_def, FOLDL_drop_out] >> rw[] >> gvs[] >> metis_tac[]) >>
  ‘snt = snt ++ []’ by simp[] >> pop_assum SUBST1_TAC >>
  irule oi_shift >> qexistsl [‘opn’, ‘ps’] >> simp[FOLDL_drop_out] >>
  simp[obp_def, live_def, FOLDL_drop_out] >>
  reverse conj_tac >- (every_case_tac >> rw[]) >>
  strip_tac >> simp[] >>
  ‘epfd opn j = SOME f’ by (irule tbl_epfd >> qexistsl [‘k’, ‘lfd’, ‘ps’] >> fs[]) >>
  simp[]
QED

(* As honestL1PFOut's forget_keys (not an ancestor here) *)
Theorem forget_keys[local]:
  outbox_of (forget f st) g = (if g = f then [] else outbox_of st g) ∧
  (forget f st).gone = FILTER ($≠ f) st.gone ∧ (forget f st).tbl = st.tbl ∧
  (forget f st).closing = FILTER ($≠ f) st.closing ∧ (forget f st).nxt = st.nxt
Proof
  rw[forget_def, outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY]
QED

Theorem okb_forget:
  okb b ⇒ okb (forget f b)
Proof
  simp[okb_def, forget_def, MEM_FILTER] >> rpt strip_tac >> Cases_on ‘f' = f’ >>
  gvs[outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >>
  first_x_assum (qspec_then ‘f'’ mp_tac) >> simp[outbox_of_def]
QED

Theorem epfd_ADELKEY_ne:
  ep_ok (k, opn) ∧ epfd opn j ≠ SOME f ⇒ epfd (ADELKEY f opn) j = epfd opn j
Proof
  strip_tac >> Cases_on ‘epfd opn j’
  >- (Cases_on ‘epfd (ADELKEY f opn) j’ >> simp[] >>
      drule_all epfd_ADELKEY >> simp[]) >>
  rename1 ‘epfd opn j = SOME g’ >>
  ‘ALOOKUP opn g = SOME j’ by (drule_then (qspecl_then [‘j’, ‘g’] mp_tac) epfd_iff >> simp[]) >>
  ‘ep_ok (k, ADELKEY f opn)’ by metis_tac[ep_ok_ADELKEY] >>
  ‘ALOOKUP (ADELKEY f opn) g = SOME j’ by gvs[ALOOKUP_ADELKEY] >>
  drule_then (qspecl_then [‘j’, ‘g’] mp_tac) epfd_iff >> simp[]
QED

(* Closing a fd the table no longer holds: its episode's bytes are gone
   from L1 (it was quiet or dropped), nothing else changes *)
Theorem close_out:
  l1_close f (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ okb b ∧
  own_ok lfd (k, opn) (ps with b := b) ∧ b.nxt < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ∧ ¬MEM f (MAP SND b.tbl) ∧
  oi lfd (ps with b := b) opn snt hwt j ⇒
  okb b' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧
  oi lfd (ps with b := b') (SND (l0_ep_st (k, opn) evs)) (snt ++ ep_sn j (k, opn) evs) hwt j
Proof
  strip_tac >> drule l1_close_shape >> strip_tac >> gvs[] >>
  drule_all sys_close_event >> strip_tac >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  ‘okb (forget f b)’ by metis_tac[okb_forget] >>
  ‘ep_sn j (k, opn) [ev] = []’
    by (rewrite_tac[ep_fold_def] >> qpat_x_assum ‘send_fd ev = _’ (fn th => rewrite_tac[th]) >>
        simp_tac (srw_ss()) []) >>
  simp[forget_keys] >>
  ‘∀g. ALOOKUP b.tbl (l1hdl lfd j) = SOME g ⇒ g ≠ f’
    by (rpt strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
        gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘SND (l0_ep_step (k, opn) ev) = opn ∨ SND (l0_ep_step (k, opn) ev) = ADELKEY f opn’
    by (simp[l0_ep_step_def] >> every_case_tac >> gvs[]) >>
  (Cases_on ‘epfd opn j = SOME f’
   >- ((* j's own fd: closed *)
       ‘¬live lfd (ps with b := forget f b) j ∧
        obp lfd (ps with b := forget f b) (SND (l0_ep_step (k, opn) ev)) j = []’
         by (simp[live_def, obp_def, forget_keys, MEM_FILTER] >> conj_tac
             >- (rpt strip_tac >> ‘epfd opn j = SOME f'’ by (irule tbl_epfd >>
                   qexistsl [‘k’, ‘lfd’, ‘ps with b := b’] >> fs[]) >> gvs[] >> metis_tac[]) >>
             every_case_tac >> gvs[] >>
             TRY (drule_all epfd_ADELKEY >> strip_tac >> gvs[]) >> metis_tac[]) >>
       gvs[oi_def] >> imp_res_tac isPREFIX_APPEND_L >> fs[]) >>
   ‘epfd (SND (l0_ep_step (k, opn) ev)) j = epfd opn j’
     by (gvs[] >> metis_tac[epfd_ADELKEY_ne]) >>
   ‘obp lfd (ps with b := forget f b) (SND (l0_ep_step (k, opn) ev)) j =
    obp lfd (ps with b := b) opn j ∧
    (live lfd (ps with b := forget f b) j ⇔ live lfd (ps with b := b) j)’
     by (irule obp_frame >> simp[forget_keys, MEM_FILTER] >> rpt strip_tac >> gvs[] >>
         metis_tac[]) >>
   gvs[oi_def])
QED

(* The reap *)
Theorem l1_reap_out:
  ∀fs w b w' b' evs opn snt.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ okb b ∧
    own_ok lfd (k, opn) (ps with b := b) ∧ b.nxt < dimword (:64) ∧
    hdln (w2n lfd) j < dimword (:64) ∧
    (∀f. MEM f fs ⇒ ¬MEM f (MAP SND b.tbl) ∧ ¬MEM f ps.acq) ∧
    oi lfd (ps with b := b) opn snt hwt j ⇒
    okb b' ∧ b'.tbl = b.tbl ∧ b'.nxt = b.nxt ∧
    oi lfd (ps with b := b') (SND (l0_ep_st (k, opn) evs)) (snt ++ ep_sn j (k, opn) evs) hwt j
Proof
  Induct >> simp[l1_reap_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  ‘b.nxt < dimword (:64) ∧ hdln (w2n lfd) j < dimword (:64)’ by fs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> simp[]
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      PairCases_on ‘ws’ >> gvs[] >>
      rename1 ‘l1_close h (w, b) = SOME ((w1, b1), evs1)’ >>
      ‘b.nxt < dimword (:64) ∧ hdln (w2n lfd) j < dimword (:64)’ by fs[] >>
      ‘¬MEM h (MAP SND b.tbl) ∧ ¬MEM h ps.acq’ by metis_tac[] >>
      drule_all close_out >> strip_tac >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      ‘l0_rely w1’ by (gvs[sys_close_def] >> metis_tac[l0_do_rely]) >>
      ‘own_ok lfd (k, opn) (ps with b := forget h b) ∧
       own_ok lfd (k, ADELKEY h opn) (ps with b := forget h b)’
        by (irule own_forget >> simp[]) >>
      ‘FST (l0_ep_step (k, opn) ev) = k ∧
       (SND (l0_ep_step (k, opn) ev) = opn ∨ SND (l0_ep_step (k, opn) ev) = ADELKEY h opn)’
        by (‘l0_rely w’ by simp[] >> drule_all sys_close_event >> strip_tac >>
            simp[l0_ep_step_def] >> every_case_tac >> gvs[]) >>
      Cases_on ‘l0_ep_step (k, opn) ev’ >> gvs[] >>
      ‘ep_sn j (k, opn) (ev :: evs'') =
       ep_sn j (k, opn) [ev] ++ ep_sn j (l0_ep_step (k, opn) ev) evs''’
        by rewrite_tac[ep_fold_def, APPEND_NIL] >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      qpat_assum ‘l0_ep_step _ _ = _’ (fn th => REWRITE_TAC [th]) >>
      first_x_assum (drule_at (Pos (el 1))) >> simp[] >>
      disch_then (qspecl_then [‘SND (l0_ep_step (k, opn) ev)’,
                               ‘snt ++ ep_sn j (k, opn) [ev]’] mp_tac) >>
      qpat_x_assum ‘l0_ep_step _ _ = _’ (fn th => REWRITE_TAC [th]) >> simp[] >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp[]) >>
  strip_tac >> first_x_assum (qspecl_then [‘w’, ‘b’, ‘w'’, ‘b'’, ‘evs’, ‘opn’, ‘snt’] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >> simp[]
QED

(* An accept of a fd L1 does not hold opens episode k with no bytes, and
   ends any stale binding of that fd (which held no bytes either) *)
Theorem obp_accept:
  ep_ok (k, opn) ∧ ¬MEM g (MAP SND ps.b.tbl) ∧ ¬MEM g ps.b.closing ⇒
  obp lfd ps ((g, k) :: ADELKEY g opn) j = obp lfd ps opn j
Proof
  strip_tac >>
  ‘∀x. ALOOKUP ps.b.tbl x ≠ SOME g’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  Cases_on ‘j = k’
  >- (‘epfd opn k = NONE’
        by (Cases_on ‘epfd opn k’ >> simp[] >>
            drule_then (qspecl_then [‘k’, ‘x’] mp_tac) epfd_iff >> simp[] >> strip_tac >>
            gvs[ep_ok_def, EVERY_MEM] >> imp_res_tac ALOOKUP_MEM >>
            gvs[MEM_MAP, EXISTS_PROD] >> res_tac >> fs[]) >>
      simp[obp_def] >> simp[epfd_def] >> fs[]) >>
  ‘epfd ((g, k) :: ADELKEY g opn) j = epfd (ADELKEY g opn) j’ by simp[epfd_def] >>
  simp[obp_def] >>
  Cases_on ‘epfd opn j = SOME g’
  >- (‘epfd (ADELKEY g opn) j = NONE’
        by (Cases_on ‘epfd (ADELKEY g opn) j’ >> simp[] >> drule_all epfd_ADELKEY >> simp[]) >>
      simp[] >> fs[]) >>
  drule_all epfd_ADELKEY_ne >> simp[]
QED

(* The fetch sends nothing and moves no output *)
Theorem pf_fetch_obp:
  ∀fs w ps k opn w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ fds_lt w ∧
    ep_ok (k, opn) ∧
    (∀f. MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing ⇒ MEM f (l0_used w)) ⇒
    ps'.b = ps.b ∧ (∀j. ep_sn j (k, opn) evs = []) ∧
    ∀j. obp lfd ps' (SND (l0_ep_st (k, opn) evs)) j = obp lfd ps opn j
Proof
  Induct >- (rw[pf_fetch_def] >> simp[ep_fold_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once pf_fetch_def] >> IF_CASES_TAC >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC >> simp[]
  >- (Cases_on ‘sys_accept lfd w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, w1, ev)’ >>
      pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      drule_all sys_accept_event >> strip_tac >>
      ‘l0_rely w1 ∧ fds_lt w1’
        by (gvs[sys_accept_def] >>
            metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_accept» = «sys_connect»”]) >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)’
        by (gvs[sys_accept_def] >> drule l0_do_used >> simp[]) >>
      ‘ps1.b = ps.b’ by (every_case_tac >> gvs[]) >>
      ‘∃k1 opn1. l0_ep_step (k, opn) ev = (k1, opn1)’ by metis_tac[PAIR] >>
      ‘ep_ok (k1, opn1)’ by metis_tac[ep_ok_step] >>
      first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘k1’, ‘opn1’] mp_tac) >> simp[] >>
      impl_tac >- metis_tac[] >> strip_tac >>
      ‘∀j. ep_sn j (k, opn) (ev :: evs') =
           ep_sn j (k, opn) [ev] ++ ep_sn j (l0_ep_step (k, opn) ev) evs'’
        by rewrite_tac[ep_fold_def, APPEND_NIL] >>
      ‘∀j. ep_sn j (k, opn) [ev] = []’ by simp[ep_fold_def] >>
      ‘∀j. obp lfd ps1 opn1 j = obp lfd ps opn j’
        by (gen_tac >>
            ‘obp lfd ps1 opn1 j = obp lfd ps opn1 j’ by simp[obp_def] >> simp[] >>
            Cases_on ‘l0_res_of out’ >> gvs[l0_ep_step_def] >>
            rename1 ‘l0_res_of out = Ok kk’ >>
            drule_all sys_accept_fresh >> strip_tac >>
            irule obp_accept >> simp[] >> metis_tac[]) >>
      gvs[]) >>
  Cases_on ‘sys_recv h pf_chunk w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
  rename1 ‘sys_recv h pf_chunk w = SOME (out, w1, ev)’ >>
  pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule_all sys_recv_event >> strip_tac >>
  ‘l0_rely w1 ∧ fds_lt w1 ∧ l0_used w1 = l0_used w’
    by (gvs[sys_recv_def] >> imp_res_tac l0_do_used >> gvs[] >>
        metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_recv» = «sys_connect»”]) >>
  ‘ps1.b = ps.b’ by (every_case_tac >> gvs[set_inb_def]) >>
  ‘l0_ep_step (k, opn) ev = (k, opn)’ by simp[l0_ep_step_def] >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘k’, ‘opn’] mp_tac) >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  ‘∀j. obp lfd ps1 opn j = obp lfd ps opn j’ by simp[obp_def] >>
  gvs[ep_fold_def]
QED

Theorem polls_sn:
  ∀cs w rv w' evs. l1_polls cs w = SOME (rv, w', evs) ∧ l0_rely w ⇒ ∀j s. ep_sn j s evs = []
Proof
  Induct >> simp[l1_polls_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> drule_all sys_poll_event >> strip_tac >>
  first_x_assum drule_all >> simp[ep_fold_def]
QED

Theorem oi_obp:
  ps'.b = ps.b ∧ (∀j. obp lfd ps' opn' j = obp lfd ps opn j) ∧ oi lfd ps opn s h j ⇒
  oi lfd ps' opn' s h j
Proof
  rw[oi_def, live_def]
QED

Theorem l1p_b_id[local]:
  (ps : l1p) with b := ps.b = ps
Proof
  simp[l1p_component_equality]
QED

(* MAIN, the tail of a round *)
Theorem pf_tail_out:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt < dimword (:64) ∧ okb ps.b ∧
  hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
  okb ps'.b ∧
  oi lfd ps' (SND (l0_ep_st (k, opn) evs)) (snt ++ ep_sn j (k, opn) evs) hwt j
Proof
  strip_tac >> qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[wown_def] >>
  ‘ep_ok (k, opn) ∧ k ≤ ps.b.nxt + 1’ by gvs[own_ok_def] >>
  (* poll *)
  drule_all l1_polls_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  ‘∀j s. ep_sn j s pevs = []’ by (drule_all polls_sn >> simp[]) >>
  drule_all l1_polls_wown >> strip_tac >>
  (* flush *)
  drule_all l1_flush_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  ‘wown lfd w2 (ps with b := b2)’ by (irule l1_flush_wown >> metis_tac[]) >>
  ‘own_ok lfd (k, opn) (ps with b := b2)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := b2’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[]) >>
  ‘own_ok lfd (k, opn) (ps with b := ps.b) ∧ oi lfd (ps with b := ps.b) opn snt hwt j’
    by simp[l1p_b_id] >>
  drule_all l1_flush_out >> strip_tac >>
  (* fetch *)
  ‘fds_lt w2 ∧ (∀f. MEM f (MAP SND b2.tbl) ∨ MEM f b2.closing ⇒ MEM f (l0_used w2))’
    by (gvs[wown_def, owned_def] >> metis_tac[]) >>
  qspecl_then [‘FILTER (λf. MEM f (in_fds (pf_poll_set lfd hw ps hs))) (readable_fds rv)’,
               ‘w2’, ‘ps with b := b2’, ‘k’, ‘opn’, ‘w3’, ‘ps3'’, ‘log’, ‘gevs’]
    mp_tac pf_fetch_obp >> simp[] >>
  (impl_tac >- (qpat_x_assum ‘∀f. MEM f (MAP SND b2.tbl) ∨ _ ⇒ _’ mp_tac >> gvs[])) >>
  strip_tac >>
  drule pf_fetch_in >>
  disch_then (qspecl_then [‘k’, ‘opn’] mp_tac) >> simp[] >>
  impl_tac
  >- (rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
  strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) gevs’ >> rename1 ‘l0_ep_st _ gevs = (k3, opn3)’ >>
  ‘oi lfd ps3' opn3 (snt ++ ep_sn j (k, opn) fevs) hwt j’
    by (irule oi_obp >> qexistsl [‘opn’, ‘ps with b := b2’] >> gvs[]) >>
  (* hung up *)
  ‘k3 ≤ ps.b.nxt + 1 ∧ ps3'.b.nxt < dimword (:64)’
    by (‘ps3'.b.nxt = ps.b.nxt’ by gvs[] >> gvs[own_ok_def]) >>
  ‘okb ps3'.b’ by gvs[] >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  ‘okb ps3.b ∧ oi lfd ps3 opn3 (snt ++ ep_sn j (k, opn) fevs) hwt j’
    by (simp[Abbr ‘ps3’] >> irule stall_out >> simp[] >> qexists_tac ‘k3’ >> fs[]) >>
  ‘own_ok lfd (k3, opn3) ps3 ∧ wown lfd w3 ps3’
    by (simp[Abbr ‘ps3’, stall_step_in] >> qpat_x_assum ‘wown _ w3 _’ mp_tac >>
        simp[wown_def, owned_def] >> metis_tac[]) >>
  (* reap *)
  ‘∀f. MEM f ps3.b.closing ⇒ ¬MEM f (MAP SND ps3.b.tbl) ∧ ¬MEM f ps3.acq’
    by (rpt gen_tac >> strip_tac >> drule_all own_closing_free >> simp[]) >>
  ‘l1_reap ps3.b.closing (w3, ps3.b) = SOME ((w4, b4), cevs)’
    by gvs[Abbr ‘ps3’] >>
  ‘l0_rely w3’ by gvs[wown_def] >>
  qspecl_then [‘ps3.b.closing’, ‘w3’, ‘ps3.b’, ‘w4’, ‘b4’, ‘cevs’, ‘opn3’,
               ‘snt ++ ep_sn j (k, opn) fevs’]
    mp_tac (Q.INST [‘ps’ |-> ‘ps3’, ‘k’ |-> ‘k3’] l1_reap_out) >>
  simp[l1p_b_id] >> impl_tac >- (simp[Abbr ‘ps3’] >> fs[]) >> strip_tac >>
  (* the round's tail *)
  qpat_x_assum ‘_ = ps'’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘_ = evs’ (SUBST_ALL_TAC o SYM) >>
  simp[ep_fold_APPEND] >>
  ‘oi lfd (ps3 with <|b := b4; pause := ps3'.pause − 1|>) =
   oi lfd (ps3 with b := b4)’ by (irule oi_b >> simp[]) >>
  gvs[]
QED

(* Nothing is held for an episode whose handle is not yet handed out, so
   the invariant holds trivially of nothing sent and the bytes held *)
Theorem obp_unhanded:
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒
  obp lfd ps opn j = []
Proof
  strip_tac >> simp[obp_def] >> Cases_on ‘epfd opn j’ >> simp[] >>
  rename1 ‘epfd opn j = SOME f’ >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  ‘ALOOKUP opn f = SOME j’ by (drule_then (qspecl_then [‘j’, ‘f’] mp_tac) epfd_iff >> simp[]) >>
  IF_CASES_TAC >> simp[] >> pop_assum strip_assume_tac
  >- (‘ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME f’ by simp[] >>
      drule_all own_tbl_lookup >> strip_tac >>
      qmatch_asmsub_rename_tac ‘l1hdl lfd j = l1hdl lfd jj’ >>
      ‘jj < k’ by (qpat_x_assum ‘own_ok _ _ _’ mp_tac >> simp[own_ok_def]) >>
      ‘hdln (w2n lfd) jj < dimword (:64)’ by HB ‘ps.b.nxt’ >>
      ‘hdl lfd j = hdl lfd jj ⇔ j = jj’ by (irule hdl_eq_iff >> fs[]) >> fs[]) >>
  qpat_x_assum ‘own_ok _ _ _’ mp_tac >> simp[own_ok_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> fs[]
QED

(* Nothing is held for an episode whose handle is not yet handed out, so
   the invariant holds trivially of nothing sent and the bytes held *)
Theorem oi_triv:
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ⇒
  oi lfd ps opn [] (obp lfd ps opn j) j
Proof
  strip_tac >> simp[oi_def] >> strip_tac >>
  irule obp_unhanded >> simp[] >> qexists_tac ‘k’ >> fs[]
QED

(* MAIN: a round, per episode in range: what the spec says it sent in
   the round, after the bytes L1 held for it, is what the server wrote in
   the round, up to what L1 now holds (exactly, while it is live) *)
Theorem pround_out:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧ okb ps.b ∧
  ps.b.nxt + naccepts acts < dimword (:64) ∧
  (∀j. hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒
       FLAT (MAP (wr (l1hdl lfd j)) acts) = []) ⇒
  okb ps'.b ∧
  ∀j snt hwt. hdln (w2n lfd) j < dimword (:64) ∧ oi lfd ps opn snt hwt j ⇒
    oi lfd ps' (SND (l0_ep_st (k, opn) evs)) (snt ++ ep_sn j (k, opn) evs)
       (hwt ++ FLAT (MAP (wr (l1hdl lfd j)) acts)) j
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘pf_tail _ _ _ _ = SOME (rdy, _, log2, tevs)’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  ‘k ≤ ps.b.nxt + 1’ by gvs[own_ok_def] >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule_all pacts_out >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> rename1 ‘l0_ep_st _ _ = (k1, opn1)’ >> gvs[] >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by (drule pacts_nxt_acc >> fs[]) >>
  drule pf_tail_out >> simp[] >> strip_tac >>
  ‘hdln (w2n lfd) 0 < dimword (:64)’ by rw[hdln_def] >>
  conj_tac
  >- (first_x_assum (qspecl_then [‘[]’, ‘opn1’, ‘k’, ‘0’, ‘obp lfd ws11 opn1 0’] mp_tac) >>
      simp[] >> impl_tac
      >- (fs[] >> irule oi_triv >> fs[] >> qexists_tac ‘k’ >> fs[]) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum ‘∀j snt hwt. _ ∧ oi lfd ps opn _ _ _ ⇒ _’ drule_all >> strip_tac >>
  first_x_assum (qspecl_then [‘snt ++ ep_sn j (k, opn) evs1’, ‘opn1’, ‘k’, ‘j’,
                              ‘hwt ++ FLAT (MAP (wr (l1hdl lfd j)) acts)’] mp_tac) >>
  simp[ep_fold_APPEND]
QED

Theorem set_outbox_nfields:
  (set_outbox f bs st).tbl = st.tbl ∧ (set_outbox f bs st).nxt = st.nxt ∧
  (set_outbox f bs st).closing = st.closing
Proof
  simp[set_outbox_def]
QED

(* A write keeps the outboxes on held fds *)
Theorem pdo_write_okb:
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs) ∧ okb ps.b ⇒ okb ps'.b
Proof
  simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >> PairCases_on ‘z’ >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[] >> rename1 ‘ALOOKUP _ h = SOME f’ >>
  ‘MEM f (MAP SND ps.b.tbl)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  TRY (irule okb_after_send >> simp[set_outbox_nfields]) >>
  irule okb_set_outbox >> simp[]
QED

(* The round's actions keep the outboxes on held fds *)
Theorem pacts_okb:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ∧ okb ps.b ⇒
    okb ps'.b
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘ps.b.nxt < dimword (:64)’ by simp[] >>
  ‘ps1.b.nxt + naccepts acts < dimword (:64)’
    by (drule pdo_nxt_acc >>
        ‘naccepts (a :: acts) = naccepts [a] + naccepts acts’ by (Cases_on ‘a’ >> simp[]) >>
        fs[]) >>
  ‘okb ps1.b’
    by (Cases_on ‘a’
        >- (drule_all pdo_accept_out >> simp[])
        >- (drule_all pdo_read_out >> simp[])
        >> drule_all pdo_write_okb >> simp[]) >>
  drule_all pdo_in >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

