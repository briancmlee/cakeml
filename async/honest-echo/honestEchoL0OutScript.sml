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
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round
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

(* L1's outboxes: only held fds have one or are gone, and a gone fd has none *)
Definition okb_def:
  okb (b : l1st) ⇔
    ∀f. (outbox_of b f ≠ [] ∨ MEM f b.gone ⇒ MEM f (MAP SND b.tbl) ∨ MEM f b.closing) ∧
        (MEM f b.gone ⇒ outbox_of b f = [])
End

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

(* Episode j's handle holds j's fd *)
Theorem own_epfd:
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧
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
  rw[okb_def] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem okb_after_send:
  okb b ∧ (MEM f (MAP SND b.tbl) ∨ MEM f b.closing) ⇒ okb (after_send f r b)
Proof
  rw[after_send_def] >> every_case_tac >> gvs[]
  >- (irule okb_set_outbox >> gvs[okb_def])
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
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧ okb ps.b ∧
  (∀j. hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒ h ≠ l1hdl lfd j) ⇒
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
      rpt strip_tac >> qpat_x_assum ‘∀j'. _ ⇒ _ ≠ _’ (qspec_then ‘j’ mp_tac) >> fs[]) >>
  gvs[] >>
  drule_all own_tbl_lookup >> strip_tac >> rename1 ‘h = l1hdl lfd i’ >>
  ‘i < k’ by gvs[own_ok_def] >>
  ‘epfd opn i = SOME f’ by metis_tac[epfd_iff] >>
  ‘hdln (w2n lfd) i < dimword (:64)’ by (irule hdln_mono >> qexists_tac ‘k’ >> simp[]) >>
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
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧ okb ps.b ⇒
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
  ‘outbox_of ps.b f = [] ∧ ¬MEM f ps.b.gone’ by (gvs[okb_def] >> metis_tac[]) >>
  ‘ps.b.nxt < k’ by gvs[own_ok_def] >>
  ‘hdln (w2n l) ps.b.nxt < dimword (:64)’
    by (irule hdln_mono >> qexists_tac ‘k’ >> fs[]) >>
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
  own_ok lfd (k, opn) ps ∧ hdln (w2n lfd) k < dimword (:64) ∧ okb ps.b ⇒
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
  ‘hdln (w2n lfd) i < dimword (:64)’ by (irule hdln_mono >> qexists_tac ‘k’ >> simp[]) >>
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
