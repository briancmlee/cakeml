(*
  E1, the output side (moonshot step 12, C1(ii)): what L1 has sent on an
  episode's fd, on the raw trace, is what the layer's channel was written,
  up to L1's outbox; a prefix of it once L1 dropped the outbox (gone).

  Stated on the trace (the sys_send events' taken bytes, honestL1PFOut's
  ev_sent), so it needs no L0 world invariant beyond l0_rely, and E1's
  connecting channels are no obstacle.
*)
Theory honestL1EPOut
Ancestors
  honestL1EPModel honestL1PFOut honestL1PFRefine honestL1PFRound honestL1PFModel
  honestL1Steps honestL1Props honestL1Model honestL0WorldProps honestL0Rely honestL0World
  endpointHLModel endpointWorld
Libs
  preamble

(* A send event's bytes on f *)
Theorem sys_send_tsent:
  sys_send g bs w = SOME (out, w', ev) ∧ l0_rely w ⇒
  l0_rely w' ∧
  ∀f. ev_sent f ev = (if g = f then (case l0_res_of out of Ok k => TAKE k bs | Fail _ _ => [])
                      else [])
Proof
  rw[sys_send_def] >>
  ‘LENGTH out = 13 ∧ l0_rely w'’
    by (gvs[l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[ev_sent_def, taken_def, MAP_SND_ZIP_REPLICATE] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  simp[TAKE_APPEND1, DROP_APPEND1, TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL_rwt] >> rw[]
QED

(* The flush: per fd, the bytes sent leave the outbox; a fd dropped (gone)
   keeps a prefix *)
Theorem l1_flush_tsent:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒
    l0_rely w' ∧
    (MEM f b.gone ⇒ evs_sent f evs = [] ∧ MEM f b'.gone ∧ outbox_of b' f = outbox_of b f) ∧
    (¬MEM f b.gone ⇒
       (¬MEM f b'.gone ⇒ evs_sent f evs ++ outbox_of b' f = outbox_of b f) ∧
       (MEM f b'.gone ⇒ evs_sent f evs ≼ outbox_of b f ∧ outbox_of b' f = []))
Proof
  Induct >- simp[l1_flush_def] >>
  rpt gen_tac >> simp[Once l1_flush_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘sys_send h _ w = SOME (out, w1, ev)’ >>
  drule_all sys_send_tsent >> strip_tac >> pop_assum (qspec_then ‘f’ assume_tac) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  Cases_on ‘h = f’ >> gvs[]
  >- (Cases_on ‘l0_res_of out’ >> gvs[after_send_def, outbox_of_set_outbox] >>
      TRY (rename1 ‘l1_transient e’ >> Cases_on ‘l1_transient e’ >> gvs[outbox_of_set_outbox, MEM_FILTER]) >>
      rw[] >> gvs[outbox_of_set_outbox, MEM_FILTER] >>
      metis_tac[TAKE_DROP, rich_listTheory.IS_PREFIX_APPEND3, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  ‘outbox_of (after_send h (l0_res_of out) b) f = outbox_of b f ∧
   (MEM f (after_send h (l0_res_of out) b).gone ⇔ MEM f b.gone)’
    by (simp[after_send_def] >> every_case_tac >> simp[outbox_of_set_outbox, MEM_FILTER]) >>
  gvs[]
QED

(* ------------------------------------------------------------------------
   One fd, across a step of L1: events evs, the program wrote adw on it
   ------------------------------------------------------------------------ *)

Definition ostep_def:
  ostep f (b : l1st) (b' : l1st) evs adw ⇔
    (MEM f b.gone ⇒ MEM f b'.gone ∧ evs_sent f evs = []) ∧
    (¬MEM f b.gone ⇒
       (¬MEM f b'.gone ⇒ evs_sent f evs ++ outbox_of b' f = outbox_of b f ++ adw) ∧
       (MEM f b'.gone ⇒ evs_sent f evs ≼ outbox_of b f ++ adw))
End

(* The account of fd f's episode: raw sent so far, L1's outbox, and the
   layer's channel's bytes *)
Definition oacct_def:
  oacct raw (b : l1st) f hl ⇔
    (¬MEM f b.gone ⇒ raw ++ outbox_of b f = hl) ∧ (MEM f b.gone ⇒ raw ≼ hl)
End

Theorem ostep_trans:
  ostep f b1 b2 e1 a1 ∧ ostep f b2 b3 e2 a2 ⇒ ostep f b1 b3 (e1 ++ e2) (a1 ++ a2)
Proof
  rw[ostep_def] >>
  Cases_on ‘MEM f b1.gone’ >> Cases_on ‘MEM f b2.gone’ >> Cases_on ‘MEM f b3.gone’ >>
  gvs[] >> fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem ostep_acct:
  oacct raw b f hl ∧ ostep f b b' evs adw ⇒ oacct (raw ++ evs_sent f evs) b' f (hl ++ adw)
Proof
  rw[oacct_def, ostep_def] >>
  Cases_on ‘MEM f b.gone’ >> Cases_on ‘MEM f b'.gone’ >>
  gvs[] >> fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem oacct_prefix:
  oacct raw b f hl ⇒ raw ≼ hl
Proof
  rw[oacct_def] >> Cases_on ‘MEM f b.gone’ >> gvs[]
QED

(* A step that sends nothing on f and leaves its outbox and gone status *)
Theorem ostep_quiet:
  evs_sent f evs = [] ∧ outbox_of b' f = outbox_of b f ∧ (MEM f b'.gone ⇔ MEM f b.gone) ⇒
  ostep f b b' evs []
Proof
  rw[ostep_def]
QED

Theorem l1_flush_ostep:
  l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒ l0_rely w' ∧ ostep f b b' evs []
Proof
  strip_tac >> drule_all l1_flush_tsent >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  simp[ostep_def] >> rw[] >> gvs[]
QED

Theorem after_send_other:
  g ≠ f ⇒ outbox_of (after_send g r st) f = outbox_of st f ∧
          (MEM f (after_send g r st).gone ⇔ MEM f st.gone)
Proof
  simp[after_send_def] >> every_case_tac >> simp[outbox_of_set_outbox, MEM_FILTER]
QED

Theorem pdo_write_ostep:
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs) ∧ l0_rely w ⇒
  l0_rely w' ∧ ∀f. ostep f ps.b ps'.b evs (wbytes f ps.b (Write h bs))
Proof
  simp[pdo_def, l1do_def] >> strip_tac >> gvs[AllCaseEqs()]
  >~ [‘sys_send _ _ _ = SOME _’]
  >- (drule_all sys_send_tsent >> strip_tac >> simp[] >> gen_tac >>
      rename1 ‘ostep g _ _ _ _’ >>
      first_x_assum (qspec_then ‘g’ assume_tac) >>
      Cases_on ‘g = f’ >> fs[]
      >- (simp[ostep_def, wbytes_def] >>
          Cases_on ‘l0_res_of out’ >> fs[after_send_def, outbox_of_set_outbox] >>
          rename1 ‘Fail e _’ >> Cases_on ‘l1_transient e’ >>
          fs[outbox_of_set_outbox, MEM_FILTER]) >>
      simp[ostep_def, wbytes_def, after_send_other, outbox_of_set_outbox]) >>
  gen_tac >> simp[ostep_def, wbytes_def, outbox_of_set_outbox] >>
  Cases_on ‘f' = f’ >> simp[]
QED

(* An fd that L1 stops holding during the step (closed): what was sent is
   a prefix of what it had to send *)
Definition ostepc_def:
  ostepc f (b : l1st) evs adw ⇔
    (¬MEM f b.gone ⇒ evs_sent f evs ≼ outbox_of b f ++ adw) ∧
    (MEM f b.gone ⇒ evs_sent f evs = [])
End

Theorem ostep_ostepc:
  ostep f b b' evs adw ⇒ ostepc f b evs adw
Proof
  rw[ostep_def, ostepc_def] >> Cases_on ‘MEM f b'.gone’ >> gvs[] >>
  metis_tac[rich_listTheory.IS_PREFIX_APPEND3, IS_PREFIX_REFL]
QED

Theorem ostep_ostepc_trans:
  ostep f b1 b2 e1 a1 ∧ ostepc f b2 e2 a2 ⇒ ostepc f b1 (e1 ++ e2) (a1 ++ a2)
Proof
  rw[ostep_def, ostepc_def] >>
  Cases_on ‘MEM f b1.gone’ >> Cases_on ‘MEM f b2.gone’ >>
  gvs[] >> fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem ostepc_quiet:
  ostepc f b e1 a1 ∧ evs_sent f e2 = [] ⇒ ostepc f b (e1 ++ e2) (a1 ++ a2)
Proof
  rw[ostepc_def] >> gvs[] >> fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem ostepc_acct:
  oacct raw b f hl ∧ ostepc f b evs adw ⇒ raw ++ evs_sent f evs ≼ hl ++ adw
Proof
  rw[oacct_def, ostepc_def] >> Cases_on ‘MEM f b.gone’ >> gvs[] >>
  fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem sys_close_quiet:
  sys_close g w = SOME (out, w', ev) ⇒ ∀f. ev_sent f ev = []
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[ev_sent_def]
QED

Theorem forget_other:
  g ≠ f ⇒ outbox_of (forget g st) f = outbox_of st f ∧
          (MEM f (forget g st).gone ⇔ MEM f st.gone) ∧
          (MEM f (forget g st).closing ⇔ MEM f st.closing) ∧
          (forget g st).tbl = st.tbl
Proof
  rw[forget_def, outbox_of_set_outbox, MEM_FILTER] >> simp[set_outbox_def, MEM_FILTER, outbox_of_def]
QED

Theorem l1_close_ostep:
  l1_close g (w, b) = SOME ((w', b'), evs) ⇒
  (l0_rely w ⇒ l0_rely w') ∧ (∀f. evs_sent f evs = []) ∧ (∀f. f ≠ g ⇒ ostep f b b' evs []) ∧
  b'.tbl = b.tbl ∧ (∀f. MEM f b'.closing ⇔ MEM f b.closing ∧ f ≠ g)
Proof
  simp[l1_close_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule sys_close_quiet >> strip_tac >> gvs[] >>
  conj_tac >- (gvs[sys_close_def] >> metis_tac[l0_do_rely]) >>
  simp[ostep_def, forget_other] >> simp[forget_def, MEM_FILTER] >> metis_tac[]
QED

(* The fds L1 holds *)
Definition held_def:
  held (b : l1st) f ⇔ MEM f (MAP SND b.tbl) ∨ MEM f b.closing
End

(* Reads and accepts send nothing; an fd still held keeps its account; the
   auto-closed one ends *)
Theorem ADELKEY_SND_distinct:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l h = SOME f ⇒ ¬MEM f (MAP SND (ADELKEY h l))
Proof
  Induct >> simp[FORALL_PROD, ADELKEY_def] >> rw[] >> gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[]
QED

Theorem pdo_read_ostep:
  pdo lfd (w, ps) (Read h n) = SOME (r, (w', ps'), evs) ∧ pown lfd ps ⇒
  (l0_rely w ⇒ l0_rely w') ∧ (∀f. evs_sent f evs = []) ∧
  ∀f. held ps.b f ⇒ (held ps'.b f ⇒ ostep f ps.b ps'.b evs []) ∧ ostepc f ps.b evs []
Proof
  simp[pdo_def] >> rw[] >> gvs[AllCaseEqs()] >>
  TRY (simp[ostep_def, ostepc_def, set_inb_def] >> NO_TAC) >>
  TRY (simp[ostep_def, ostepc_def] >> rw[] >> NO_TAC) >>
  PairCases_on ‘z’ >> gvs[] >> drule l1_close_ostep >> strip_tac >>
  TRY (simp[ostepc_def] >> NO_TAC) >>
  ‘ALL_DISTINCT (MAP SND ps.b.tbl) ∧ ¬MEM f' ps.b.closing’
    by (gvs[honestL1PFRefineTheory.pown_def, ALL_DISTINCT_APPEND] >> imp_res_tac ALOOKUP_MEM >>
        gvs[MEM_MAP] >> metis_tac[SND]) >>
  ‘f ≠ f'’
    by (strip_tac >> qpat_x_assum ‘held z1 _’ mp_tac >> simp[held_def] >>
        qpat_x_assum ‘z1.tbl = _’ (fn th => simp[th]) >>
        qpat_x_assum ‘∀f. MEM f z1.closing ⇔ _’ (fn th => simp[th]) >>
        gvs[] >> metis_tac[ADELKEY_SND_distinct]) >>
  qpat_x_assum ‘∀f. _ ⇒ ostep _ _ _ _ _’ (qspec_then ‘f’ mp_tac) >> simp[ostep_def]
QED

Theorem pdo_accept_ostep:
  pdo lfd (w, ps) (Accept l) = SOME (r, (w', ps'), evs) ⇒
  evs = [] ∧ w' = w ∧ ps'.b.closing = ps.b.closing ∧ ps'.b.gone = ps.b.gone ∧
  ps'.b.outbox = ps.b.outbox ∧
  (ps'.b.tbl = ps.b.tbl ∧ ps'.acq = ps.acq ∨
   ∃h. ps'.b.tbl = (h, HD ps.acq) :: ps.b.tbl ∧ ps.acq = HD ps.acq :: ps'.acq)
Proof
  simp[pdo_def] >> rw[] >> gvs[AllCaseEqs()]
QED

Theorem sys_connect_quiet:
  sys_connect p w = SOME (out, w', ev) ⇒ ∀f. ev_sent f ev = []
Proof
  rw[sys_connect_def] >> drule l0_do_cases >> rw[] >> simp[ev_sent_def]
QED

(* What an E1 action writes on fd f (a connect handle's writes take
   nothing: pending is a misuse, refused takes 0) *)
Definition ewbytes_def:
  ewbytes f (es : l1e) (EWrite h bs) = (if ALOOKUP es.p.b.tbl h = SOME f then bs else []) ∧
  ewbytes f es (ERead h n) = [] ∧ ewbytes f es (EAccept l) = [] ∧
  ewbytes f es (EConnect a) = [] ∧ ewbytes f es (ELevel h) = []
End

(* What the output side needs of L1's own invariant (E1's eown implies it) *)
Definition oown_def:
  oown lfd (es : l1e) ⇔
    pown lfd es.p ∧
    ALL_DISTINCT (MAP SND es.p.b.tbl ++ es.p.b.closing ++ MAP SND es.ctbl) ∧
    ALL_DISTINCT (MAP FST es.p.b.tbl ++ MAP FST es.ctbl)
End

Theorem eown_ctbl_held:
  oown lfd es ∧ MEM f (MAP SND es.ctbl) ⇒ ¬held es.p.b f
Proof
  rw[oown_def, held_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem eown_ctbl_lookup:
  oown lfd es ∧ ALOOKUP es.ctbl h = SOME f0 ∧ held es.p.b g ⇒ g ≠ f0
Proof
  rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
  ‘MEM f0 (MAP SND es.ctbl)’ by (simp[MEM_MAP] >> metis_tac[SND]) >>
  metis_tac[eown_ctbl_held]
QED

Theorem edo_ostep:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ oown lfd es ∧ l0_rely w ⇒
  l0_rely w' ∧
  ∀f. held es.p.b f ⇒
      (held es'.p.b f ⇒ ostep f es.p.b es'.p.b evs (ewbytes f es a)) ∧
      ostepc f es.p.b evs (ewbytes f es a)
Proof
  strip_tac >> ‘pown lfd es.p’ by fs[oown_def] >>
  Cases_on ‘a’ >> gvs[edo_def, AllCaseEqs()]
  (* EAccept *)
  >~ [‘pdo _ _ (Accept _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_accept_ostep >> strip_tac >> gvs[] >>
      simp[ostep_def, ostepc_def, ewbytes_def, outbox_of_def])
  (* ERead on a layer handle *)
  >~ [‘pdo _ _ (Read _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_read_ostep >> strip_tac >>
      simp[ewbytes_def] >> rpt strip_tac >> res_tac)
  (* EWrite on a layer handle *)
  >~ [‘pdo _ _ (Write _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_write_ostep >> strip_tac >>
      simp[ewbytes_def] >> rpt strip_tac >>
      first_x_assum (qspec_then ‘f’ assume_tac) >> gvs[wbytes_def] >>
      metis_tac[ostep_ostepc])
  (* a refused connect handle, read: closed *)
  >~ [‘l1_close _ _ = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule l1_close_ostep >> strip_tac >>
      simp[ec_del_def, ewbytes_def] >> rpt strip_tac >>
      metis_tac[ostep_ostepc, eown_ctbl_lookup])
  (* EConnect *)
  >~ [‘sys_connect _ _ = _’]
  >- (drule sys_connect_quiet >> strip_tac >>
      ‘l0_rely w'’ by (gvs[sys_connect_def] >> metis_tac[l0_do_rely]) >>
      simp[ostep_def, ostepc_def, ewbytes_def, outbox_of_def] >> rw[] >> simp[])
  (* the rest change nothing *)
  >> simp[ostep_def, ostepc_def, ewbytes_def] >>
  TRY (rename1 ‘ALOOKUP es.ctbl h = SOME _’ >>
       ‘ALOOKUP es.p.b.tbl h = NONE’
         by (simp[ALOOKUP_NONE] >> imp_res_tac ALOOKUP_MEM >>
             gvs[oown_def, ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[FST]) >>
       simp[]) >>
  drule sys_connect_quiet >> strip_tac >>
  ‘l0_rely w'’ by (gvs[sys_connect_def] >> metis_tac[l0_do_rely]) >> simp[]
QED

(* ------------------------------------------------------------------------
   The fds an episode lives on: held, or accepted ahead (whose account is
   empty: only held fds have an outbox or are gone, okeys)
   ------------------------------------------------------------------------ *)

Definition live_def:
  live (es : l1e) f ⇔ held es.p.b f ∨ MEM f es.p.acq
End

Theorem edo_okeys:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ oown lfd es ∧ okeys es.p.b ⇒
  okeys es'.p.b
Proof
  strip_tac >> ‘pown lfd es.p’ by fs[oown_def] >>
  Cases_on ‘a’ >> gvs[edo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule_all pdo_keys >> simp[] >> NO_TAC) >>
  TRY (gvs[okeys_def, outbox_of_def] >> NO_TAC) >>
  gvs[ec_del_def, l1_close_def, AllCaseEqs()] >> irule okeys_forget >> simp[]
QED

Theorem edo_acq:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ MEM f es'.p.acq ⇒ MEM f es.p.acq
Proof
  Cases_on ‘a’ >> rw[edo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[ec_del_def] >>
  gvs[pdo_def, AllCaseEqs()] >> TRY (PairCases_on ‘z’) >> gvs[]
QED

Theorem pdo_write_held:
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs) ⇒
  ps'.b.tbl = ps.b.tbl ∧ ps'.b.closing = ps.b.closing
Proof
  simp[pdo_def, l1do_def] >> rw[] >> gvs[AllCaseEqs(), set_outbox_def] >>
  simp[after_send_def] >> every_case_tac >> simp[set_outbox_def]
QED

(* An fd L1 does not hold: no bytes written on it; held after only as the
   accepted one *)
Theorem edo_unheld:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ oown lfd es ∧ ¬held es.p.b f ⇒
  ewbytes f es a = [] ∧ (held es'.p.b f ⇒ MEM f es.p.acq)
Proof
  strip_tac >>
  ‘∀h. ALOOKUP es.p.b.tbl h ≠ SOME f’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >> gvs[held_def, MEM_MAP] >> metis_tac[SND]) >>
  Cases_on ‘a’ >> gvs[edo_def, AllCaseEqs(), ewbytes_def]
  >~ [‘pdo _ _ (Accept _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_accept_ostep >> strip_tac >> gvs[held_def] >>
      rw[] >> qpat_x_assum ‘es.p.acq = _’ (fn th => ONCE_REWRITE_TAC [th]) >> simp[])
  >~ [‘pdo _ _ (Read _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >>
      strip_tac >> qpat_x_assum ‘held _ _’ mp_tac >> qpat_x_assum ‘¬held _ _’ mp_tac >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
      simp[pdo_def, AllCaseEqs(), held_def] >> rw[] >> gvs[set_inb_def] >>
      TRY (PairCases_on ‘z’) >> gvs[l1_close_def, AllCaseEqs(), forget_def, MEM_FILTER] >>
      metis_tac[honestL1PFRefineTheory.MEM_SND_ADELKEY_sub])
  >~ [‘pdo _ _ (Write _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_write_held >> strip_tac >> gvs[held_def])
  >~ [‘l1_close _ _ = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule l1_close_ostep >> strip_tac >>
      gvs[ec_del_def, held_def] >> metis_tac[])
  >> gvs[held_def]
QED

Theorem edo_unlive:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ oown lfd es ∧ ¬live es f ⇒
  ewbytes f es a = [] ∧ ¬live es' f
Proof
  strip_tac >> fs[live_def] >> drule_all edo_unheld >> strip_tac >> simp[] >>
  metis_tac[edo_acq]
QED

(* An fd L1 does not hold: nothing sent or written; held after only as the
   accepted one, with an empty outbox *)
Theorem edo_quiet:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ oown lfd es ∧ okeys es.p.b ∧
  l0_rely w ∧ ¬held es.p.b f ⇒
  evs_sent f evs = [] ∧ ewbytes f es a = [] ∧
  (held es'.p.b f ⇒ MEM f es.p.acq ∧ outbox_of es'.p.b f = [] ∧ ¬MEM f es'.p.b.gone)
Proof
  strip_tac >>
  ‘outbox_of es.p.b f = [] ∧ ¬MEM f es.p.b.gone’ by (gvs[okeys_def, held_def] >> metis_tac[]) >>
  ‘∀h. ALOOKUP es.p.b.tbl h ≠ SOME f’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >> gvs[held_def, MEM_MAP] >> metis_tac[SND]) >>
  Cases_on ‘a’ >> gvs[edo_def, AllCaseEqs(), ewbytes_def]
  >~ [‘pdo _ _ (Accept _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_accept_ostep >> strip_tac >> gvs[held_def] >>
      rw[] >- (qpat_x_assum ‘es.p.acq = _’ (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
      fs[outbox_of_def])
  >~ [‘pdo _ _ (Read _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >>
      ‘pown lfd es.p’ by fs[oown_def] >> drule_all pdo_read_ostep >> strip_tac >> simp[] >>
      strip_tac >> qpat_x_assum ‘held _ _’ mp_tac >> qpat_x_assum ‘¬held _ _’ mp_tac >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
      simp[pdo_def, AllCaseEqs(), held_def] >> rw[] >> gvs[set_inb_def] >>
      TRY (PairCases_on ‘z’) >> gvs[l1_close_def, AllCaseEqs(), forget_def, MEM_FILTER] >>
      metis_tac[honestL1PFRefineTheory.MEM_SND_ADELKEY_sub])
  >~ [‘pdo _ _ (Write _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_write_ostep >> strip_tac >>
      drule pdo_write_held >> strip_tac >>
      first_x_assum (qspec_then ‘f’ mp_tac) >> simp[ostep_def, wbytes_def] >>
      ‘∀h. ALOOKUP es.p.b.tbl h = SOME f ⇔ F’ by metis_tac[] >> simp[] >>
      Cases_on ‘MEM f z2.b.gone’ >> simp[] >> gvs[held_def])
  >~ [‘l1_close _ _ = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule l1_close_ostep >> strip_tac >>
      gvs[ec_del_def, held_def] >> metis_tac[])
  >> TRY (drule sys_connect_quiet >> strip_tac) >> gvs[held_def]
QED

Theorem edo_live:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ oown lfd es ∧ okeys es.p.b ∧ l0_rely w ⇒
  l0_rely w' ∧ okeys es'.p.b ∧
  ∀f. (live es f ⇒
         (live es' f ⇒ ostep f es.p.b es'.p.b evs (ewbytes f es a)) ∧
         ostepc f es.p.b evs (ewbytes f es a)) ∧
      (¬live es f ⇒ evs_sent f evs = [] ∧ ewbytes f es a = [] ∧ ¬live es' f)
Proof
  strip_tac >> drule_all edo_ostep >> strip_tac >> drule_all edo_okeys >> strip_tac >>
  simp[] >> gen_tac >>
  ‘pown lfd es.p’ by fs[oown_def] >>
  Cases_on ‘held es.p.b f’
  >- (‘¬MEM f es.p.acq’ by gvs[held_def, honestL1PFRefineTheory.pown_def, ALL_DISTINCT_APPEND] >>
      ‘¬MEM f es'.p.acq’ by metis_tac[edo_acq] >>
      simp[live_def] >> metis_tac[]) >>
  drule_all edo_quiet >> strip_tac >> simp[live_def] >>
  ‘outbox_of es.p.b f = [] ∧ ¬MEM f es.p.b.gone’ by (gvs[okeys_def, held_def] >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[edo_acq] >>
  strip_tac >> simp[ostepc_def] >>
  rpt strip_tac >> simp[ostep_def] >>
  Cases_on ‘held es'.p.b f’ >> gvs[] >>
  ‘outbox_of es'.p.b f = [] ∧ ¬MEM f es'.p.b.gone’ by (gvs[okeys_def, held_def] >> metis_tac[]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   A round's actions
   ------------------------------------------------------------------------ *)

(* What the actions wrote on fd f, each in the state the ones before left *)
Definition eawbytes_def:
  eawbytes lfd pol f ws [] = [] ∧
  eawbytes lfd pol f ws (a :: acts) =
    ewbytes f (SND ws) a ++
    (case edo lfd pol ws a of
     | SOME (_, ws1, _) => eawbytes lfd pol f ws1 acts
     | NONE => [])
End

Theorem ostep_refl:
  ostep f b b [] []
Proof
  simp[ostep_def]
QED

(* The actions, given L1's own invariant before each (E1 has it: eown) *)
Theorem eacts_live:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧
    (∀i rs0 evs0 wi esi.
       i < LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
       oown lfd esi) ∧
    okeys es.p.b ∧ l0_rely w ⇒
    l0_rely w' ∧ okeys es'.p.b ∧
    ∀f. (live es f ⇒
           (live es' f ⇒ ostep f es.p.b es'.p.b evs (eawbytes lfd pol f (w, es) acts)) ∧
           ostepc f es.p.b evs (eawbytes lfd pol f (w, es) acts)) ∧
        (¬live es f ⇒
           evs_sent f evs = [] ∧ eawbytes lfd pol f (w, es) acts = [] ∧ ¬live es' f)
Proof
  Induct
  >- (simp[eacts_def, eawbytes_def] >> rpt strip_tac >> gvs[ostep_refl, ostepc_def]) >>
  rpt gen_tac >> rename1 ‘a :: acts’ >> strip_tac >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ mp_tac >> simp[Once eacts_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘edo _ _ _ _ = SOME (r1, (w1, es1), evs1)’ >> strip_tac >> gvs[] >>
  ‘oown lfd es’
    by (first_x_assum (qspecl_then [‘0’, ‘[]’, ‘[]’, ‘w’, ‘es’] mp_tac) >> simp[eacts_def]) >>
  drule_all edo_live >> strip_tac >>
  first_x_assum (qspecl_then [‘w1’, ‘es1’] mp_tac) >> simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [‘SUC i’, ‘r1 :: rs0’, ‘evs1 ++ evs0’, ‘wi’, ‘esi’] mp_tac) >>
      simp[eacts_def]) >>
  strip_tac >> simp[eawbytes_def] >> gen_tac >>
  last_x_assum (qspec_then ‘f’ strip_assume_tac) >>
  first_x_assum (qspec_then ‘f’ strip_assume_tac) >>
  Cases_on ‘live es f’ >> gvs[] >>
  Cases_on ‘live es1 f’ >> gvs[]
  >- metis_tac[ostep_trans, ostep_ostepc_trans] >>
  metis_tac[ostepc_quiet, APPEND_NIL]
QED

(* ------------------------------------------------------------------------
   The round's tail, stage by stage (on the trace: no L0 world invariant)
   ------------------------------------------------------------------------ *)

Theorem pf_fetch_quiet:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ⇒
    l0_rely w' ∧ ps'.b = ps.b ∧ (∀f. evs_sent f evs = []) ∧
    (∀f. MEM f ps'.acq ⇔ MEM f ps.acq ∨ MEM (FConn f) log)
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (g :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      ‘l0_rely w1’ by (gvs[sys_accept_def] >> metis_tac[l0_do_rely]) >>
      first_x_assum drule_all >> strip_tac >>
      ‘∀f. ev_sent f ev = []’ by (drule (cj 4 sys_ev_sent) >> simp[]) >>
      Cases_on ‘l0_res_of out’ >> gvs[] >> rw[] >> gvs[] >> metis_tac[])
  >> Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  ‘l0_rely w1’ by (gvs[sys_recv_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> strip_tac >>
  ‘∀f. ev_sent f ev = []’ by (drule (cj 2 sys_ev_sent) >> simp[]) >>
  ‘ps1.b = ps.b ∧ ps1.acq = ps.acq ∧ ∀f. ¬MEM (FConn f) fl'’
    by (qpat_x_assum ‘_ = (ps1, fl')’ mp_tac >> rw[AllCaseEqs(), set_inb_def] >> gvs[]) >>
  gvs[]
QED

Theorem drop_ostep:
  ostep f b (drop_out b g) [] []
Proof
  rw[ostep_def, drop_out_def, outbox_of_set_outbox, MEM_FILTER] >> rw[] >> gvs[]
QED

Theorem FOLDL_drop_ostep:
  ∀dl b. ostep f b (FOLDL drop_out b dl) [] []
Proof
  Induct >> simp[ostep_refl] >> rpt gen_tac >>
  ‘ostep f b (FOLDL drop_out (drop_out b h) dl) ([] ++ []) ([] ++ [])’
    by metis_tac[ostep_trans, drop_ostep] >>
  fs[]
QED

Theorem stall_ostep:
  ostep f ps.b (stall_step hfs ob log ps).b [] []
Proof
  simp[stall_step_def, FOLDL_drop_ostep]
QED

Theorem l1_reap_quiet:
  ∀fs w b w' b' evs. l1_reap fs (w, b) = SOME ((w', b'), evs) ⇒ ∀f. evs_sent f evs = []
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  TRY (PairCases_on ‘ws’) >> gvs[] >> res_tac >> gvs[l1_close_def, AllCaseEqs()] >>
  metis_tac[sys_close_quiet]
QED

(* A closing fd with something to send stays as it is *)
Theorem l1_reap_busy:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ outbox_of b f ≠ [] ∧ ¬MEM f b.gone ⇒
    outbox_of b' f = outbox_of b f ∧ ¬MEM f b'.gone
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >> rw[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> gvs[l1_close_def, AllCaseEqs()] >>
  ‘h ≠ f’ by (strip_tac >> gvs[]) >>
  first_x_assum drule >> simp[forget_other]
QED

(* ... and one that leaves closing was closed: its account is empty *)
Theorem l1_reap_closed:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ MEM f b.closing ∧ ¬MEM f b'.closing ⇒
    outbox_of b' f = [] ∧ ¬MEM f b'.gone
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> PairCases_on ‘ws’ >>
      fs[l1_close_def, AllCaseEqs()] >> rveq >>
      Cases_on ‘h = f’ >> fs[] >>
      TRY (first_x_assum drule >> simp[forget_other] >> NO_TAC) >>
      rveq >> ‘outbox_of (forget f b) f = [] ∧ ¬MEM f (forget f b).gone’
        by simp[forget_keys, MEM_FILTER] >>
      drule_all l1_reap_clean >> simp[])
  >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem sys_connerr_quiet:
  sys_connerr g w = SOME (out, w', ev) ⇒ ∀f. ev_sent f ev = []
Proof
  rw[sys_connerr_def] >> drule l0_do_cases >> rw[] >> simp[ev_sent_def]
QED

Theorem settle_fds_quiet:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ∧ l0_rely w ⇒
    l0_rely w' ∧ es'.p = es.p ∧ es'.ctbl = es.ctbl ∧ ∀f. evs_sent f evs = []
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  ‘l0_rely w1’ by (gvs[sys_connerr_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule sys_connerr_quiet >> simp[] >> disch_then kall_tac >>
  every_case_tac >> gvs[]
QED

Theorem promote_fields:
  (promote es).p.b.outbox = es.p.b.outbox ∧ (promote es).p.b.gone = es.p.b.gone ∧
  (promote es).p.b.closing = es.p.b.closing ∧ (promote es).p.acq = es.p.acq ∧
  (∀f. MEM f (MAP SND (promote es).p.b.tbl) ⇒
       MEM f (MAP SND es.p.b.tbl) ∨ MEM f (MAP SND es.ctbl)) ∧
  (∀f. MEM f (MAP SND es.p.b.tbl) ⇒ MEM f (MAP SND (promote es).p.b.tbl))
Proof
  simp[promote_def] >> rw[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem apply_early_p[simp]:
  (apply_early es).p = es.p ∧ (apply_early es).ctbl = es.ctbl
Proof
  simp[apply_early_def]
QED

Theorem ostep_sent:
  evs_sent f e1 = evs_sent f e2 ⇒
  (ostep f b b' e1 a ⇔ ostep f b b' e2 a) ∧ (ostepc f b e1 a ⇔ ostepc f b e2 a)
Proof
  simp[ostep_def, ostepc_def]
QED

Theorem etail_live:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  oown lfd es ∧ okeys es.p.b ∧ l0_rely w ∧ pown lfd es'.p ⇒
  l0_rely w' ∧ okeys es'.p.b ∧
  (∀f. MEM f (MAP SND es'.ctbl) ⇒ MEM f (MAP SND es.ctbl)) ∧
  (∀f. live es' f ⇒ live es f ∨ MEM f (MAP SND es.ctbl) ∨ MEM (FConn f) log) ∧
  ∀f. (live es f ⇒
         ostepc f es.p.b tevs [] ∧
         (live es' f ∧ ¬MEM (FConn f) log ⇒ ostep f es.p.b es'.p.b tevs [])) ∧
      (¬live es f ⇒ evs_sent f tevs = []) ∧
      (live es' f ∧ (¬live es f ∨ MEM (FConn f) log) ⇒
         outbox_of es'.p.b f = [] ∧ ¬MEM f es'.p.b.gone)
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  ‘es'.p = (promote es5).p’ by (qpat_x_assum ‘_ = es'’ (SUBST1_TAC o SYM) >> simp[]) >>
  ‘∀f. MEM f (MAP SND es'.ctbl) ⇒ MEM f (MAP SND es5.ctbl)’
    by (qpat_x_assum ‘_ = es'’ (SUBST1_TAC o SYM) >>
        simp[promote_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  qpat_x_assum ‘FILTER _ hs = rdy’ kall_tac >> qpat_x_assum ‘_ = es'’ kall_tac >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3'’ >>
  ‘pown lfd es.p’ by fs[oown_def] >>
  (* the stages *)
  drule_all l1_polls_l0 >> strip_tac >> drule l1_polls_quiet >> strip_tac >>
  drule_all l1_flush_l0 >> strip_tac >> drule_all l1_flush_keys >> strip_tac >>
  drule_all pf_fetch_quiet >> simp[] >> strip_tac >>
  ‘ps3.b.tbl = ps3'.b.tbl ∧ ps3.b.closing = ps3'.b.closing ∧ ps3.acq = ps3'.acq ∧
   okeys ps3.b ∧ (∀f. ostep f ps3'.b ps3.b [] []) ∧
   ∀f. ¬MEM f (MAP SND ps3'.b.tbl) ∧ ¬MEM f ps3'.b.closing ⇒
       outbox_of ps3.b f = outbox_of ps3'.b f ∧ (MEM f ps3.b.gone ⇔ MEM f ps3'.b.gone)’
    by simp[Abbr ‘ps3’, stall_out, stall_ostep, stall_other] >>
  drule_all l1_reap_l0 >> strip_tac >> drule l1_reap_quiet >> strip_tac >>
  ‘okeys b4’ by metis_tac[l1_reap_okeys] >>
  drule_all settle_fds_quiet >> simp[] >> strip_tac >>
  ‘es'.p.b.outbox = b4.outbox ∧ es'.p.b.gone = b4.gone ∧ es'.p.b.closing = b4.closing ∧
   es'.p.acq = ps3'.acq ∧
   (∀f. MEM f (MAP SND es'.p.b.tbl) ⇒ MEM f (MAP SND b4.tbl) ∨ MEM f (MAP SND es.ctbl)) ∧
   (∀f. MEM f (MAP SND b4.tbl) ⇒ MEM f (MAP SND es'.p.b.tbl))’
    by (qpat_x_assum ‘es'.p = _’ SUBST1_TAC >>
        mp_tac (Q.INST [‘es’ |-> ‘es5’] promote_fields) >> simp[]) >>
  ‘∀f. outbox_of es'.p.b f = outbox_of b4 f’ by simp[outbox_of_def] >>
  ‘okeys es'.p.b’ by (gvs[okeys_def] >> metis_tac[]) >>
  ‘∀f. MEM f (MAP SND es'.ctbl) ⇒ MEM f (MAP SND es.ctbl)’ by metis_tac[] >>
  ‘∀f. live es' f ⇒ live es f ∨ MEM f (MAP SND es.ctbl) ∨ MEM (FConn f) log’
    by (rpt strip_tac >> fs[live_def, held_def] >> rfs[] >>
        ‘b4.tbl = es.p.b.tbl ∧ ps3.b.closing = es.p.b.closing’ by rfs[] >>
        metis_tac[]) >>
  qpat_x_assum ‘es'.p = _’ (fn th => REWRITE_TAC [GSYM th]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> gen_tac >>
  ‘evs_sent f (pevs ++ fevs ++ gevs ++ cevs ++ sevs) = evs_sent f fevs’ by simp[] >>
  drule ostep_sent >> strip_tac >> pop_assum kall_tac >>
  ‘∀b b'. ostep f b b' (pevs ++ fevs ++ gevs ++ cevs ++ sevs) [] ⇔ ostep f b b' fevs []’
    by metis_tac[ostep_sent] >>
  ‘∀b. ostepc f b (pevs ++ fevs ++ gevs ++ cevs ++ sevs) [] ⇔ ostepc f b fevs []’
    by metis_tac[ostep_sent] >>
  ntac 2 (pop_assum (fn th => REWRITE_TAC [th])) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  (* an fd not held at the start keeps an empty account *)
  ‘¬held es.p.b f ⇒ evs_sent f fevs = [] ∧ outbox_of es'.p.b f = [] ∧ ¬MEM f es'.p.b.gone’
    by (strip_tac >>
        ‘outbox_of es.p.b f = [] ∧ ¬MEM f es.p.b.gone’
          by (fs[okeys_def, held_def] >> metis_tac[]) >>
        ‘outbox_of b2 f = [] ∧ ¬MEM f b2.gone ∧ evs_sent f fevs = []’
          by (drule_all l1_flush_other >> fs[]) >>
        ‘¬MEM f (MAP SND ps3'.b.tbl) ∧ ¬MEM f ps3'.b.closing’ by fs[held_def] >>
        ‘outbox_of ps3.b f = [] ∧ ¬MEM f ps3.b.gone’ by (res_tac >> fs[]) >>
        ‘outbox_of b4 f = [] ∧ ¬MEM f b4.gone’
          by (qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule_all l1_reap_other >> fs[]) >>
        fs[]) >>
  (* to the stall, any fd *)
  ‘ostep f es.p.b ps3.b fevs []’
    by (drule_all l1_flush_ostep >> strip_tac >>
        pop_assum (qspec_then ‘f’ assume_tac) >>
        ‘ostep f ps3'.b ps3.b [] []’ by fs[] >> rfs[] >>
        metis_tac[ostep_trans, APPEND_NIL]) >>
  (* the reap keeps an fd it does not close *)
  ‘¬MEM f ps3'.b.closing ∨ MEM f b4.closing ⇒ ostep f es.p.b es'.p.b fevs []’
    by (strip_tac >>
        ‘outbox_of b4 f = outbox_of ps3.b f ∧ (MEM f b4.gone ⇔ MEM f ps3.b.gone)’
          by (qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >>
              TRY (drule_all l1_reap_other >> simp[] >> NO_TAC) >>
              drule_all l1_reap_closing >> strip_tac >> rfs[] >>
              drule_all l1_reap_busy >> simp[]) >>
        ‘ostep f ps3.b es'.p.b [] []’ by (irule ostep_quiet >> fs[]) >>
        metis_tac[ostep_trans, APPEND_NIL]) >>
  ‘MEM f ps3'.b.closing ⇔ MEM f es.p.b.closing’ by fs[] >>
  ‘MEM f es.p.b.closing ⇒ ¬MEM f (MAP SND es.p.b.tbl) ∧ ¬MEM f es.p.acq ∧
                          ¬MEM f (MAP SND es.ctbl)’
    by (strip_tac >> ‘held es.p.b f’ by simp[held_def] >>
        metis_tac[pown_disjoint, eown_ctbl_held]) >>
  ‘MEM f (MAP SND es'.p.b.tbl) ⇒ MEM f (MAP SND es.p.b.tbl) ∨ MEM f (MAP SND es.ctbl)’
    by (strip_tac >> res_tac >> rfs[]) >>
  ‘MEM f es'.p.acq ⇒ ¬held es'.p.b f’ by metis_tac[pown_disjoint, held_def] >>
  rpt conj_tac
  >- (strip_tac >> conj_tac >- metis_tac[ostep_ostepc] >>
      strip_tac >> first_x_assum irule >> CCONTR_TAC >> fs[live_def, held_def] >>
      metis_tac[])
  >- (simp[live_def])
  >> strip_tac >> Cases_on ‘held es.p.b f’ >> fs[live_def]
  >- metis_tac[]
  >> ‘MEM f es'.p.acq’ by fs[] >>
  ‘¬MEM f b4.closing ∧ ¬MEM f (MAP SND b4.tbl)’ by metis_tac[held_def] >>
  ‘b4.tbl = es.p.b.tbl ∧ ps3.b.closing = es.p.b.closing’
    by (qpat_x_assum ‘b4.tbl = _’ SUBST1_TAC >> qpat_x_assum ‘ps3.b.tbl = _’ SUBST1_TAC >>
        qpat_x_assum ‘ps3.b.closing = _’ SUBST1_TAC >> qpat_x_assum ‘ps3'.b = _’ SUBST1_TAC >>
        conj_tac >> first_assum ACCEPT_TAC) >>
  ‘MEM f ps3.b.closing’ by (fs[held_def] >> metis_tac[]) >>
  qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >> drule_all l1_reap_closed >> fs[]
QED

(* ------------------------------------------------------------------------
   A round: an fd that lives through it keeps its account; one that ends
   (closed in the actions, or reaped) sent a prefix; one that starts (a
   connect that came up, an accepted connection, FConn) starts empty
   ------------------------------------------------------------------------ *)

Theorem eround_live:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
  (∀i rs0 evs0 wi esi.
     i ≤ LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
     oown lfd esi) ∧
  pown lfd es'.p ∧ okeys es.p.b ∧ l0_rely w ⇒
  ∃rs aevs w1 es1.
    eacts lfd pol (w, es) acts = SOME (rs, aevs, (w1, es1)) ∧
    l0_rely w' ∧ okeys es'.p.b ∧
    (∀f. MEM f (MAP SND es'.ctbl) ⇒ MEM f (MAP SND es1.ctbl)) ∧
    (∀f. live es' f ⇒ live es1 f ∨ MEM f (MAP SND es1.ctbl) ∨ MEM (FConn f) log) ∧
    ∀f. (live es f ⇒ ostepc f es.p.b evs (eawbytes lfd pol f (w, es) acts)) ∧
        (live es f ∧ live es1 f ∧ live es' f ∧ ¬MEM (FConn f) log ⇒
         ostep f es.p.b es'.p.b evs (eawbytes lfd pol f (w, es) acts)) ∧
        (¬live es f ⇒
         evs_sent f evs = [] ∧ eawbytes lfd pol f (w, es) acts = [] ∧ ¬live es1 f) ∧
        (live es' f ∧ (¬live es1 f ∨ MEM (FConn f) log) ⇒
         outbox_of es'.p.b f = [] ∧ ¬MEM f es'.p.b.gone)
Proof
  simp[eround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, ws1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, (w1, es1))’ >>
  gvs[] >>
  ‘oown lfd es1’
    by (first_x_assum (qspec_then ‘LENGTH acts’ mp_tac) >> simp[TAKE_LENGTH_ID_rwt]) >>
  drule eacts_live >> impl_tac >- (simp[] >> metis_tac[LESS_IMP_LESS_OR_EQ]) >> strip_tac >>
  qpat_x_assum ‘etail _ _ _ _ = _’ assume_tac >> drule etail_live >>
  impl_tac >- fs[] >> strip_tac >> simp[] >> gen_tac >>
  last_x_assum (qspec_then ‘f’ strip_assume_tac) >>
  first_x_assum (qspec_then ‘f’ strip_assume_tac) >>
  qabbrev_tac ‘aw = eawbytes lfd pol f (w, es) acts’ >>
  Cases_on ‘live es f’ >> fs[]
  >- (Cases_on ‘live es1 f’ >> fs[]
      >- (conj_tac
          >- (‘ostepc f es.p.b (aevs ++ tevs) (aw ++ [])’ by metis_tac[ostep_ostepc_trans] >>
              fs[])
          >> rpt strip_tac >>
          ‘ostep f es.p.b es'.p.b (aevs ++ tevs) (aw ++ [])’ by metis_tac[ostep_trans] >>
          fs[])
      >> ‘ostepc f es.p.b (aevs ++ tevs) (aw ++ [])’ by metis_tac[ostepc_quiet] >> fs[]) >>
  rpt strip_tac >> fs[]
QED

(* An fd not live gets no bytes for the rest of the actions *)
Theorem eacts_unlive:
  ∀acts w es.
    (∀i rs0 evs0 wi esi.
       i < LENGTH acts ∧ eacts lfd pol (w, es) (TAKE i acts) = SOME (rs0, evs0, (wi, esi)) ⇒
       oown lfd esi) ∧ ¬live es f ⇒
    eawbytes lfd pol f (w, es) acts = []
Proof
  Induct >> simp[eawbytes_def] >> rpt gen_tac >> strip_tac >>
  ‘oown lfd es’
    by (first_x_assum (qspecl_then [‘0’, ‘[]’, ‘[]’, ‘w’, ‘es’] mp_tac) >> simp[eacts_def]) >>
  Cases_on ‘edo lfd pol (w, es) h’ >> simp[]
  >- (Cases_on ‘h’ >> simp[ewbytes_def] >> rw[] >> imp_res_tac ALOOKUP_MEM >>
      gvs[live_def, held_def, MEM_MAP] >> metis_tac[SND]) >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  drule_all edo_unlive >> strip_tac >> simp[] >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘SUC i’, ‘x0 :: rs0’, ‘x3 ++ evs0’, ‘wi’, ‘esi’] mp_tac) >>
  simp[eacts_def]
QED
