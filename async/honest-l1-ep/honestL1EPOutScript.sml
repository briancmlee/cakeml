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
  honestL1EPRefine honestL1EPModel honestL1PFOut honestL1PFRound honestL1PFModel
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
  (∀f. evs_sent f evs = []) ∧ (∀f. f ≠ g ⇒ ostep f b b' evs []) ∧
  b'.tbl = b.tbl ∧ (∀f. MEM f b'.closing ⇔ MEM f b.closing ∧ f ≠ g)
Proof
  simp[l1_close_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule sys_close_quiet >> strip_tac >> gvs[] >>
  simp[ostep_def, forget_other] >> simp[forget_def, MEM_FILTER] >> metis_tac[]
QED
