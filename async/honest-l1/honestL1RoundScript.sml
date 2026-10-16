(*
  R2, round by round: in the simple world, a round of L1 (the
  computation's actions, then the poll) is a round of the handle layer
  (asyncHLModel's hacts and hpoll), with the same responses and snapshot,
  and L1's renamed events are the handle layer's with some would-block
  events deleted.

  The server's side of the round discipline is stated on the handle
  layer alone (hacts_disc): it accepts only on the listener and reads only
  handles that were polled, with the fd they had, at the last poll.
*)
Theory honestL1Round
Ancestors
  honestL1Steps honestL1Refine honestL1Model honestL1Simple honestL1Inv
  honestL0World honestL0WorldProps honestL0Rely honestL0 asyncHLModel socketV2FFI
  socketV2Events ffiSpikeSocketFFI asyncM3World asyncCore asyncLevel1
Libs
  preamble

(* ------------------------------------------------------------------------
   The actions of a round
   ------------------------------------------------------------------------ *)

(* The discipline, on the handle layer's run of the actions *)
Definition hacts_disc_def:
  hacts_disc lfd polp sh [] = T ∧
  hacts_disc lfd polp (s, hs) (a :: acts) =
    ((case a of
      | Accept l => l = lfd ∧ MEM (lfd, lfd) polp
      | Read h n => 0 < n ∧ n < 256 ** 8 ∧ ∀f. ALOOKUP hs.tbl h = SOME f ⇒ MEM (h, f) polp
      | Write h bs => LENGTH bs < 256 ** 8) ∧
     case hdo lfd (s, hs) a of
     | SOME (r, sh', evs) => hacts_disc lfd polp sh' acts
     | NONE => T)
End

Theorem act_disc_hl:
  st.tbl = hs.tbl ⇒
  (act_disc lfd polp st a ⇔
   case a of
   | Accept l => l = lfd ∧ MEM (lfd, lfd) polp
   | Read h n => 0 < n ∧ n < 256 ** 8 ∧ ∀f. ALOOKUP hs.tbl h = SOME f ⇒ MEM (h, f) polp
   | Write h bs => LENGTH bs < 256 ** 8)
Proof
  Cases_on ‘a’ >> simp[act_disc_def]
QED

Theorem hdln_mono:
  j ≤ k ⇒ hdln n j ≤ hdln n k
Proof
  rw[hdln_def]
QED

Theorem acts_step:
  ∀acts w st s hs.
    simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
    rdy_ok lfd polp w st ∧ fds_lt w ∧ hacts_disc lfd polp (s, hs) acts ∧
    LENGTH (l0_used w) + LENGTH acts < 2147483647 ∧
    hdln (w2n lfd) (st.nxt + LENGTH acts) < dimword (:64) ∧ w2n lfd < 2147483648 ⇒
    ∃rs evs w' st' evs' s' hs'.
      l1acts lfd (w, st) acts = SOME (rs, evs, (w', st')) ∧
      hacts lfd (s, hs) acts = SOME (rs, evs', (s', hs')) ∧
      drops (MAP l0_v2_event evs) evs' ∧
      simple_v2 p lfd sched w' ∧ l0_rely w' ∧
      l1v2_rel p lfd sched (w', st') (s', hs') ∧ rdy_ok lfd polp w' st' ∧ fds_lt w' ∧
      st'.nxt ≤ st.nxt + LENGTH acts ∧
      LENGTH (l0_used w') ≤ LENGTH (l0_used w) + LENGTH acts
Proof
  Induct >> simp[l1acts_def, hacts_def] >> rpt gen_tac >> strip_tac >>
  ‘st.tbl = hs.tbl’ by gvs[l1v2_rel_def] >>
  ‘act_disc lfd polp st h’ by (Cases_on ‘h’ >> gvs[act_disc_def, hacts_disc_def]) >>
  ‘LENGTH (l0_used w) < 2147483647’ by decide_tac >>
  ‘hdln (w2n lfd) st.nxt ≤ hdln (w2n lfd) (st.nxt + SUC (LENGTH acts))’
    by (irule hdln_mono >> simp[]) >>
  ‘hdln (w2n lfd) st.nxt < dimword (:64)’ by (fs[] >> decide_tac) >>
  drule_all act_step >> strip_tac >> simp[] >>
  ‘hacts_disc lfd polp (s', hs') acts’ by gvs[hacts_disc_def] >>
  ‘simple_v2 p lfd sched w'’ by metis_tac[simple_v2_same] >>
  ‘l0_rely w'’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  first_x_assum (qspecl_then [‘w'’, ‘st'’, ‘s'’, ‘hs'’] mp_tac) >>
  impl_tac
  >- (simp[] >> TRY (conj_tac >- decide_tac) >>
      ‘hdln (w2n lfd) (st'.nxt + LENGTH acts) ≤ hdln (w2n lfd) (st.nxt + SUC (LENGTH acts))’
        by (irule hdln_mono >> simp[]) >>
      fs[] >> decide_tac) >>
  strip_tac >> simp[] >>
  rpt conj_tac >> TRY (metis_tac[drops_APPEND] >> NO_TAC) >> decide_tac
QED
