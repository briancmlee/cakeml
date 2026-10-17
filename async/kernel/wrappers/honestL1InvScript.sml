(*
  L1 never makes a failing L0 call (proved).

  An L0 call fails (the C exits; the model's FFI call fails) only on
  misuse: wrong lengths, an fd above 2^31 - 1, more than 4096 fds in one
  poll.  L1's calls have the right lengths by construction, polls are
  chunked (at most 4096 entries each), and every fd L1 holds is one it was
  given by the kernel or the listener: the invariant small_fds says they
  are all below 2^31 (the rely bounds the fd limit by 2^31, and the kernel
  gives the lowest free fd below the limit).

  MAIN:
   - l1round_ok: a round completes (SOME), keeps the invariant and the
     rely, provided the computation's actions are well formed (as for the
     handle layer: reads of 0 < n < 2^64 bytes) and the handle numbers do
     not overflow;
   - lrounds_ok: hence the whole run never fails.
*)
Theory honestL1Inv
Ancestors
  honestL1Model honestL0World honestL0WorldProps honestL0Rely honestL0
  socketWorld loopPollWorld asyncCore asyncLevel1 Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   The invariant
   ------------------------------------------------------------------------ *)

Definition small_def:
  small (f : word64) ⇔ w2n f < 2147483648
End

Definition small_fds_def:
  small_fds lfd st ⇔
    small lfd ∧ EVERY small (MAP SND st.tbl) ∧ EVERY small st.closing ∧
    EVERY small (MAP FST st.outbox) ∧ EVERY small st.rdy ∧ EVERY small st.gone
End

(* The computation's actions are well formed *)
Definition act_ok_def:
  act_ok (Read h n) = (0 < n ∧ n < 256 ** 8) ∧
  act_ok _ = T
End

(* ------------------------------------------------------------------------
   Each L0 call succeeds, and keeps the rely
   ------------------------------------------------------------------------ *)

Theorem l0_do_SOME:
  l0_rely w ∧ l0_call n conf (REPLICATE alen 0w) (l0_tick n w) = SOME (FFIreturn out w1) ⇒
  l0_do n conf alen w =
    SOME (out, w1 with hist := w.hist ++ [(n, conf, REPLICATE alen 0w)],
          IO_event (ExtCall n) conf (ZIP (REPLICATE alen 0w, out))) ∧
  l0_rely (w1 with hist := w.hist ++ [(n, conf, REPLICATE alen 0w)])
Proof
  strip_tac >> simp[l0_do_def, l0_ffi_fn_def] >>
  imp_res_tac l0_call_ch >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]
QED

Theorem TAKE_DROP_fd_bytes[simp]:
  TAKE 8 (fd_bytes f ++ bs) = fd_bytes f ∧ DROP 8 (fd_bytes f ++ bs) = bs
Proof
  ‘LENGTH (fd_bytes f) = 8’ by simp[] >>
  metis_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

(* accept's result is well formed, and an fd it returns is below 2^31 *)
Theorem l0_accept_res:
  l0_rely w ∧ l0_accept l w = (r, w') ⇒
  l0_res_ok r ∧ ∀f. r = Ok f ⇒ f < 2147483648
Proof
  simp[l0_accept_def, l0_alloc_def] >> every_case_tac >>
  rw[] >> gvs[l0_res_ok_def, fail_def, l0_rely_def]
QED

Theorem sys_accept_ok:
  l0_rely w ∧ small l ⇒
  ∃out w' ev r. sys_accept l w = SOME (out, w', ev) ∧ l0_rely w' ∧
                l0_res_of out = r ∧ (∀f. r = Ok f ⇒ f < 2147483648)
Proof
  rw[small_def, sys_accept_def] >>
  ‘l0_rely (l0_tick «sys_accept» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  Cases_on ‘l0_accept l (l0_tick «sys_accept» w)’ >>
  drule_all l0_accept_res >> strip_tac >>
  ‘l0_call «sys_accept» (fd_bytes l) (REPLICATE 13 0w) (l0_tick «sys_accept» w) =
     SOME (FFIreturn (enc_res q) r)’
    by simp[l0_call_def, l0_hdr_def, fd_ok_def] >>
  drule_all l0_do_SOME >> strip_tac >> simp[] >>
  ‘l0_res_of (enc_res q) = q’ by
    (simp[l0_res_of_def] >> drule dec_enc_res >>
     disch_then (qspec_then ‘[]’ mp_tac) >> simp[]) >>
  simp[]
QED

Theorem sys_recv_ok:
  l0_rely w ∧ small f ∧ 0 < n ⇒
  ∃out w' ev. sys_recv f n w = SOME (out, w', ev) ∧ l0_rely w'
Proof
  rw[small_def, sys_recv_def] >>
  ‘l0_rely (l0_tick «sys_recv» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘∃out w1. l0_call «sys_recv» (fd_bytes f) (REPLICATE (n + 13) 0w)
              (l0_tick «sys_recv» w) = SOME (FFIreturn out w1)’
    by (simp[l0_call_def, l0_hdr_def, fd_ok_def] >> pairarg_tac >> simp[]) >>
  drule_all l0_do_SOME >> strip_tac >> simp[]
QED

Theorem sys_send_ok:
  l0_rely w ∧ small f ⇒
  ∃out w' ev. sys_send f bs w = SOME (out, w', ev) ∧ l0_rely w'
Proof
  rw[small_def, sys_send_def] >>
  ‘l0_rely (l0_tick «sys_send» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘∃out w1. l0_call «sys_send» (fd_bytes f ++ bs) (REPLICATE 13 0w)
              (l0_tick «sys_send» w) = SOME (FFIreturn out w1)’
    by (simp[l0_call_def, l0_hdr_def, fd_ok_def] >> pairarg_tac >> simp[]) >>
  drule_all l0_do_SOME >> strip_tac >> simp[]
QED

Theorem sys_close_ok:
  l0_rely w ∧ small f ⇒
  ∃out w' ev. sys_close f w = SOME (out, w', ev) ∧ l0_rely w'
Proof
  rw[small_def, sys_close_def] >>
  ‘l0_rely (l0_tick «sys_close» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘∃out w1. l0_call «sys_close» (fd_bytes f) (REPLICATE 13 0w)
              (l0_tick «sys_close» w) = SOME (FFIreturn out w1)’
    by (simp[l0_call_def, l0_hdr_def, fd_ok_def] >> pairarg_tac >> simp[]) >>
  drule_all l0_do_SOME >> strip_tac >> simp[]
QED

Theorem l0_do_buf_SOME:
  l0_rely w ∧ l0_call n conf bytes (l0_tick n w) = SOME (FFIreturn out w1) ⇒
  l0_do_buf n conf bytes w =
    SOME (out, w1 with hist := w.hist ++ [(n, conf, bytes)],
          IO_event (ExtCall n) conf (ZIP (bytes, out))) ∧
  l0_rely (w1 with hist := w.hist ++ [(n, conf, bytes)])
Proof
  strip_tac >> simp[l0_do_buf_def, l0_ffi_fn_def] >>
  imp_res_tac l0_call_ch >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]
QED

Theorem LENGTH_pfd_bytes[simp]:
  LENGTH (pfd_bytes fe) = 8
Proof
  PairCases_on ‘fe’ >> simp[pfd_bytes_def]
QED

Theorem LENGTH_FLAT_pfd_bytes[simp]:
  ∀fes. LENGTH (FLAT (MAP pfd_bytes fes)) = 8 * LENGTH fes
Proof
  Induct >> simp[MULT_CLAUSES]
QED

(* The poll's buffer is decoded back to its entries *)
Theorem pollfd_entries_buf:
  ∀fes. pollfd_entries (FLAT (MAP pfd_bytes fes)) = MAP pfd_bytes fes
Proof
  Induct >- simp[Once pollfd_entries_def] >>
  rw[] >> simp[Once pollfd_entries_def] >>
  ‘LENGTH (pfd_bytes h) = 8’ by simp[] >>
  simp[TAKE_APPEND1, DROP_APPEND1, TAKE_LENGTH_ID_rwt, DROP_LENGTH_NIL_rwt]
QED

Theorem pe_pfd_bytes:
  small f ∧ e < 4 ⇒ pe_fe (pfd_bytes (f, e)) = (f, e) ∧ pe_ok (pfd_bytes (f, e))
Proof
  strip_tac >> fs[small_def] >>
  ‘f <+ 0x80000000w’ by simp[WORD_LO] >>
  ‘pe_fd (pfd_bytes (f, e)) = f’
    by (simp[pfd_bytes_def, pe_fd_def] >> pop_assum mp_tac >> blastLib.BBLAST_TAC) >>
  ‘e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3’ by decide_tac >> gvs[] >>
  simp[pe_fe_def, pe_ok_def] >> simp[pfd_bytes_def, pe_events_def]
QED

Theorem sys_poll_ok:
  l0_rely w ∧ EVERY (λ(f, e). small f ∧ e < 4) fes ⇒
  ∃out w' ev. sys_poll fes w = SOME (out, w', ev) ∧ l0_rely w' ∧
              LENGTH out = 16 + 8 * LENGTH fes
Proof
  rw[sys_poll_def] >>
  ‘l0_rely (l0_tick «sys_poll» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘EVERY pe_ok (MAP pfd_bytes fes)’
    by (gvs[EVERY_MEM, MEM_MAP, FORALL_PROD, PULL_EXISTS] >> metis_tac[pe_pfd_bytes]) >>
  ‘∃out w1. l0_call «sys_poll» [0w] (poll_buf fes) (l0_tick «sys_poll» w) =
            SOME (FFIreturn out w1)’
    by (simp[l0_call_def, poll_buf_def, pollfd_entries_buf, DROP_APPEND,
             DROP_LENGTH_TOO_LONG] >> every_case_tac >> simp[]) >>
  drule_all l0_do_buf_SOME >> strip_tac >> simp[] >>
  drule_all l0_call_length >> simp[poll_buf_def]
QED

(* ------------------------------------------------------------------------
   The invariant is kept by L1's state changes
   ------------------------------------------------------------------------ *)

Theorem EVERY_MAP_SND_ADELKEY[local]:
  EVERY P (MAP SND l) ⇒ EVERY P (MAP SND (ADELKEY k l))
Proof
  simp[ADELKEY_def, EVERY_MAP, EVERY_FILTER_IMP] >> metis_tac[EVERY_MEM, MEM_FILTER]
QED

Theorem EVERY_MAP_FST_ADELKEY[local]:
  EVERY P (MAP FST l) ⇒ EVERY P (MAP FST (ADELKEY k l))
Proof
  simp[ADELKEY_def, EVERY_MAP, EVERY_MEM, MEM_FILTER]
QED

Theorem small_fds_set_outbox:
  small_fds lfd st ∧ small f ⇒ small_fds lfd (set_outbox f bs st)
Proof
  rw[small_fds_def, set_outbox_def] >> simp[EVERY_MAP_FST_ADELKEY]
QED

Theorem small_fds_forget:
  small_fds lfd st ∧ small f ⇒ small_fds lfd (forget f st)
Proof
  rw[forget_def] >> irule small_fds_set_outbox >>
  gvs[small_fds_def, EVERY_FILTER_IMP]
QED

Theorem small_fds_after_send:
  small_fds lfd st ∧ small f ⇒ small_fds lfd (after_send f r st)
Proof
  Cases_on ‘r’ >> rw[after_send_def] >> irule small_fds_set_outbox >>
  gvs[small_fds_def, EVERY_FILTER_IMP]
QED

Theorem small_fds_tbl_del:
  small_fds lfd st ⇒ small_fds lfd (st with tbl := ADELKEY h st.tbl)
Proof
  rw[small_fds_def] >> simp[EVERY_MAP_SND_ADELKEY]
QED

Theorem small_fds_rdy:
  small_fds lfd st ∧ EVERY small r ⇒ small_fds lfd (st with rdy := r)
Proof
  rw[small_fds_def]
QED

Theorem small_tbl_lookup:
  small_fds lfd st ∧ ALOOKUP st.tbl h = SOME f ⇒ small f
Proof
  rw[small_fds_def] >> imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
  metis_tac[SND]
QED

Theorem l1_close_ok:
  l0_rely w ∧ small_fds lfd st ∧ small f ⇒
  ∃w' st' evs. l1_close f (w, st) = SOME ((w', st'), evs) ∧ l0_rely w' ∧
               small_fds lfd st'
Proof
  rw[l1_close_def] >> drule_all sys_close_ok >> strip_tac >> simp[] >>
  irule small_fds_forget >> simp[]
QED

(* ------------------------------------------------------------------------
   Actions
   ------------------------------------------------------------------------ *)

Theorem l1do_ok:
  l0_rely w ∧ small_fds lfd st ∧ act_ok a ∧ l1hdln (w2n lfd) st.nxt < dimword (:64) ⇒
  ∃r w' st' evs. l1do lfd (w, st) a = SOME (r, (w', st'), evs) ∧ l0_rely w' ∧
                 small_fds lfd st' ∧ st'.nxt ≤ st.nxt + 1
Proof
  Cases_on ‘a’ >> rw[act_ok_def]
  (* Accept *)
  >- (rename1 ‘Accept l’ >> simp[l1do_def] >> IF_CASES_TAC >> simp[] >>
      ‘small l’ by gvs[small_fds_def, EVERY_MEM] >>
      drule_all sys_accept_ok >> strip_tac >> simp[] >>
      Cases_on ‘l0_res_of out’ >> gvs[]
      >- (gvs[small_fds_def, small_def] >> simp[])
      >> irule small_fds_rdy >> gvs[small_fds_def, EVERY_FILTER_IMP] >> simp[])
  (* Read *)
  >- (rename1 ‘Read h n’ >> simp[l1do_def] >>
      Cases_on ‘ALOOKUP st.tbl h’ >> simp[] >> rename1 ‘ALOOKUP _ _ = SOME f’ >>
      ‘small f’ by metis_tac[small_tbl_lookup] >>
      ‘small_fds lfd (st with tbl := ADELKEY h st.tbl)’ by metis_tac[small_fds_tbl_del] >>
      IF_CASES_TAC
      >- (drule_all l1_close_ok >> strip_tac >> simp[] >>
          imp_res_tac (DB.fetch "honestL1Model" "l1_close_def") >>
          gvs[l1_close_def, AllCaseEqs(), forget_def, set_outbox_def])
      >> IF_CASES_TAC >> simp[] >>
      drule_all sys_recv_ok >> strip_tac >> simp[] >>
      Cases_on ‘l0_res_of out’ >> simp[]
      >- (rw[]
          >- (qspecl_then [‘w'’, ‘st with tbl := ADELKEY h st.tbl’, ‘f’] mp_tac
                (Q.GENL [‘w’, ‘st’, ‘f’] l1_close_ok) >> simp[] >> strip_tac >> simp[] >>
              gvs[l1_close_def, AllCaseEqs(), forget_def, set_outbox_def])
          >> gvs[small_fds_def, EVERY_FILTER_IMP, EVERY_MAP_SND_ADELKEY])
      >> rw[]
      >- (irule small_fds_rdy >> gvs[small_fds_def, EVERY_FILTER_IMP])
      >> qspecl_then [‘w'’, ‘st with tbl := ADELKEY h st.tbl’, ‘f’] mp_tac
           (Q.GENL [‘w’, ‘st’, ‘f’] l1_close_ok) >> simp[] >> strip_tac >> simp[] >>
      gvs[l1_close_def, AllCaseEqs(), forget_def, set_outbox_def])
  (* Write *)
  >> rename1 ‘Write h bs’ >> simp[l1do_def] >>
  Cases_on ‘ALOOKUP st.tbl h’ >> simp[] >> rename1 ‘ALOOKUP _ _ = SOME f’ >>
  ‘small f’ by metis_tac[small_tbl_lookup] >>
  Cases_on ‘MEM f st.gone’ >> simp[] >>
  Cases_on ‘outbox_of st f = []’ >> simp[]
  >- (drule_all sys_send_ok >> disch_then (qspec_then ‘bs’ strip_assume_tac) >> simp[] >>
      conj_tac
      >- (irule small_fds_after_send >> simp[] >> irule small_fds_set_outbox >> simp[])
      >> Cases_on ‘l0_res_of out’ >> simp[after_send_def, set_outbox_def] >> rw[])
  >> conj_tac >- (irule small_fds_set_outbox >> simp[])
  >> simp[set_outbox_def] >> rw[]
QED

(* ------------------------------------------------------------------------
   A round's actions
   ------------------------------------------------------------------------ *)

Theorem l1hdln_mono:
  j ≤ k ⇒ l1hdln n j ≤ l1hdln n k
Proof
  rw[l1hdln_def]
QED

Theorem l1acts_ok:
  ∀acts w st.
    l0_rely w ∧ small_fds lfd st ∧ EVERY act_ok acts ∧
    l1hdln (w2n lfd) (st.nxt + LENGTH acts) < dimword (:64) ⇒
    ∃rs evs w' st'. l1acts lfd (w, st) acts = SOME (rs, evs, (w', st')) ∧
                    l0_rely w' ∧ small_fds lfd st' ∧ st'.nxt ≤ st.nxt + LENGTH acts
Proof
  Induct >> simp[l1acts_def] >> rpt gen_tac >> strip_tac >>
  ‘l1hdln (w2n lfd) st.nxt < dimword (:64)’
    by (qspecl_then [‘st.nxt’, ‘st.nxt + SUC (LENGTH acts)’, ‘w2n lfd’] mp_tac
          (Q.GENL [‘j’, ‘k’, ‘n’] l1hdln_mono) >> gvs[]) >>
  drule_all l1do_ok >> strip_tac >> simp[] >>
  first_x_assum (qspecl_then [‘w'’, ‘st'’] mp_tac) >> impl_tac
  >- (simp[] >>
      qspecl_then [‘st'.nxt + LENGTH acts’, ‘st.nxt + SUC (LENGTH acts)’, ‘w2n lfd’] mp_tac
        (Q.GENL [‘j’, ‘k’, ‘n’] l1hdln_mono) >> gvs[]) >>
  strip_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll, flush and closes
   ------------------------------------------------------------------------ *)

Theorem LENGTH_pollfd_entries:
  ∀k bs. LENGTH bs = 8 * k ⇒ LENGTH (pollfd_entries bs) = k
Proof
  Induct >> rw[] >> ONCE_REWRITE_TAC [pollfd_entries_def] >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem poll_revents_small:
  EVERY (λ(f, e). small f) fes ∧ LENGTH out = 16 + 8 * LENGTH fes ⇒
  EVERY (small o FST) (poll_revents fes out)
Proof
  rw[poll_revents_def] >> CASE_TAC >> simp[] >>
  ‘LENGTH (pollfd_entries (DROP 16 out)) = LENGTH fes’
    by (irule LENGTH_pollfd_entries >> simp[]) >>
  ‘LENGTH (MAP FST fes) =
   LENGTH (MAP (λe. abi_revents (DROP 6 e)) (pollfd_entries (DROP 16 out)))’ by simp[] >>
  simp[EVERY_MEM, FORALL_PROD, MEM_ZIP] >> rw[] >>
  gvs[EVERY_EL, EL_MAP] >> first_x_assum drule >> pairarg_tac >> simp[]
QED

Theorem l1_polls_ok:
  ∀cs w. l0_rely w ∧ EVERY (EVERY (λ(f, e). small f ∧ e < 4)) cs ⇒
         ∃rv w' evs. l1_polls cs w = SOME (rv, w', evs) ∧ l0_rely w' ∧
                     EVERY (small o FST) rv
Proof
  Induct >> simp[l1_polls_def] >> rpt strip_tac >>
  drule_all sys_poll_ok >> strip_tac >> simp[] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  irule poll_revents_small >> gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem l1_flush_ok:
  ∀fs w st. l0_rely w ∧ small_fds lfd st ∧ EVERY small fs ⇒
            ∃w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ l0_rely w' ∧
                         small_fds lfd st' ∧ st'.nxt = st.nxt
Proof
  Induct >> simp[l1_flush_def] >> rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  ‘small h’ by simp[] >>
  drule_all sys_send_ok >> disch_then (qspec_then ‘outbox_of st h’ strip_assume_tac) >>
  simp[] >>
  first_x_assum (qspecl_then [‘w'’, ‘after_send h (l0_res_of out) st’] mp_tac) >>
  impl_tac >- (simp[] >> irule small_fds_after_send >> simp[]) >>
  strip_tac >> simp[] >>
  Cases_on ‘l0_res_of out’ >> gvs[after_send_def, set_outbox_def] >> rw[] >> gvs[]
QED

Theorem l1_reap_ok:
  ∀fs w st. l0_rely w ∧ small_fds lfd st ∧ EVERY small fs ⇒
            ∃w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ l0_rely w' ∧
                         small_fds lfd st' ∧ st'.nxt = st.nxt
Proof
  Induct >> simp[l1_reap_def] >> rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  ‘small h’ by simp[] >>
  drule_all l1_close_ok >> strip_tac >> simp[] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  gvs[l1_close_def, AllCaseEqs(), forget_def, set_outbox_def] >> rw[]
QED

Theorem poll_set_small:
  small_fds lfd st ⇒ EVERY (λ(f, e). small f ∧ e < 4) (l1_poll_set lfd hw st hs)
Proof
  rw[l1_poll_set_def, EVERY_MEM, MEM_FLAT, MEM_MAP, MEM_FILTER, EXISTS_PROD, FORALL_PROD] >>
  gvs[AllCaseEqs()] >> every_case_tac >> gvs[small_fds_def] >>
  imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD, FORALL_PROD] >>
  metis_tac[]
QED

Theorem readable_small:
  EVERY (small o FST) rv ⇒ EVERY small (readable_fds rv) ∧ EVERY small (writable_fds rv)
Proof
  rw[readable_fds_def, writable_fds_def, EVERY_MAP] >>
  gvs[EVERY_MEM, MEM_FILTER]
QED

Theorem l1_tail_ok:
  l0_rely w ∧ small_fds lfd st ⇒
  ∃rdy w' st' evs. l1_tail lfd hw hs (w, st) = SOME (rdy, (w', st'), evs) ∧
                   l0_rely w' ∧ small_fds lfd st' ∧ st'.nxt = st.nxt
Proof
  strip_tac >> simp[l1_tail_def] >>
  ‘EVERY (EVERY (λ(f, e). small f ∧ e < 4)) [l1_poll_set lfd hw st hs]’
    by (simp[] >> irule poll_set_small >> simp[]) >>
  drule_all l1_polls_ok >> strip_tac >> simp[] >>
  drule readable_small >> strip_tac >>
  ‘small_fds lfd (st with rdy := readable_fds rv)’ by (irule small_fds_rdy >> simp[]) >>
  drule_all l1_flush_ok >> strip_tac >> simp[] >>
  ‘EVERY small st'.closing’ by gvs[small_fds_def] >>
  drule_all l1_reap_ok >> strip_tac >> simp[]
QED

(* MAIN: a round completes, keeping the rely and the invariant *)
Theorem l1round_ok:
  l0_rely w ∧ small_fds lfd st ∧ EVERY act_ok acts ∧
  l1hdln (w2n lfd) (st.nxt + LENGTH acts) < dimword (:64) ⇒
  ∃snap w' st' evs. l1round lfd hw hs (w, st) acts = SOME (snap, (w', st'), evs) ∧
                    l0_rely w' ∧ small_fds lfd st' ∧ st'.nxt ≤ st.nxt + LENGTH acts
Proof
  strip_tac >> simp[l1round_def] >>
  drule_all l1acts_ok >> strip_tac >> simp[] >>
  drule_all l1_tail_ok >> disch_then (qspecl_then [‘hw’, ‘hs’] strip_assume_tac) >>
  simp[]
QED

(* MAIN: the whole run never makes a failing L0 call, provided every round
   the computation reaches is well formed: its actions read 0 < n < 2^64
   bytes, and the handle numbers do not overflow (the handle layer's
   hrun_ok asks the same) *)
Definition l2_ok_def:
  l2_ok lfd hw ifds m ws0 ⇔
    ∀n h ws evs. lrounds lfd hw ifds m ws0 n = SOME (h, ws, evs) ⇒
      EVERY act_ok (new_actions (log_of m) h) ∧
      l1hdln (w2n lfd) ((SND ws).nxt + LENGTH (new_actions (log_of m) h)) < dimword (:64)
End

Theorem lrounds_ok:
  l0_rely w0 ∧ small_fds lfd st0 ∧ l2_ok lfd hw ifds m (w0, st0) ⇒
  ∀n. ∃h w st evs. lrounds lfd hw ifds m (w0, st0) n = SOME (h, (w, st), evs) ∧
                   l0_rely w ∧ small_fds lfd st
Proof
  strip_tac >> Induct >- simp[lrounds_def] >>
  gvs[] >> simp[lrounds_def] >>
  qpat_x_assum ‘l2_ok _ _ _ _ _’ (mp_tac o REWRITE_RULE [l2_ok_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  ‘l1hdln (w2n lfd) (st.nxt + LENGTH (new_actions (log_of m) h)) < dimword (:64)’
    by gvs[] >>
  drule_all l1round_ok >>
  disch_then (qspecl_then [‘hw’, ‘ifds h’] strip_assume_tac) >> simp[]
QED

Theorem lrun_ok_thm:
  l0_rely w0 ∧ small_fds lfd st0 ∧ l2_ok lfd hw ifds m (w0, st0) ⇒
  lrun_ok lfd hw ifds m (w0, st0)
Proof
  rw[lrun_ok_def] >> drule_all lrounds_ok >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  simp[]
QED
