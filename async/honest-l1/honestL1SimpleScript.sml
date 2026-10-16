(*
  The SIMPLE L0 world, and L1's wrappers in it (design/36 R3).

  simple0 w: the instance of the L0 world in which nothing the old models
  lacked can happen: the kernel takes every send whole, recv returns all
  that is available, no call fails transiently, no connection breaks, the
  fd limit is the C's (2^31), and arrivals come only before polls (time
  passes only at polls, as in versions 1 and 2).  The other world choices
  (ERR/HUP shown, ...) are left free: they only matter for broken or shut
  channels.

  In it, L1's wrappers are today's calls (one L0 call per action, the
  same response): here, write_simple (a Write is one sys_send, fully
  accepted, leaving no outbox).
*)
Theory honestL1Simple
Ancestors
  honestL1Model honestL1Props honestL0World honestL0WorldProps honestL0Rely
  honestL0 ffiSpikeSocketFFI asyncM3World Marshalling
Libs
  preamble

Definition env_simple_def:
  env_simple (env : num -> lcall list -> mlstring -> l0_arrival list) ⇔
    (∀n h nm. nm ≠ «sys_poll» ⇒ env n h nm = []) ∧
    (∀n h nm j e k. ¬MEM (LBreak j e k) (env n h nm))
End

Definition simple0_def:
  simple0 (w : l0world) ⇔
    (∀j h b n. w.ch.takes j h b n = n) ∧
    (∀j h a. w.ch.short j h a = a) ∧
    (∀h. w.ch.transient h = NONE) ∧
    (∀h. w.ch.listen_fails h = NONE) ∧
    (∀h. w.ch.close_intr h = NONE) ∧
    w.fd_limit = 2 ** 31 ∧
    env_simple w.env
End

(* Before any call but a poll, time passes and nothing arrives *)
Theorem tick_simple:
  simple0 w ∧ nm ≠ «sys_poll» ⇒ l0_tick nm w = w with clock := w.clock + 1
Proof
  rw[simple0_def, env_simple_def, l0_tick_def]
QED

Theorem chan_of_clock[simp]:
  l0_chan_of (w with clock := c) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def]
QED

Theorem fd_ok_fd_bytes[simp]:
  TAKE 8 (fd_bytes f ++ bs) = fd_bytes f ∧ DROP 8 (fd_bytes f ++ bs) = bs
Proof
  ‘LENGTH (fd_bytes f) = 8’ by simp[] >>
  metis_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

(* A send on a healthy channel takes everything *)
Theorem send_simple:
  simple0 w ∧ l0_chan_of w f = SOME j ∧ ¬(EL j w.chans).broken ∧ ¬(EL j w.chans).shut ∧
  ¬(EL j w.chans).connecting ∧ w2n f < 2 ** 31 ⇒
  ∃w'. sys_send f bs w =
         SOME (enc_res (Ok (LENGTH bs)), w',
               IO_event (ExtCall «sys_send») (fd_bytes f ++ bs)
                 (ZIP (REPLICATE 13 0w, enc_res (Ok (LENGTH bs))))) ∧
       l0_chan_of w' f = SOME j ∧ (EL j w'.chans).sent = (EL j w.chans).sent ++ bs ∧
       w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >>
  ‘l0_tick «sys_send» w = w with clock := w.clock + 1’ by simp[tick_simple] >>
  gvs[simple0_def] >>
  simp[sys_send_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def, fd_ok_def,
       l0_send_def] >>
  IF_CASES_TAC >> gvs[] >>
  gvs[l0_chan_of_def, AllCaseEqs(), upd_lchan_def, EL_LUPDATE]
QED

Theorem l0_res_of_ok:
  n < 256 ** 8 ⇒ l0_res_of (enc_res (Ok n)) = Ok n
Proof
  rw[l0_res_of_def] >>
  ‘l0_res_ok (Ok n)’ by simp[l0_res_ok_def] >>
  drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >> simp[]
QED

(* R3, write: in the simple world a Write to a healthy connection whose
   outbox is empty is ONE sys_send of exactly bs, answered Wrote, and it
   leaves the outbox empty: today's «sock_write» *)
Theorem write_simple:
  simple0 w ∧ ALOOKUP st.tbl h = SOME f ∧ ¬MEM f st.gone ∧ outbox_of st f = [] ∧
  l0_chan_of w f = SOME j ∧ ¬(EL j w.chans).broken ∧ ¬(EL j w.chans).shut ∧
  ¬(EL j w.chans).connecting ∧ w2n f < 2 ** 31 ∧ LENGTH bs < 256 ** 8 ⇒
  ∃w' st'. l1do lfd (w, st) (Write h bs) =
             SOME (Wrote, (w', st'),
                   [IO_event (ExtCall «sys_send») (fd_bytes f ++ bs)
                      (ZIP (REPLICATE 13 0w, enc_res (Ok (LENGTH bs))))]) ∧
           outbox_of st' f = [] ∧ st'.tbl = st.tbl ∧ st'.gone = st.gone ∧
           st'.rdy = st.rdy ∧ (EL j w'.chans).sent = (EL j w.chans).sent ++ bs
Proof
  strip_tac >>
  drule_all send_simple >> disch_then (qspec_then ‘bs’ strip_assume_tac) >>
  simp[l1do_def, l0_res_of_ok, after_send_def, outbox_of_set_outbox] >>
  simp[set_outbox_def]
QED

Theorem l0_res_of_ok_app:
  n < 256 ** 8 ⇒ l0_res_of (enc_res (Ok n) ++ rest) = Ok n
Proof
  rw[l0_res_of_def] >>
  ‘l0_res_ok (Ok n)’ by simp[l0_res_ok_def] >>
  drule dec_enc_res >> disch_then (qspec_then ‘rest’ mp_tac) >> simp[]
QED

Theorem LENGTH_enc_res_ok[local]:
  LENGTH (enc_res (Ok n)) = 13
Proof
  simp[enc_res_def, LENGTH_n2w8]
QED

(* recv in the L0 world, on a channel with input, when nothing fails and
   recv returns all that is available *)
Theorem l0_recv_data:
  (∀h. w.ch.transient h = NONE) ∧ (∀j h a. w.ch.short j h a = a) ∧
  l0_chan_of w f = SOME j ∧ (EL j w.chans).inbox ≠ [] ∧ ¬(EL j w.chans).connecting ⇒
  l0_recv f n w =
    (Ok (MIN n (LENGTH (EL j w.chans).inbox)), TAKE n (EL j w.chans).inbox,
     upd_lchan j (λc. c with inbox := DROP n c.inbox) w)
Proof
  rw[l0_recv_def] >>
  simp[TAKE_TAKE_MIN] >> rw[MIN_DEF] >>
  gvs[NOT_LESS, TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG] >>
  simp[upd_lchan_def] >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  rw[DROP_LENGTH_TOO_LONG]
QED

Theorem LENGTH_TAKE_MIN:
  LENGTH (TAKE n l) = MIN n (LENGTH l)
Proof
  rw[LENGTH_TAKE_EQ, MIN_DEF]
QED

(* R3, read: in the simple world a Read of a handle whose fd the poll
   reported readable, with data waiting, is ONE sys_recv, answered with
   exactly the data today's «sock_read» returns: TAKE n of the input *)
Theorem read_simple:
  simple0 w ∧ 0 < n ∧ n < 256 ** 8 ∧ ALOOKUP st.tbl h = SOME f ∧ ¬MEM f st.gone ∧
  MEM f st.rdy ∧ l0_chan_of w f = SOME j ∧ (EL j w.chans).inbox ≠ [] ∧
  ¬(EL j w.chans).connecting ∧ w2n f < 2 ** 31 ⇒
  ∃w' ev. l1do lfd (w, st) (Read h n) =
            SOME (Got (SOME (TAKE n (EL j w.chans).inbox)), (w', st), [ev]) ∧
          l0_chan_of w' f = SOME j ∧
          (EL j w'.chans).inbox = DROP n (EL j w.chans).inbox
Proof
  strip_tac >> ‘w2n f < 2147483648’ by gvs[] >>
  ‘l0_tick «sys_recv» w = w with clock := w.clock + 1’ by simp[tick_simple] >>
  ‘l0_recv f n (w with clock := w.clock + 1) =
     (Ok (MIN n (LENGTH (EL j w.chans).inbox)), TAKE n (EL j w.chans).inbox,
      upd_lchan j (λc. c with inbox := DROP n c.inbox) (w with clock := w.clock + 1))’
    by (mp_tac (Q.INST [‘w’ |-> ‘w with clock := w.clock + 1’] l0_recv_data) >>
        gvs[simple0_def]) >>
  qabbrev_tac ‘inb = (EL j w.chans).inbox’ >>
  qabbrev_tac ‘k = MIN n (LENGTH inb)’ >>
  ‘0 < k ∧ k < 256 ** 8’ by (unabbrev_all_tac >> Cases_on ‘(EL j w.chans).inbox’ >>
                             gvs[MIN_DEF]) >>
  ‘∀rest. l0_res_of (enc_res (Ok k) ++ rest) = Ok k’ by simp[l0_res_of_ok_app] >>
  ‘LENGTH (TAKE n inb) = k’ by simp[Abbr ‘k’, LENGTH_TAKE_MIN] >>
  simp[l1do_def, sys_recv_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def,
       fd_ok_def] >>
  asm_simp_tac (srw_ss()) [DROP_APPEND, LENGTH_enc_res_ok, TAKE_APPEND] >>
  ‘TAKE k (TAKE n inb) = TAKE n inb’ by metis_tac[TAKE_LENGTH_ID] >>
  qmatch_goalsub_abbrev_tac ‘l0_res_of out’ >>
  ‘l0_res_of out = Ok k’ by (simp[Abbr ‘out’] >> metis_tac[APPEND_ASSOC]) >>
  simp[] >>
  gvs[l0_chan_of_def, AllCaseEqs(), upd_lchan_def, EL_LUPDATE, Abbr ‘inb’]
QED

Theorem lowest_fd_clock[simp]:
  lowest_fd (w with clock := c) = lowest_fd w
Proof
  simp[lowest_fd_def, l0_used_def]
QED

(* R3, accept: in the simple world an Accept of a listener the poll
   reported readable, with a connection pending, is ONE sys_accept; it
   returns the lowest free fd ([P 2.6]) under a fresh handle: today's
   «sock_accept» with version 2's fd choice *)
Theorem accept_simple:
  simple0 w ∧ MEM l st.rdy ∧ ¬st.exhausted ∧
  FILTER (λ(l', p, q). l' = l) w.listeners = (l, p, j :: q) :: rest ∧
  ¬(EL j w.chans).broken ∧ w2n (lowest_fd w) < 2 ** 31 ∧ w2n l < 2 ** 31 ∧
  l1hdln (w2n lfd) st.nxt < dimword (:64) ⇒
  ∃w' ev. l1do lfd (w, st) (Accept l) =
            SOME (Accepted (SOME (l1hdl lfd st.nxt)),
                  (w', st with <| tbl := (l1hdl lfd st.nxt, lowest_fd w) :: st.tbl;
                                  nxt := st.nxt + 1 |>), [ev]) ∧
          ALOOKUP w'.open_fds (lowest_fd w) = SOME j
Proof
  strip_tac >> ‘w2n l < 2147483648 ∧ w2n (lowest_fd w) < 2147483648’ by gvs[] >>
  ‘l0_tick «sys_accept» w = w with clock := w.clock + 1’ by simp[tick_simple] >>
  ‘w2n (lowest_fd w) < 256 ** 8’ by gvs[] >>
  gvs[simple0_def] >>
  simp[l1do_def, sys_accept_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def,
       fd_ok_def, l0_accept_def, l0_alloc_def] >>
  simp[l0_res_of_ok]
QED
