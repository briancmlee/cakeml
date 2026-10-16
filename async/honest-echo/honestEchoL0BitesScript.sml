(*
  echo_safe_l0 bites (user's condition, before the P3 proof): it rejects
  a server that swaps clients, drops a byte, duplicates a byte, or leaks
  a connection's bytes to the next connection on the same (reused) fd;
  and it is not vacuous: an ideal trace, with a short send, satisfies it.

  The events are encoded as the L0 world returns them: the conf is the
  8-byte fd (and, for a send, the bytes), and the output is the 13-byte
  result header enc_res (and, for a recv, the data).
*)
Theory honestEchoL0Bites
Ancestors
  llist ffi Marshalling honestL0 honestEchoL0Spec ffiSpikeSocketFFI
Libs
  preamble

(* Successful calls, as L0 encodes them *)
Definition acc_ev_def:
  acc_ev (l : word64) (f : word64) =
    IO_event (ExtCall «sys_accept») (fd_bytes l)
      (ZIP (REPLICATE 13 0w, enc_res (Ok (w2n f))))
End

Definition recv_ev_def:
  recv_ev (f : word64) (bs : word8 list) =
    IO_event (ExtCall «sys_recv») (fd_bytes f)
      (ZIP (REPLICATE (13 + LENGTH bs) 0w, enc_res (Ok (LENGTH bs)) ++ bs))
End

(* A send of bs of which the kernel took k bytes *)
Definition send_ev_def:
  send_ev (f : word64) (bs : word8 list) k =
    IO_event (ExtCall «sys_send») (fd_bytes f ++ bs)
      (ZIP (REPLICATE 13 0w, enc_res (Ok k)))
End

Definition close_ev_def:
  close_ev (f : word64) =
    IO_event (ExtCall «sys_close») (fd_bytes f)
      (ZIP (REPLICATE 13 0w, enc_res (Ok 0)))
End

Theorem LENGTH_fd_bytes[local,simp]:
  LENGTH (fd_bytes f) = 8
Proof
  simp[fd_bytes_def, LENGTH_n2w8]
QED

(* As honest-l1's fd_ok_fd_bytes; local, so that the spec's bites need no
   L1 theory *)
Theorem fd_bytes_app[local,simp]:
  TAKE 8 (fd_bytes f ++ bs) = fd_bytes f ∧ DROP 8 (fd_bytes f ++ bs) = bs
Proof
  ‘8 = LENGTH (fd_bytes f)’ by simp[] >> pop_assum SUBST1_TAC >>
  simp_tac std_ss [TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

Theorem bytes_fd_fd_bytes[local,simp]:
  bytes_fd (fd_bytes f) = f
Proof
  simp[bytes_fd_def]
QED

Theorem LENGTH_enc_res_Ok[local,simp]:
  LENGTH (enc_res (Ok k)) = 13
Proof
  simp[enc_res_def, LENGTH_n2w8]
QED

Theorem w2n_lt_256_8[local]:
  w2n (f : word64) < 256 ** 8
Proof
  assume_tac (INST_TYPE [alpha |-> “:64”] w2n_lt) >> fs[]
QED

Theorem ev_res_Ok[local]:
  k < 256 ** 8 ⇒
  l0_ev_res (ZIP (REPLICATE (LENGTH rest + 13) 0w, enc_res (Ok k) ++ rest)) = SOME (Ok k)
Proof
  strip_tac >> simp[l0_ev_res_def, MAP_ZIP] >>
  irule dec_enc_res >> simp[l0_res_ok_def]
QED

Theorem ev_res_Ok_13[local]:
  k < 256 ** 8 ⇒ l0_ev_res (ZIP (REPLICATE 13 0w, enc_res (Ok k))) = SOME (Ok k)
Proof
  strip_tac >> drule (Q.INST [‘rest’ |-> ‘[]’] ev_res_Ok) >> simp[]
QED

Theorem DROP_enc_res_Ok[local]:
  k < 256 ** 8 ⇒ DROP 13 (MAP SND (ZIP (REPLICATE (LENGTH rest + 13) 0w, enc_res (Ok k) ++ rest))) = rest
Proof
  strip_tac >> simp[MAP_ZIP] >>
  ‘13 = LENGTH (enc_res (Ok k))’ by simp[] >> pop_assum SUBST1_TAC >>
  simp_tac std_ss [DROP_LENGTH_APPEND]
QED

(* What the spec's event functions see *)
Theorem l0_events_of[local,simp]:
  l0_event_accepted (acc_ev l f) = SOME f ∧
  l0_event_accepted (recv_ev f bs) = NONE ∧
  l0_event_accepted (send_ev f bs k) = NONE ∧
  l0_event_accepted (close_ev f) = NONE ∧
  l0_event_closed (acc_ev l f) = NONE ∧
  l0_event_closed (recv_ev f bs) = NONE ∧
  l0_event_closed (send_ev f bs k) = NONE ∧
  l0_event_closed (close_ev f) = SOME f ∧
  l0_event_recv g (acc_ev l f) = [] ∧
  (LENGTH bs < 256 ** 8 ⇒
   l0_event_recv g (recv_ev f bs) = if f = g then bs else []) ∧
  l0_event_recv g (send_ev f bs k) = [] ∧
  l0_event_recv g (close_ev f) = [] ∧
  l0_event_sent g (acc_ev l f) = [] ∧
  l0_event_sent g (recv_ev f bs) = [] ∧
  (k < 256 ** 8 ⇒
   l0_event_sent g (send_ev f bs k) = if f = g then TAKE k bs else []) ∧
  l0_event_sent g (close_ev f) = []
Proof
  rpt conj_tac >> rpt strip_tac >>
  simp[acc_ev_def, recv_ev_def, send_ev_def, close_ev_def,
       l0_event_accepted_def, l0_event_closed_def, l0_event_recv_def,
       l0_event_sent_def, ev_res_Ok_13, ev_res_Ok, DROP_enc_res_Ok,
       w2n_lt_256_8, TAKE_APPEND1, DROP_LENGTH_APPEND] >>
  rw[]
QED

val bite_tac =
  strip_tac >> simp[echo_safe_l0_def, PULL_EXISTS] >>
  first_assum (irule_at Any) >>
  simp[l0_sent_def, l0_read_def, l0_accepted_def, l0_ep_events_def,
       alistTheory.ADELKEY_def];

(* Bite 1, swapped clients: the server read "a" from client 0 (fd 4) and
   "b" from client 1 (fd 5), and sends "b" to client 0 *)
Theorem bite_swapped:
  LPREFIX (fromList [acc_ev 3w 4w; acc_ev 3w 5w; recv_ev 4w [97w]; recv_ev 5w [98w];
                     send_ev 4w [98w] 1]) io ⇒
  ¬echo_safe_l0 io
Proof
  bite_tac >> qexists_tac ‘0’ >> EVAL_TAC
QED

(* Bite 2, a dropped byte: read "ab", sent "b" *)
Theorem bite_dropped:
  LPREFIX (fromList [acc_ev 3w 4w; recv_ev 4w [97w; 98w]; send_ev 4w [98w] 1]) io ⇒
  ¬echo_safe_l0 io
Proof
  bite_tac >> qexists_tac ‘0’ >> EVAL_TAC
QED

(* Bite 3, a duplicated byte: read "a", sent "aa" (the kernel took both) *)
Theorem bite_duplicated:
  LPREFIX (fromList [acc_ev 3w 4w; recv_ev 4w [97w]; send_ev 4w [97w; 97w] 2]) io ⇒
  ¬echo_safe_l0 io
Proof
  bite_tac >> qexists_tac ‘0’ >> EVAL_TAC
QED

(* Bite 4, a leak across fd reuse: client 0 sends "s" on fd 4 and the
   server closes fd 4; the kernel gives fd 4 to client 1, and the server
   sends it "s" *)
Theorem bite_fd_reuse_leak:
  LPREFIX (fromList [acc_ev 3w 4w; recv_ev 4w [115w]; close_ev 4w; acc_ev 3w 4w;
                     send_ev 4w [115w] 1]) io ⇒
  ¬echo_safe_l0 io
Proof
  bite_tac >> qexists_tac ‘1’ >> EVAL_TAC
QED

(* The kernel's count matters: of a send of "ax" after reading "a", the
   kernel taking both bytes is unsafe (taking one is safe, below) *)
Theorem bite_send_count:
  LPREFIX (fromList [acc_ev 3w 4w; recv_ev 4w [97w]; send_ev 4w [97w; 120w] 2]) io ⇒
  ¬echo_safe_l0 io
Proof
  bite_tac >> qexists_tac ‘0’ >> EVAL_TAC
QED

(* Non-vacuity: an ideal trace of two interleaved clients, with a short
   send (the kernel takes 1 of 2 bytes, the rest is sent again), a close,
   and fd reuse, is safe *)
Definition ideal_trace_def:
  ideal_trace =
    [acc_ev 3w 4w; recv_ev 4w [104w; 105w]; acc_ev 3w 5w; recv_ev 5w [120w];
     send_ev 4w [104w; 105w] 1; send_ev 5w [120w] 1; send_ev 4w [105w] 1;
     close_ev 4w; acc_ev 3w 4w; recv_ev 4w [121w]; send_ev 4w [121w] 1]
End

(* A finite trace is safe if every prefix is: a check by evaluation *)
Definition safe_upto_def:
  safe_upto l ⇔
    EVERY (λn. EVERY (λj. l0_sent j (TAKE n l) ≼ l0_read j (TAKE n l))
                     (COUNT_LIST (LENGTH (l0_accepted (TAKE n l)))))
          (COUNT_LIST (SUC (LENGTH l)))
End

Theorem safe_upto_echo_safe_l0:
  safe_upto l ⇒ echo_safe_l0 (fromList l)
Proof
  rw[safe_upto_def, echo_safe_l0_def, LPREFIX_fromList, from_toList,
     rich_listTheory.IS_PREFIX_EQ_TAKE, EVERY_MEM, rich_listTheory.MEM_COUNT_LIST] >>
  Cases_on ‘j < LENGTH (l0_accepted (TAKE n l))’ >- (first_x_assum irule >> simp[]) >>
  qexists_tac ‘0’ >> simp[l0_sent_def]
QED

Theorem echo_safe_l0_ideal:
  echo_safe_l0 (fromList ideal_trace)
Proof
  irule safe_upto_echo_safe_l0 >> EVAL_TAC
QED
