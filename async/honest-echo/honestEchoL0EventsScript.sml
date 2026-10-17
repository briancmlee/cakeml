(*
  Route (d), stage S2a (design/46): what each of L1's calls contributes
  to the spec's episode fold (honestEchoL0Trace).  An accept that returns
  Ok k opens an episode on n2w k; a close that returns Ok ends f's; a
  recv on f contributes the bytes it returned, a send on f the bytes the
  kernel took; a poll contributes nothing.
*)
Theory honestEchoL0Events
Ancestors
  ffi Marshalling honestL0 honestL0World honestL0WorldProps honestL0Rely honestL1Model
  honestEchoL0Spec honestEchoL0Trace ffiSpikeSocketFFI
Libs
  preamble

(* An L0 call's event, and its decoded result *)
Theorem l0_do_event:
  l0_rely w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒
  ev = IO_event (ExtCall n) conf (ZIP (REPLICATE alen 0w, out)) ∧
  LENGTH out = alen ∧
  l0_ev_res (ZIP (REPLICATE alen 0w, out)) = dec_res out
Proof
  rw[l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> rw[] >>
  simp[l0_ev_res_def, MAP_ZIP]
QED

Theorem l0_res_of_Ok:
  l0_res_of out = Ok k ⇔ dec_res out = SOME (Ok k)
Proof
  rw[l0_res_of_def] >> every_case_tac >> simp[]
QED

Theorem fd_bytes_app[local,simp]:
  TAKE 8 (fd_bytes f ++ bs) = fd_bytes f ∧ DROP 8 (fd_bytes f ++ bs) = bs ∧
  LENGTH (fd_bytes f) = 8
Proof
  ‘LENGTH (fd_bytes f) = 8’ by simp[fd_bytes_def, LENGTH_n2w8] >>
  ‘8 = LENGTH (fd_bytes f)’ by simp[] >> pop_assum SUBST1_TAC >>
  simp_tac std_ss [TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem bytes_fd_fd_bytes[local,simp]:
  bytes_fd (fd_bytes f) = f
Proof
  simp[bytes_fd_def]
QED

Theorem sys_accept_event:
  l0_rely w ∧ sys_accept l w = SOME (out, w', ev) ⇒
  l0_event_accepted ev =
    (case l0_res_of out of Ok k => SOME (n2w k) | Fail _ _ => NONE) ∧
  l0_event_closed ev = NONE ∧ recv_fd ev = NONE ∧ send_fd ev = NONE
Proof
  rw[sys_accept_def] >> drule_all l0_do_event >> rw[] >>
  simp[l0_event_accepted_def, l0_event_closed_def, recv_fd_def, send_fd_def,
       l0_res_of_def] >>
  every_case_tac >> gvs[]
QED

Theorem sys_recv_event:
  l0_rely w ∧ sys_recv f n w = SOME (out, w', ev) ⇒
  recv_fd ev = SOME f ∧
  l0_event_recv f ev =
    (case l0_res_of out of Ok k => TAKE k (DROP 13 out) | Fail _ _ => []) ∧
  l0_event_accepted ev = NONE ∧ l0_event_closed ev = NONE ∧ send_fd ev = NONE
Proof
  rw[sys_recv_def] >> drule_all l0_do_event >> rw[] >>
  simp[l0_event_accepted_def, l0_event_closed_def, recv_fd_def, send_fd_def,
       l0_event_recv_def, l0_res_of_def, MAP_ZIP] >>
  every_case_tac >> gvs[]
QED

Theorem sys_send_event:
  l0_rely w ∧ sys_send f bs w = SOME (out, w', ev) ⇒
  send_fd ev = SOME f ∧
  l0_event_sent f ev =
    (case l0_res_of out of Ok k => TAKE k bs | Fail _ _ => []) ∧
  l0_event_accepted ev = NONE ∧ l0_event_closed ev = NONE ∧ recv_fd ev = NONE
Proof
  rw[sys_send_def] >> drule_all l0_do_event >> rw[] >>
  simp[l0_event_accepted_def, l0_event_closed_def, recv_fd_def, send_fd_def,
       l0_event_sent_def, l0_res_of_def] >>
  every_case_tac >> gvs[]
QED

Theorem sys_close_event:
  l0_rely w ∧ sys_close f w = SOME (out, w', ev) ⇒
  l0_event_closed ev =
    (case l0_res_of out of Ok _ => SOME f | Fail _ _ => NONE) ∧
  l0_event_accepted ev = NONE ∧ recv_fd ev = NONE ∧ send_fd ev = NONE
Proof
  rw[sys_close_def] >> drule_all l0_do_event >> rw[] >>
  simp[l0_event_accepted_def, l0_event_closed_def, recv_fd_def, send_fd_def,
       l0_res_of_def] >>
  every_case_tac >> gvs[]
QED

(* D20: a call whose buffer carries data in *)
Theorem l0_do_buf_event:
  l0_rely w ∧ l0_do_buf n conf bytes w = SOME (out, w', ev) ⇒
  ev = IO_event (ExtCall n) conf (ZIP (bytes, out)) ∧ LENGTH out = LENGTH bytes ∧
  l0_rely w'
Proof
  rw[l0_do_buf_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> rw[]
QED

Theorem sys_poll_event:
  l0_rely w ∧ sys_poll fes w = SOME (out, w', ev) ⇒
  l0_event_accepted ev = NONE ∧ l0_event_closed ev = NONE ∧
  recv_fd ev = NONE ∧ send_fd ev = NONE ∧ l0_rely w'
Proof
  rw[sys_poll_def] >> drule_all l0_do_buf_event >> rw[] >>
  simp[l0_event_accepted_def, l0_event_closed_def, recv_fd_def, send_fd_def]
QED
