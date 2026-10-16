(*
  The CF specs of the socket calls against the version-2 world.

  The program owns the version-2 socket part, with its I/O events
  explicit: SOCKETS2_EV s evs.  The Socket module's poll, accept, read and
  write (version 1's code, unchanged) and SocketClose.close each make one
  FFI call; their specs are stated with the version-2 model's operations
  (sock_poll2, sock_accept2, sock_read2, sock_write2, sock_close2 of
  lifetimeWorld) and record the call's event.  The events of accept, read
  and write have version 1's shapes (loopPollWorld's act_event), since the
  encodings are the same.
*)
Theory lifetimeProof
Ancestors
  ml_translator cfHeapsBase cfMain Marshalling Word8ArrayProof mlstring
  socketWorld socketProg socketProof loopPollWorld
  lifetimeWorld lifetimePart lifetimeProg
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "lifetimeProg";

(* SOCKETS2_EV s evs: the program owns the version-2 socket part, in state
   s, with the events evs so far *)
Definition SOCKETS2_EV_def:
  SOCKETS2_EV s evs =
    one (FFI_part (sockets2_encode s) (mk_ffi_next sockets2_ffi_part)
           socket2_names evs)
End

(* The event of «sock_poll» on fds in state s *)
Definition spoll2_event_def:
  spoll2_event fds s =
    IO_event (ExtCall «sock_poll») (fds_bytes fds)
      (ZIP (REPLICATE (LENGTH fds) 0w,
            MAP (λfd. if is_ready2 (tick2 s) fd then 1w else 0w) fds))
End

(* The event of «sock_close» on c *)
Definition close_event_def:
  close_event c = IO_event (ExtCall «sock_close») (fd_bytes c) []
End

Overload bytes_str = “λbs:word8 list. implode (MAP (CHR o w2n) bs)”

(*---------------------------------------------------------------------------*)
(* The FFI calls on the buffers the functions build *)

Theorem sock_read2_LENGTH:
  sock_read2 c n s = SOME (SOME d, s') ⇒ LENGTH d ≤ n
Proof
  rw [sock_read2_def, AllCaseEqs()] \\ simp [LENGTH_TAKE_EQ]
QED

Theorem ffi_sock_poll2_call:
  ffi_sock_poll2 (fds_bytes fds) (REPLICATE (LENGTH fds) 0w) s =
    SOME (FFIreturn (MAP (λfd. if is_ready2 (tick2 s) fd then 1w else 0w) fds)
                    (tick2 s))
Proof
  simp [ffi_sock_poll2_def]
QED

Theorem ffi_sock_accept2_call:
  sock_accept2 l s = SOME (r, s') ⇒
  ffi_sock_accept2 (fd_bytes l) (REPLICATE 9 0w) s =
    SOME (FFIreturn (case r of
                     | NONE => 0w :: REPLICATE 8 0w
                     | SOME c => 1w :: fd_bytes c) s')
Proof
  rw [ffi_sock_accept2_def] \\ Cases_on ‘r’ \\ gvs [] \\ EVAL_TAC
QED

Theorem TL_REPLICATE_9[local]:
  TL (REPLICATE (n + 9) x) = REPLICATE (n + 8) x
Proof
  ‘n + 9 = SUC (n + 8)’ by simp [] \\ pop_assum SUBST1_TAC \\ simp [REPLICATE]
QED

Theorem ffi_sock_read2_call:
  sock_read2 c n s = SOME (r, s') ∧ 0 < n ⇒
  ffi_sock_read2 (fd_bytes c) (REPLICATE (n + 9) 0w) s =
    SOME (FFIreturn (read_bytes n r) s')
Proof
  rw [ffi_sock_read2_def, read_bytes_def, TL_REPLICATE_9]
  \\ every_case_tac \\ gvs []
QED

Theorem ffi_sock_write2_call:
  sock_write2 c bs s = SOME s' ⇒
  ffi_sock_write2 (fd_bytes c ++ bs) [] s = SOME (FFIreturn [] s')
Proof
  rw [ffi_sock_write2_def, TAKE_APPEND1, DROP_APPEND, DROP_LENGTH_TOO_LONG]
  \\ gvs [TAKE_LENGTH_ID_rwt]
QED

Theorem ffi_sock_close2_call:
  sock_close2 c s = SOME s' ⇒
  ffi_sock_close2 (fd_bytes c) [] s = SOME (FFIreturn [] s')
Proof
  rw [ffi_sock_close2_def]
QED

Theorem cl_conf_fd_bytes:
  cl_conf (w2n fd) = implode (MAP (CHR o w2n) (fd_bytes fd))
Proof
  ‘cl_byte_char = CHR o w2n’
    by simp [FUN_EQ_THM, fetch "lifetimeProg" "cl_byte_char_def"]
  \\ simp [fetch "lifetimeProg" "cl_conf_def", fetch "lifetimeProg" "cl_n2w8_def",
           fd_bytes_def]
QED

(*---------------------------------------------------------------------------*)
(* The specs *)

Theorem Socket_poll2_spec_ev:
  LIST_TYPE NUM (MAP w2n fds) fdsv ⇒
  app (p:'ffi ffi_proj) Socket_poll_v [fdsv]
    (SOCKETS2_EV s evs)
    (POSTv v. &LIST_TYPE NUM (MAP w2n (FST (sock_poll2 fds s))) v *
              SOCKETS2_EV (tick2 s) (evs ++ [spoll2_event fds s]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "socketProg" "Socket_poll_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ xlet ‘POSTv uv. W8ARRAY av
             (MAP (λfd. if is_ready2 (tick2 s) fd then 1w else 0w) fds) *
           SOCKETS2_EV (tick2 s) (evs ++ [spoll2_event fds s])’
  >- (simp [SOCKETS2_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fds_conf_fds_bytes]
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘sockets2_encode s’,
                   ‘mk_ffi_next sockets2_ffi_part’, ‘socket2_names’, ‘evs’]
      \\ xsimpl
      \\ simp [sockets2_ffi_part_def, mk_ffi_next_def, ffi_sock_poll2_call,
               spoll2_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ qmatch_goalsub_abbrev_tac ‘W8ARRAY av flagbytes’
  \\ ‘LENGTH flagbytes = LENGTH fds’ by simp [Abbr ‘flagbytes’]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av flagbytes * SOCKETS2_EV (tick2 s) (evs ++ [spoll2_event fds s])’,
               ‘MAP (CHR o w2n) (TAKE (LENGTH fds) flagbytes)’,
               ‘MAP w2n fds’]
  \\ gvs [Abbr ‘flagbytes’] \\ xsimpl
  \\ simp [CHR_o_w2n, TAKE_LENGTH_ID_rwt]
  \\ rpt strip_tac \\ fs [ready_of_flags, sock_poll2_def]
  >- (‘(λfd. is_ready2 (tick2 s) fd) = is_ready2 (tick2 s)’ by simp [FUN_EQ_THM]
      \\ fs [])
  \\ xsimpl
QED

Theorem Socket_accept2_spec_ev:
  NUM (w2n l) lv ∧ sock_accept2 l s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_accept_v [lv] (SOCKETS2_EV s evs)
    (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n r) v *
              SOCKETS2_EV s' (evs ++ [act_event (Accept l) (Accepted r)]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "socketProg" "Socket_accept_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ qabbrev_tac ‘resbytes = case r of
                             | NONE => 0w :: REPLICATE 8 0w
                             | SOME c => 1w :: fd_bytes c’
  \\ xlet ‘POSTv uv. W8ARRAY av resbytes *
             SOCKETS2_EV s' (evs ++ [act_event (Accept l) (Accepted r)])’
  >- (simp [SOCKETS2_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qexistsl [‘fd_bytes l’, ‘emp’, ‘sockets2_encode s’,
                   ‘mk_ffi_next sockets2_ffi_part’, ‘socket2_names’, ‘evs’]
      \\ xsimpl
      \\ drule ffi_sock_accept2_call \\ strip_tac
      \\ simp [sockets2_ffi_part_def, mk_ffi_next_def, act_event_def,
               Abbr ‘resbytes’]
      \\ xsimpl \\ EVAL_TAC)
  \\ ‘LENGTH resbytes = 9’ by (Cases_on ‘r’ \\ simp [Abbr ‘resbytes’])
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av resbytes *
                SOCKETS2_EV s' (evs ++ [act_event (Accept l) (Accepted r)])’,
               ‘implode (MAP (CHR o w2n) resbytes)’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ qunabbrev_tac ‘resbytes’ \\ Cases_on ‘r’
  \\ full_simp_tac std_ss [option_case_def, decode_accept_none,
                          decode_accept_some, OPTION_MAP_DEF]
QED

Theorem Socket_read2_spec_ev:
  NUM (w2n c) cv ∧ NUM n nv ∧ 0 < n ∧ n < 256 ** 8 ∧
  sock_read2 c n s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_read_v [cv; nv] (SOCKETS2_EV s evs)
    (POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str r) v *
              SOCKETS2_EV s' (evs ++ [act_event (Read c n) (Got r)]))
Proof
  strip_tac
  \\ ‘sread_out n r = read_bytes n r’ by simp [sread_out_def, read_bytes_def]
  \\ xcf_with_def (fetch "socketProg" "Socket_read_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ xlet ‘POSTv uv. W8ARRAY av (read_bytes n r) *
             SOCKETS2_EV s' (evs ++ [act_event (Read c n) (Got r)])’
  >- (simp [SOCKETS2_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qexistsl [‘fd_bytes c’, ‘emp’, ‘sockets2_encode s’,
                   ‘mk_ffi_next sockets2_ffi_part’, ‘socket2_names’, ‘evs’]
      \\ xsimpl
      \\ drule_all ffi_sock_read2_call \\ strip_tac
      \\ simp [sockets2_ffi_part_def, mk_ffi_next_def, act_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ ‘∀d. r = SOME d ⇒ LENGTH d ≤ n’
    by (rw [] \\ imp_res_tac sock_read2_LENGTH)
  \\ drule LENGTH_read_bytes \\ strip_tac
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av (read_bytes n r) *
                SOCKETS2_EV s' (evs ++ [act_event (Read c n) (Got r)])’,
               ‘implode (MAP (CHR o w2n) (read_bytes n r))’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ simp [decode_read_bytes]
QED

Theorem bytes_str_round_trip[local]:
  MAP (n2w o ORD) (explode (bytes_str bs)) = bs
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF, ORD_CHR_RWT, w2n_lt_256] >>
  Induct_on ‘bs’ >> simp[ORD_CHR_RWT, w2n_lt_256]
QED

Theorem Socket_write2_spec_ev:
  NUM (w2n c) cv ∧ STRING_TYPE (bytes_str bs) sv ∧
  sock_write2 c bs s = SOME s' ⇒
  app (p:'ffi ffi_proj) Socket_write_v [cv; sv] (SOCKETS2_EV s evs)
    (POSTv v. &UNIT_TYPE () v *
              SOCKETS2_EV s' (evs ++ [act_event (Write c bs) Wrote]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "socketProg" "Socket_write_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTv uv. W8ARRAY av [] *
             SOCKETS2_EV s' (evs ++ [act_event (Write c bs) Wrote])’
  >- (simp [SOCKETS2_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, write_conf, bytes_str_round_trip]
      \\ qexistsl [‘fd_bytes c ++ bs’, ‘emp’, ‘sockets2_encode s’,
                   ‘mk_ffi_next sockets2_ffi_part’, ‘socket2_names’, ‘evs’]
      \\ xsimpl
      \\ drule ffi_sock_write2_call \\ strip_tac
      \\ simp [sockets2_ffi_part_def, mk_ffi_next_def, act_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xcon \\ xsimpl
QED

Theorem SocketClose_close_spec_ev:
  NUM (w2n c) cv ∧ sock_close2 c s = SOME s' ⇒
  app (p:'ffi ffi_proj) SocketClose_close_v [cv] (SOCKETS2_EV s evs)
    (POSTv v. &UNIT_TYPE () v * SOCKETS2_EV s' (evs ++ [close_event c]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "lifetimeProg" "SocketClose_close_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTv uv. W8ARRAY av [] * SOCKETS2_EV s' (evs ++ [close_event c])’
  >- (simp [SOCKETS2_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, cl_conf_fd_bytes]
      \\ qexistsl [‘fd_bytes c’, ‘emp’, ‘sockets2_encode s’,
                   ‘mk_ffi_next sockets2_ffi_part’, ‘socket2_names’, ‘evs’]
      \\ xsimpl
      \\ drule ffi_sock_close2_call \\ strip_tac
      \\ simp [sockets2_ffi_part_def, mk_ffi_next_def, close_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xcon \\ xsimpl
QED
