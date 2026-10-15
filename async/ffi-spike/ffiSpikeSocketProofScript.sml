(*
  The sockets as a separation-logic resource, and the CF specs of the
  Socket module.  Like the basis specs, the specs are generic in the FFI
  world (p:'ffi ffi_proj): they only need the socket part to be present.
  Each spec is stated with the model's operation (sock_poll, sock_accept,
  sock_read, sock_write of ffiSpikeSocketFFI).
*)
Theory ffiSpikeSocketProof
Ancestors
  ml_translator cfHeapsBase cfMain Marshalling Word8ArrayProof mlstring
  ffiSpikeSocketFFI ffiSpikeSocketProg
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "ffiSpikeSocketProg";

(* SOCKETS s: the program owns the socket part, in state s. *)
Definition SOCKETS_def:
  SOCKETS s = IOx sockets_ffi_part s
End

Theorem SOCKETS_FFI_part_hprop:
  FFI_part_hprop (SOCKETS s)
Proof
  rw [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def, FFI_part_hprop_def,
      SEP_CLAUSES, SEP_EXISTS_THM, cond_STAR]
  \\ fs [one_def]
QED

Theorem SOCKETS_precond:
  SOCKETS s {FFI_part (sockets_encode s) (mk_ffi_next sockets_ffi_part)
               [«sock_poll»; «sock_accept»; «sock_read»; «sock_write»] events}
Proof
  rw [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def, SEP_EXISTS_THM,
      cond_STAR, one_def]
QED

(*---------------------------------------------------------------------------*)
(* The marshalling functions invert the FFI's encodings *)

Theorem CHR_o_w2n[local]:
  CHR o w2n = byte_char
Proof
  simp [FUN_EQ_THM, byte_char_def]
QED

Theorem byte_char_11[local]:
  byte_char w1 = byte_char w2 ⇔ w1 = w2
Proof
  simp [byte_char_def, CHR_11, w2n_lt_256]
QED

Theorem byte_char_n2w[local]:
  n < 256 ⇒ byte_char (n2w n) = CHR n
Proof
  simp [byte_char_def]
QED

Theorem fd_conf_fd_bytes:
  fd_conf (w2n fd) = implode (MAP (CHR o w2n) (fd_bytes fd))
Proof
  simp [fd_conf_def, fd_chars_def, fd_bytes_def, CHR_o_w2n]
QED

Theorem fds_conf_fds_bytes:
  ∀fds. fds_conf (MAP w2n fds) = implode (MAP (CHR o w2n) (fds_bytes fds))
Proof
  simp [fds_conf_def, fds_bytes_def, MAP_FLAT, MAP_MAP_o, fd_chars_def,
        fd_bytes_def, CHR_o_w2n, combinTheory.o_DEF]
QED

Theorem chars_num_w82n[local]:
  LENGTH ws = 8 ⇒ chars_num 0 (MAP byte_char ws) = w82n ws
Proof
  rw [LENGTH_EQ_NUM_compute]
  \\ simp [chars_num_def, byte_char_def, w82n_def, ORD_CHR_RWT, w2n_lt_256]
QED

Theorem chars_num_n2w8[local]:
  k < 256 ** 8 ⇒ chars_num 0 (MAP byte_char (n2w8 k)) = k
Proof
  rw [chars_num_w82n, LENGTH_n2w8] \\ irule w82n_n2w8 \\ simp []
QED

Theorem ready_of_flags:
  ∀fds. ready_of (MAP w2n fds)
          (MAP byte_char (MAP (λfd. if P fd then 1w else 0w) fds)) =
        MAP w2n (FILTER P fds)
Proof
  Induct \\ rw [ready_of_def] \\ Cases_on ‘P h’
  \\ gvs [ready_of_def, byte_char_def, CHR_11]
QED

Theorem decode_accept_some:
  decode_accept (implode (MAP (CHR o w2n) (1w :: fd_bytes c))) = SOME (w2n c)
Proof
  simp [decode_accept_def, CHR_o_w2n, byte_char_n2w, CHR_11]
  \\ ‘TAKE 8 (MAP byte_char (fd_bytes c)) = MAP byte_char (fd_bytes c)’
    by simp [TAKE_LENGTH_ID_rwt]
  \\ simp [chars_num_w82n]
QED

Theorem decode_accept_none:
  decode_accept (implode (MAP (CHR o w2n) ((0w:word8) :: rest))) = NONE
Proof
  simp [decode_accept_def, CHR_o_w2n, byte_char_n2w, CHR_11]
QED

Theorem decode_read_data:
  LENGTH d < 256 ** 8 ⇒
  decode_read (implode (MAP (CHR o w2n) (0w :: n2w8 (LENGTH d) ++ d ++ rest))) =
    SOME (implode (MAP byte_char d))
Proof
  strip_tac
  \\ qabbrev_tac ‘hd = MAP byte_char (n2w8 (LENGTH d))’
  \\ ‘LENGTH hd = 8 ∧ chars_num 0 hd = LENGTH d’
    by simp [Abbr ‘hd’, LENGTH_n2w8, chars_num_n2w8]
  \\ simp [decode_read_def, CHR_o_w2n, byte_char_n2w, CHR_11]
  \\ simp [TAKE_APPEND1, DROP_APPEND, TAKE_LENGTH_ID_rwt,
           DROP_LENGTH_TOO_LONG]
  \\ metis_tac [TAKE_LENGTH_APPEND, LENGTH_MAP]
QED

Theorem decode_read_eof:
  decode_read (implode (MAP (CHR o w2n) ((2w:word8) :: rest))) = SOME (strlit "")
Proof
  simp [decode_read_def, CHR_o_w2n, byte_char_n2w, CHR_11]
QED

Theorem decode_read_block:
  decode_read (implode (MAP (CHR o w2n) ((1w:word8) :: rest))) = NONE
Proof
  simp [decode_read_def, CHR_o_w2n, byte_char_n2w, CHR_11]
QED

(*---------------------------------------------------------------------------*)
(* The FFI calls on the buffers the Socket functions build *)

Theorem ffi_sock_poll_call:
  ffi_sock_poll (fds_bytes fds) (REPLICATE (LENGTH fds) 0w) s =
    SOME (FFIreturn (MAP (λfd. if is_ready (tick s) fd then 1w else 0w) fds)
                    (tick s))
Proof
  simp [ffi_sock_poll_def]
QED

(* MAIN: Socket.poll fds lets one step of the schedule arrive and returns
   the ready fds among fds. *)
Theorem Socket_poll_spec:
  LIST_TYPE NUM (MAP w2n fds) fdsv ⇒
  app (p:'ffi ffi_proj) Socket_poll_v [fdsv]
    (SOCKETS s)
    (POSTv v. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds s))) v *
              SOCKETS (SND (sock_poll fds s)))
Proof
  strip_tac
  \\ xcf_with_def Socket_poll_v_def
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ xlet ‘POSTv uv. W8ARRAY av
             (MAP (λfd. if is_ready (tick s) fd then 1w else 0w) fds) *
           SOCKETS (tick s)’
  >- (qpat_abbrev_tac ‘Q = $POSTv _’
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xpull \\ qunabbrev_tac ‘Q’
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fds_conf_fds_bytes]
      \\ qmatch_goalsub_abbrev_tac ‘FFI_part s0 u ns events’
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘s0’, ‘u’, ‘ns’, ‘events’]
      \\ xsimpl
      \\ simp [Abbr ‘s0’, Abbr ‘u’, Abbr ‘ns’, mk_ffi_next_def,
               ffi_sock_poll_call]
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xsimpl
      \\ qmatch_goalsub_abbrev_tac ‘events ++ new_events’
      \\ qexists_tac ‘events ++ new_events’ \\ xsimpl)
  \\ qmatch_goalsub_abbrev_tac ‘W8ARRAY av flagbytes’
  \\ ‘LENGTH flagbytes = LENGTH fds’ by simp [Abbr ‘flagbytes’]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av flagbytes * SOCKETS (tick s)’,
               ‘MAP (CHR o w2n) (TAKE (LENGTH fds) flagbytes)’,
               ‘MAP w2n fds’]
  \\ gvs [Abbr ‘flagbytes’] \\ xsimpl
  \\ simp [CHR_o_w2n, TAKE_LENGTH_ID_rwt]
  \\ rpt strip_tac \\ fs [ready_of_flags, sock_poll_def]
  >- (‘(λfd. is_ready (tick s) fd) = is_ready (tick s)’ by simp [FUN_EQ_THM]
      \\ fs [])
  \\ xsimpl
QED

Theorem ffi_sock_accept_call:
  sock_accept l s = SOME (r, s') ⇒
  ffi_sock_accept (fd_bytes l) (REPLICATE 9 0w) s =
    SOME (FFIreturn (case r of
                     | NONE => 0w :: REPLICATE 8 0w
                     | SOME c => 1w :: fd_bytes c) s')
Proof
  rw [ffi_sock_accept_def] \\ Cases_on ‘r’ \\ gvs [] \\ EVAL_TAC
QED

(* MAIN: Socket.accept l returns the oldest pending connection of the
   listener l and removes it from the queue, or NONE if there is none. *)
Theorem Socket_accept_spec:
  NUM (w2n l) lv ∧ sock_accept l s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_accept_v [lv]
    (SOCKETS s)
    (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n r) v * SOCKETS s')
Proof
  strip_tac
  \\ xcf_with_def Socket_accept_v_def
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ qabbrev_tac ‘resbytes = case r of
                             | NONE => 0w :: REPLICATE 8 0w
                             | SOME c => 1w :: fd_bytes c’
  \\ xlet ‘POSTv uv. W8ARRAY av resbytes * SOCKETS s'’
  >- (qpat_abbrev_tac ‘Q = $POSTv _’
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xpull \\ qunabbrev_tac ‘Q’
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qmatch_goalsub_abbrev_tac ‘FFI_part s0 u ns events’
      \\ qexistsl [‘fd_bytes l’, ‘emp’, ‘s0’, ‘u’, ‘ns’, ‘events’]
      \\ xsimpl
      \\ simp [Abbr ‘s0’, Abbr ‘u’, Abbr ‘ns’, mk_ffi_next_def]
      \\ drule ffi_sock_accept_call \\ simp [] \\ strip_tac
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xsimpl
      \\ qmatch_goalsub_abbrev_tac ‘events ++ new_events’
      \\ qexists_tac ‘events ++ new_events’ \\ xsimpl)
  \\ ‘LENGTH resbytes = 9’ by (Cases_on ‘r’ \\ simp [Abbr ‘resbytes’])
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av resbytes * SOCKETS s'’,
               ‘implode (MAP (CHR o w2n) resbytes)’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ qunabbrev_tac ‘resbytes’ \\ Cases_on ‘r’
  \\ full_simp_tac std_ss [option_case_def, decode_accept_none,
                          decode_accept_some, OPTION_MAP_DEF]
QED

(* The bytes «sock_read» returns in a buffer of n data bytes. *)
Definition read_bytes_def:
  read_bytes n r =
    case r of
    | NONE => 1w :: REPLICATE (n + 8) 0w
    | SOME d =>
        if d = [] then 2w :: REPLICATE (n + 8) 0w
        else 0w :: n2w8 (LENGTH d) ++ d ++ REPLICATE (n − LENGTH d) 0w
End

Theorem TL_REPLICATE_9[local]:
  TL (REPLICATE (n + 9) x) = REPLICATE (n + 8) x
Proof
  ‘n + 9 = SUC (n + 8)’ by simp [] \\ pop_assum SUBST1_TAC \\ simp [REPLICATE]
QED

Theorem ffi_sock_read_call:
  sock_read c n s = SOME (r, s') ∧ 0 < n ⇒
  ffi_sock_read (fd_bytes c) (REPLICATE (n + 9) 0w) s =
    SOME (FFIreturn (read_bytes n r) s')
Proof
  rw [ffi_sock_read_def, read_bytes_def, TL_REPLICATE_9]
  \\ every_case_tac \\ gvs []
  \\ imp_res_tac sock_read_LENGTH \\ simp []
QED

Theorem LENGTH_read_bytes:
  (∀d. r = SOME d ⇒ LENGTH d ≤ n) ⇒ LENGTH (read_bytes n r) = n + 9
Proof
  rw [read_bytes_def] \\ every_case_tac \\ gvs [LENGTH_n2w8]
QED

Theorem decode_read_bytes:
  (∀d. r = SOME d ⇒ LENGTH d ≤ n) ∧ n < 256 ** 8 ⇒
  decode_read (implode (MAP (CHR o w2n) (read_bytes n r))) =
    OPTION_MAP (λd. implode (MAP (CHR o w2n) d)) r
Proof
  strip_tac \\ Cases_on ‘r’
  >- simp_tac std_ss [read_bytes_def, option_case_def, decode_read_block,
                      OPTION_MAP_DEF]
  \\ rename1 ‘SOME d’ \\ Cases_on ‘d = []’
  >- (asm_simp_tac std_ss [read_bytes_def, option_case_def, decode_read_eof,
                           OPTION_MAP_DEF]
      \\ EVAL_TAC)
  \\ ‘LENGTH d < 256 ** 8’ by (res_tac \\ fs [])
  \\ asm_simp_tac std_ss [read_bytes_def, option_case_def, decode_read_data,
                          OPTION_MAP_DEF]
  \\ simp [CHR_o_w2n]
QED

(* MAIN: Socket.read c n reads at most n bytes from connection c: SOME data
   (non-empty), SOME "" at EOF, or NONE if nothing is there yet. *)
Theorem Socket_read_spec:
  NUM (w2n c) cv ∧ NUM n nv ∧ 0 < n ∧ n < 256 ** 8 ∧
  sock_read c n s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_read_v [cv; nv]
    (SOCKETS s)
    (POSTv v. &OPTION_TYPE STRING_TYPE
                 (OPTION_MAP (λd. implode (MAP (CHR o w2n) d)) r) v *
              SOCKETS s')
Proof
  strip_tac
  \\ xcf_with_def Socket_read_v_def
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ xlet ‘POSTv uv. W8ARRAY av (read_bytes n r) * SOCKETS s'’
  >- (qpat_abbrev_tac ‘Q = $POSTv _’
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xpull \\ qunabbrev_tac ‘Q’
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qmatch_goalsub_abbrev_tac ‘FFI_part s0 u ns events’
      \\ qexistsl [‘fd_bytes c’, ‘emp’, ‘s0’, ‘u’, ‘ns’, ‘events’]
      \\ xsimpl
      \\ simp [Abbr ‘s0’, Abbr ‘u’, Abbr ‘ns’, mk_ffi_next_def]
      \\ drule_all ffi_sock_read_call \\ simp [] \\ strip_tac
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xsimpl
      \\ qmatch_goalsub_abbrev_tac ‘events ++ new_events’
      \\ qexists_tac ‘events ++ new_events’ \\ xsimpl)
  \\ ‘∀d. r = SOME d ⇒ LENGTH d ≤ n’
    by (rw [] \\ imp_res_tac sock_read_LENGTH)
  \\ drule LENGTH_read_bytes \\ strip_tac
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av (read_bytes n r) * SOCKETS s'’,
               ‘implode (MAP (CHR o w2n) (read_bytes n r))’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ simp [decode_read_bytes]
QED

Theorem write_conf:
  strcat (fd_conf (w2n c)) str =
    implode (MAP (CHR o w2n) (fd_bytes c ++ MAP (n2w o ORD) (explode str)))
Proof
  simp [strcat_thm, fd_conf_fd_bytes, MAP_MAP_o, combinTheory.o_DEF]
  \\ qspec_tac (‘explode str’, ‘cs’)
  \\ Induct \\ simp [ORD_BOUND, LESS_MOD, CHR_ORD]
QED

Theorem ffi_sock_write_call:
  sock_write c bs s = SOME s' ⇒
  ffi_sock_write (fd_bytes c ++ bs) [] s = SOME (FFIreturn [] s')
Proof
  rw [ffi_sock_write_def, TAKE_APPEND1, DROP_APPEND, TAKE_LENGTH_ID_rwt,
      DROP_LENGTH_TOO_LONG]
QED

(* MAIN: Socket.write c str appends the bytes of str to the outgoing log
   of connection c. *)
Theorem Socket_write_spec:
  NUM (w2n c) cv ∧ STRING_TYPE str sv ∧
  sock_write c (MAP (n2w o ORD) (explode str)) s = SOME s' ⇒
  app (p:'ffi ffi_proj) Socket_write_v [cv; sv]
    (SOCKETS s)
    (POSTv v. &UNIT_TYPE () v * SOCKETS s')
Proof
  strip_tac
  \\ xcf_with_def Socket_write_v_def
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTv uv. W8ARRAY av [] * SOCKETS s'’
  >- (qpat_abbrev_tac ‘Q = $POSTv _’
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xpull \\ qunabbrev_tac ‘Q’
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, write_conf]
      \\ qmatch_goalsub_abbrev_tac ‘FFI_part s0 u ns events’
      \\ qexistsl [‘fd_bytes c ++ MAP (n2w o ORD) (explode str)’, ‘emp’, ‘s0’,
                   ‘u’, ‘ns’, ‘events’]
      \\ xsimpl
      \\ simp [Abbr ‘s0’, Abbr ‘u’, Abbr ‘ns’, mk_ffi_next_def]
      \\ drule ffi_sock_write_call \\ simp [] \\ strip_tac
      \\ simp [SOCKETS_def, IOx_def, IO_def, sockets_ffi_part_def]
      \\ xsimpl
      \\ qmatch_goalsub_abbrev_tac ‘events ++ new_events’
      \\ qexists_tac ‘events ++ new_events’ \\ xsimpl)
  \\ xcon \\ xsimpl
QED
