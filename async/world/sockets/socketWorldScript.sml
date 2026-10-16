(*
  Logical model of network sockets, as a new FFI part.

  A world of sockets has
  - listening fds, each with a queue of pending connections;
  - connection fds, each an abstract byte stream: the bytes that have
    arrived but not yet been read, whether the peer has closed its side
    (EOF after the arrived bytes), and the log of everything written;
  - a schedule: the unpredictable future, as a lazy list of steps, each
    step a list of arrivals (a new connection, data, or EOF).  It plays
    the role of fsFFI's numchars or the clock's schedule of readings.

  Time is the schedule: each readiness check («sock_poll») first delivers
  the next step of arrivals, then reports which of the given fds are
  ready.  The other calls do not advance the schedule.  Reads are honest
  (data, would-block or EOF); writes always succeed in full.  Out of
  scope: errors beyond EOF, partial writes, closing.

  fds are 64-bit words, so they always fit the 8-byte encoding.
*)
Theory socketWorld
Ancestors
  cfHeapsBase cfFFIType llist alist nlist numpair Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The model *)

Datatype:
  arrival = Connect word64 word64      (* Connect l c: connection c is
                                          pending on listener l *)
          | Data word64 (word8 list)   (* bytes arrive on connection c *)
          | Eof word64                 (* the peer of c closes its side *)
End

Datatype:
  conn = <| incoming : word8 list      (* arrived, not yet read *)
          ; peer_closed : bool         (* EOF after the incoming bytes *)
          ; outgoing : word8 list      (* everything written so far *)
          |>
End

Datatype:
  sockets = <| listeners : (word64 # word64 list) list
                                       (* listener, its pending connections *)
             ; conns : (word64 # conn) list
             ; sched : arrival list llist
             |>
End

Definition empty_conn_def:
  empty_conn = <| incoming := []; peer_closed := F; outgoing := [] |>
End

Definition is_listener_def:
  is_listener s fd ⇔ ALOOKUP s.listeners fd ≠ NONE
End

Definition is_conn_def:
  is_conn s fd ⇔ ALOOKUP s.conns fd ≠ NONE
End

(* One arrival.  An arrival that makes no sense in the current state (a
   connection on a non-listener or reusing an fd; data or EOF on an
   unknown fd, data after EOF) is dropped; the assumption sched_wf
   (socketFair) excludes schedules containing such arrivals. *)
Definition deliver1_def:
  deliver1 s (Connect l c) =
    (if is_listener s l ∧ ¬is_listener s c ∧ ¬is_conn s c then
       s with <| listeners := AFUPDKEY l (λq. q ++ [c]) s.listeners
               ; conns := (c, empty_conn) :: s.conns |>
     else s) ∧
  deliver1 s (Data c bs) =
    s with conns :=
      AFUPDKEY c (λcn. if cn.peer_closed then cn
                       else cn with incoming := cn.incoming ++ bs) s.conns ∧
  deliver1 s (Eof c) =
    s with conns := AFUPDKEY c (λcn. cn with peer_closed := T) s.conns
End

Definition deliver_def:
  deliver s arrivals = FOLDL deliver1 s arrivals
End

(* Time passes: the next step of the schedule arrives.  After the end of
   a finite schedule nothing more arrives. *)
Definition tick_def:
  tick s =
    case LHD s.sched of
    | NONE => s
    | SOME arrivals => deliver (s with sched := THE (LTL s.sched)) arrivals
End

(* An fd is ready: a listener with a pending connection, or a connection
   with unread data or EOF.  Unknown fds are never ready. *)
Definition is_ready_def:
  is_ready s fd ⇔
    (case ALOOKUP s.listeners fd of SOME q => q ≠ [] | NONE => F) ∨
    (case ALOOKUP s.conns fd of
     | SOME cn => cn.incoming ≠ [] ∨ cn.peer_closed
     | NONE => F)
End

(* The four operations, on the model's own types.  NONE: misuse (an fd
   of the wrong kind), on which the FFI call fails. *)

(* poll: one round of time, then the ready fds among the given ones. *)
Definition sock_poll_def:
  sock_poll fds s = (FILTER (is_ready (tick s)) fds, tick s)
End

(* accept: SOME c, the oldest pending connection, or NONE (would block). *)
Definition sock_accept_def:
  sock_accept l s =
    case ALOOKUP s.listeners l of
    | NONE => NONE
    | SOME [] => SOME (NONE, s)
    | SOME (c::q) =>
        SOME (SOME c, s with listeners := AFUPDKEY l (K q) s.listeners)
End

(* read of at most n bytes: SOME data (non-empty), SOME [] (EOF), or
   NONE (would block). *)
Definition sock_read_def:
  sock_read c n s =
    case ALOOKUP s.conns c of
    | NONE => NONE
    | SOME cn =>
        if cn.incoming ≠ [] then
          SOME (SOME (TAKE n cn.incoming),
                s with conns :=
                  AFUPDKEY c (λcn. cn with incoming := DROP n cn.incoming)
                    s.conns)
        else if cn.peer_closed then SOME (SOME [], s)
        else SOME (NONE, s)
End

(* write: all bytes are appended to the connection's outgoing log. *)
Definition sock_write_def:
  sock_write c bs s =
    case ALOOKUP s.conns c of
    | NONE => NONE
    | SOME _ =>
        SOME (s with conns :=
                AFUPDKEY c (λcn. cn with outgoing := cn.outgoing ++ bs) s.conns)
End

(*---------------------------------------------------------------------------*)
(* Byte encodings *)

(* An fd is 8 bytes, big-endian. *)
Definition fd_bytes_def:
  fd_bytes (fd:word64) = n2w8 (w2n fd)
End

Definition bytes_fd_def:
  bytes_fd bs : word64 = n2w (w82n bs)
End

Theorem w82n_fd_bytes[simp]:
  w82n (fd_bytes fd) = w2n fd
Proof
  rw [fd_bytes_def]
  \\ ‘w2n fd ≤ 256 ** 8 − 1’
    by (qspec_then ‘fd’ assume_tac w2n_lt \\ fs [dimword_def])
  \\ simp [w82n_n2w8]
QED

Theorem bytes_fd_fd_bytes[simp]:
  bytes_fd (fd_bytes fd) = fd
Proof
  rw [bytes_fd_def]
QED

Theorem LENGTH_fd_bytes[simp]:
  LENGTH (fd_bytes fd) = 8
Proof
  simp [fd_bytes_def, LENGTH_n2w8]
QED

(* A list of fds is the concatenation of their encodings. *)
Definition fds_bytes_def:
  fds_bytes fds = FLAT (MAP fd_bytes fds)
End

Definition bytes_fds_def:
  bytes_fds (bs:word8 list) =
    if LENGTH bs < 8 then [] else bytes_fd (TAKE 8 bs) :: bytes_fds (DROP 8 bs)
Termination
  WF_REL_TAC ‘measure LENGTH’ \\ rw [LENGTH_DROP]
End

Theorem bytes_fds_fds_bytes[simp]:
  ∀fds. bytes_fds (fds_bytes fds) = fds
Proof
  Induct \\ simp [fds_bytes_def] \\ rw [] \\ simp [Once bytes_fds_def]
  \\ ‘LENGTH (fd_bytes h) = 8’ by simp []
  \\ ‘TAKE 8 (fd_bytes h ++ FLAT (MAP fd_bytes fds)) = fd_bytes h ∧
      DROP 8 (fd_bytes h ++ FLAT (MAP fd_bytes fds)) = FLAT (MAP fd_bytes fds)’
    by (qpat_x_assum ‘LENGTH _ = 8’ (SUBST1_TAC o SYM)
        \\ simp [TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND])
  \\ fs [fds_bytes_def]
QED

Theorem LENGTH_fds_bytes[simp]:
  ∀fds. LENGTH (fds_bytes fds) = 8 * LENGTH fds
Proof
  Induct \\ gvs [fds_bytes_def, MULT_CLAUSES]
QED

Theorem LENGTH_bytes_fds:
  ∀bs k. LENGTH bs = 8 * k ⇒ LENGTH (bytes_fds bs) = k
Proof
  ho_match_mp_tac bytes_fds_ind \\ rw []
  \\ simp [Once bytes_fds_def] \\ rw []
  \\ Cases_on ‘k’ \\ gvs [MULT_CLAUSES]
QED

(*---------------------------------------------------------------------------*)
(* The FFI functions *)

(* «sock_poll»: conf is a list of fds; one flag byte per fd is returned
   (1 ready, 0 not). *)
Definition ffi_sock_poll_def:
  ffi_sock_poll (conf:word8 list) (bytes:word8 list) s =
    if LENGTH conf = 8 * LENGTH bytes then
      SOME (FFIreturn (MAP (λfd. if is_ready (tick s) fd then 1w else 0w)
                           (bytes_fds conf)) (tick s))
    else NONE
End

(* «sock_accept»: conf is the listener; bytes are 9: a status byte (1: a
   connection, 0: would block) and the new fd. *)
Definition ffi_sock_accept_def:
  ffi_sock_accept (conf:word8 list) (bytes:word8 list) s =
    if LENGTH conf = 8 ∧ LENGTH bytes = 9 then
      case sock_accept (bytes_fd conf) s of
      | NONE => NONE
      | SOME (NONE, s') => SOME (FFIreturn (0w :: TL bytes) s')
      | SOME (SOME c, s') => SOME (FFIreturn (1w :: fd_bytes c) s')
    else NONE
End

(* «sock_read»: conf is the connection; bytes are a status byte (0: data,
   1: would block, 2: EOF), an 8-byte count and a non-empty data area. *)
Definition ffi_sock_read_def:
  ffi_sock_read (conf:word8 list) (bytes:word8 list) s =
    if LENGTH conf = 8 ∧ 9 < LENGTH bytes then
      case sock_read (bytes_fd conf) (LENGTH bytes - 9) s of
      | NONE => NONE
      | SOME (NONE, s') => SOME (FFIreturn (1w :: TL bytes) s')
      | SOME (SOME d, s') =>
          if d = [] then SOME (FFIreturn (2w :: TL bytes) s')
          else SOME (FFIreturn (0w :: n2w8 (LENGTH d) ++ d ++
                                DROP (9 + LENGTH d) bytes) s')
    else NONE
End

(* «sock_write»: conf is the connection followed by the data; bytes are
   not used. *)
Definition ffi_sock_write_def:
  ffi_sock_write (conf:word8 list) (bytes:word8 list) s =
    if 8 ≤ LENGTH conf then
      case sock_write (bytes_fd (TAKE 8 conf)) (DROP 8 conf) s of
      | NONE => NONE
      | SOME s' => SOME (FFIreturn bytes s')
    else NONE
End

Theorem sock_read_LENGTH:
  sock_read c n s = SOME (SOME d, s') ⇒ LENGTH d ≤ n
Proof
  rw [sock_read_def, AllCaseEqs()] \\ simp [LENGTH_TAKE_EQ]
QED

(* Like every FFI function, these return a buffer of the size they got. *)
Theorem ffi_sock_length:
  (ffi_sock_poll conf bytes s = SOME (FFIreturn bytes' s') ∨
   ffi_sock_accept conf bytes s = SOME (FFIreturn bytes' s') ∨
   ffi_sock_read conf bytes s = SOME (FFIreturn bytes' s') ∨
   ffi_sock_write conf bytes s = SOME (FFIreturn bytes' s')) ⇒
  LENGTH bytes' = LENGTH bytes
Proof
  rw [ffi_sock_poll_def, ffi_sock_accept_def, ffi_sock_read_def,
      ffi_sock_write_def, AllCaseEqs()]
  \\ gvs [LENGTH_bytes_fds, LENGTH_TL, LENGTH_n2w8]
  \\ imp_res_tac sock_read_LENGTH \\ simp []
QED

Theorem ffi_sock_not_diverge:
  ffi_sock_poll conf bytes s ≠ SOME FFIdiverge ∧
  ffi_sock_accept conf bytes s ≠ SOME FFIdiverge ∧
  ffi_sock_read conf bytes s ≠ SOME FFIdiverge ∧
  ffi_sock_write conf bytes s ≠ SOME FFIdiverge
Proof
  rw [ffi_sock_poll_def, ffi_sock_accept_def, ffi_sock_read_def,
      ffi_sock_write_def, AllCaseEqs()]
QED

(*---------------------------------------------------------------------------*)
(* Packaging the model as an FFI part *)

(* The schedule is encoded as a stream of numbers, one per step. *)
Definition arrival_num_def:
  arrival_num (Connect l c) = 3 * npair (w2n l) (w2n c) ∧
  arrival_num (Data c bs) = 3 * npair (w2n c) (nlist_of (MAP w2n bs)) + 1 ∧
  arrival_num (Eof c) = 3 * w2n c + 2
End

Definition num_arrival_def:
  num_arrival n =
    let k = n DIV 3 in
    if n MOD 3 = 0 then Connect (n2w (nfst k)) (n2w (nsnd k))
    else if n MOD 3 = 1 then Data (n2w (nfst k)) (MAP n2w (listOfN (nsnd k)))
    else Eof (n2w k)
End

Theorem num_arrival_arrival_num[simp]:
  num_arrival (arrival_num a) = a
Proof
  Cases_on ‘a’
  \\ simp [arrival_num_def, num_arrival_def]
  \\ simp [MAP_MAP_o, combinTheory.o_DEF]
  \\ simp [ADD_DIV_RWT, MOD_TIMES, MULT_DIV
           |> ONCE_REWRITE_RULE [MULT_COMM]]
QED

Definition step_num_def:
  step_num arrivals = nlist_of (MAP arrival_num arrivals)
End

Definition num_step_def:
  num_step n = MAP num_arrival (listOfN n)
End

Theorem num_step_step_num[simp]:
  num_step (step_num as) = as
Proof
  simp [num_step_def, step_num_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Definition encode_bytes_def:
  encode_bytes (bs:word8 list) = encode_list (Num o w2n) bs
End

Definition encode_conn_def:
  encode_conn cn =
    Cons (Cons (encode_bytes cn.incoming) (encode_bool cn.peer_closed))
         (encode_bytes cn.outgoing)
End

Definition sockets_encode_def:
  sockets_encode s =
    Cons (Cons (encode_list (encode_pair (Num o w2n)
                                         (encode_list (Num o w2n)))
                            s.listeners)
               (encode_list (encode_pair (Num o w2n) encode_conn) s.conns))
         (Stream (LMAP step_num s.sched))
End

Theorem encode_words_11[local]:
  encode_list (Num o w2n) (x:'a word list) = encode_list (Num o w2n) y ⇔
  x = y
Proof
  rw [EQ_IMP_THM]
  \\ irule encode_list_11 \\ first_x_assum (irule_at Any) \\ simp []
QED

Theorem encode_bytes_11[local]:
  encode_bytes x = encode_bytes y ⇔ x = y
Proof
  rw [encode_bytes_def, encode_words_11]
QED

Theorem encode_conn_11[local]:
  encode_conn x = encode_conn y ⇔ x = y
Proof
  rw [encode_conn_def, encode_bytes_11, encode_bool_11, EQ_IMP_THM]
  \\ simp [theorem "conn_component_equality"] \\ metis_tac []
QED

Theorem LMAP_id[local]:
  LMAP (λx. x) l = l
Proof
  ONCE_REWRITE_TAC [LNTH_EQ] \\ rw [LNTH_LMAP] \\ Cases_on ‘LNTH n l’ \\ simp []
QED

Theorem LMAP_step_num_11[local]:
  LMAP step_num x = LMAP step_num y ⇔ x = y
Proof
  eq_tac \\ rw []
  \\ pop_assum (mp_tac o AP_TERM “LMAP num_step”)
  \\ simp [LMAP_MAP, combinTheory.o_DEF, LMAP_id]
QED

Theorem sockets_encode_11[local]:
  ∀x y. sockets_encode x = sockets_encode y ⇔ x = y
Proof
  rw [sockets_encode_def, theorem "sockets_component_equality", LMAP_step_num_11,
      EQ_IMP_THM]
  \\ irule encode_list_11 \\ first_x_assum (irule_at Any)
  \\ simp [FORALL_PROD, encode_pair_def]
  \\ simp [encode_words_11, encode_conn_11]
QED

Theorem sockets_decode_exists[local]:
  ∃decode. ∀s. decode (sockets_encode s) = SOME s
Proof
  qexists_tac ‘λf. some s. sockets_encode s = f’
  \\ simp [sockets_encode_11]
QED

val sockets_decode_encode = new_specification (
  "sockets_decode_encode", ["sockets_decode"], sockets_decode_exists);
val _ = export_rewrites ["sockets_decode_encode"];

(* The socket part: four FFI names. *)
Definition sockets_ffi_part_def:
  sockets_ffi_part =
    (sockets_encode, sockets_decode,
     [(«sock_poll», ffi_sock_poll);
      («sock_accept», ffi_sock_accept);
      («sock_read», ffi_sock_read);
      («sock_write», ffi_sock_write)])
End
