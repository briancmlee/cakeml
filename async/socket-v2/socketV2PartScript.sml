(*
  The version-2 socket world as an FFI part (five names: version 1's four
  and «sock_close»), with the encoding of its state, as in version 1
  (ffiSpikeSocketFFI, ffiSpikeSocketWorld).
*)
Theory socketV2Part
Ancestors
  cfHeapsBase cfFFIType llist alist nlist numpair Marshalling
  ffiSpikeSocketFFI socketV2FFI
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* Encoding the state *)

Definition arrival2_num_def:
  arrival2_num (Connect2 l) = 3 * w2n l ∧
  arrival2_num (Data2 j bs) = 3 * npair j (nlist_of (MAP w2n bs)) + 1 ∧
  arrival2_num (Eof2 j) = 3 * j + 2
End

Definition num_arrival2_def:
  num_arrival2 n =
    let k = n DIV 3 in
    if n MOD 3 = 0 then Connect2 (n2w k)
    else if n MOD 3 = 1 then Data2 (nfst k) (MAP n2w (listOfN (nsnd k)))
    else Eof2 k
End

Theorem num_arrival2_arrival2_num[simp]:
  num_arrival2 (arrival2_num a) = a
Proof
  Cases_on ‘a’
  \\ simp [arrival2_num_def, num_arrival2_def]
  \\ simp [MAP_MAP_o, combinTheory.o_DEF]
  \\ simp [ADD_DIV_RWT, MOD_TIMES, MULT_DIV
           |> ONCE_REWRITE_RULE [MULT_COMM]]
QED

Definition step2_num_def:
  step2_num arrivals = nlist_of (MAP arrival2_num arrivals)
End

Definition num_step2_def:
  num_step2 n = MAP num_arrival2 (listOfN n)
End

Theorem num_step2_step2_num[simp]:
  num_step2 (step2_num as) = as
Proof
  simp [num_step2_def, step2_num_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Definition sockets2_encode_def:
  sockets2_encode s =
    Cons (Cons (Cons (encode_list (encode_pair (Num o w2n) (encode_list Num))
                                  s.listening)
                     (encode_list encode_conn s.clients))
               (Cons (encode_list (encode_pair (Num o w2n) Num) s.open_fds)
                     (encode_list (Num o w2n) s.reserved)))
         (Stream (LMAP step2_num s.future))
End

Theorem encode_words_11[local]:
  encode_list (Num o w2n) (x:'a word list) = encode_list (Num o w2n) y ⇔
  x = y
Proof
  rw [EQ_IMP_THM]
  \\ irule encode_list_11 \\ first_x_assum (irule_at Any) \\ simp []
QED

Theorem encode_nums_11[local]:
  encode_list Num x = encode_list Num y ⇔ x = y
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
  \\ simp [fetch "ffiSpikeSocketFFI" "conn_component_equality"] \\ metis_tac []
QED

Theorem LMAP_id[local]:
  LMAP (λx. x) l = l
Proof
  ONCE_REWRITE_TAC [LNTH_EQ] \\ rw [LNTH_LMAP] \\ Cases_on ‘LNTH n l’ \\ simp []
QED

Theorem LMAP_step2_num_11[local]:
  LMAP step2_num x = LMAP step2_num y ⇔ x = y
Proof
  eq_tac \\ rw []
  \\ pop_assum (mp_tac o AP_TERM “LMAP num_step2”)
  \\ simp [LMAP_MAP, combinTheory.o_DEF, LMAP_id]
QED

Theorem sockets2_encode_11[local]:
  ∀x y. sockets2_encode x = sockets2_encode y ⇔ x = y
Proof
  rw [sockets2_encode_def, fetch "socketV2FFI" "sockets2_component_equality",
      LMAP_step2_num_11, EQ_IMP_THM, encode_words_11]
  \\ irule encode_list_11 \\ first_x_assum (irule_at Any)
  \\ simp [FORALL_PROD, encode_pair_def, encode_words_11, encode_nums_11,
           encode_conn_11]
QED

Theorem sockets2_decode_exists[local]:
  ∃decode. ∀s. decode (sockets2_encode s) = SOME s
Proof
  qexists_tac ‘λf. some s. sockets2_encode s = f’
  \\ simp [sockets2_encode_11]
QED

val sockets2_decode_encode = new_specification (
  "sockets2_decode_encode", ["sockets2_decode"], sockets2_decode_exists);
val _ = export_rewrites ["sockets2_decode_encode"];

(*---------------------------------------------------------------------------*)
(* The part *)

Definition sockets2_ffi_part_def:
  sockets2_ffi_part =
    (sockets2_encode, sockets2_decode,
     [(«sock_poll», ffi_sock_poll2);
      («sock_accept», ffi_sock_accept2);
      («sock_read», ffi_sock_read2);
      («sock_write», ffi_sock_write2);
      («sock_close», ffi_sock_close2)])
End

Definition socket2_names_def:
  socket2_names =
    [«sock_poll»; «sock_accept»; «sock_read»; «sock_write»; «sock_close»]
End

Definition socket2_call_def:
  socket2_call m conf bytes (sk:sockets2) =
    case ALOOKUP (SND (SND sockets2_ffi_part)) m of
    | SOME f => f conf bytes sk
    | NONE => NONE
End

Definition socket2_name_def:
  socket2_name (ExtCall m) = (if MEM m socket2_names then SOME m else NONE) ∧
  socket2_name _ = NONE
End

Theorem MAP_FST_sockets2_ffi_part:
  MAP FST (SND (SND sockets2_ffi_part)) = socket2_names
Proof
  simp [sockets2_ffi_part_def, socket2_names_def]
QED

Theorem ffi_sock2_length:
  (ffi_sock_poll2 conf bytes s = SOME (FFIreturn bytes' s') ⇒
     LENGTH bytes' = LENGTH bytes) ∧
  (ffi_sock_accept2 conf bytes s = SOME (FFIreturn bytes' s') ⇒
     LENGTH bytes' = LENGTH bytes) ∧
  (ffi_sock_read2 conf bytes s = SOME (FFIreturn bytes' s') ⇒
     LENGTH bytes' = LENGTH bytes) ∧
  (ffi_sock_write2 conf bytes s = SOME (FFIreturn bytes' s') ⇒
     LENGTH bytes' = LENGTH bytes) ∧
  (ffi_sock_close2 conf bytes s = SOME (FFIreturn bytes' s') ⇒
     LENGTH bytes' = LENGTH bytes)
Proof
  rw [ffi_sock_poll2_def, ffi_sock_accept2_def, ffi_sock_read2_def,
      ffi_sock_write2_def, ffi_sock_close2_def, AllCaseEqs()]
  \\ gvs [LENGTH_bytes_fds, LENGTH_TL, LENGTH_n2w8]
  \\ gvs [sock_read2_def, AllCaseEqs(), LENGTH_TAKE_EQ]
QED

Theorem ffi_sock2_not_diverge:
  ffi_sock_poll2 conf bytes s ≠ SOME FFIdiverge ∧
  ffi_sock_accept2 conf bytes s ≠ SOME FFIdiverge ∧
  ffi_sock_read2 conf bytes s ≠ SOME FFIdiverge ∧
  ffi_sock_write2 conf bytes s ≠ SOME FFIdiverge ∧
  ffi_sock_close2 conf bytes s ≠ SOME FFIdiverge
Proof
  rw [ffi_sock_poll2_def, ffi_sock_accept2_def, ffi_sock_read2_def,
      ffi_sock_write2_def, ffi_sock_close2_def, AllCaseEqs()]
QED

Theorem mk_proj1_sockets2:
  mk_proj1 sockets2_ffi_part sk = MAP (λn. (n, sockets2_encode sk)) socket2_names
Proof
  simp [mk_proj1_def, sockets2_ffi_part_def, socket2_names_def]
QED

Theorem socket2_part_return:
  mk_ffi_next sockets2_ffi_part m conf bytes (sockets2_encode sk) =
    SOME (FFIreturn new_bytes w) ⇒
  LENGTH new_bytes = LENGTH bytes ∧
  ∃sk'. socket2_call m conf bytes sk = SOME (FFIreturn new_bytes sk') ∧
        w = sockets2_encode sk'
Proof
  strip_tac
  \\ gvs [mk_ffi_next_def, sockets2_ffi_part_def, socket2_call_def,
          AllCaseEqs()]
  \\ metis_tac [ffi_sock2_length]
QED

Theorem socket2_part_not_diverge:
  mk_ffi_next sockets2_ffi_part m conf bytes (sockets2_encode sk) ≠ SOME FFIdiverge
Proof
  rw [mk_ffi_next_def, sockets2_ffi_part_def, AllCaseEqs()]
  \\ rw [] \\ metis_tac [ffi_sock2_not_diverge]
QED
