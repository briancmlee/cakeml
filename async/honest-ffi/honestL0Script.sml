(*
  L0, the minimal honest socket FFI (design/36 §3): statement-level draft.

  Every L0 call returns a 13-byte header first:
     out[0]      code  : 0 OK, else an error code (errcode below)
     out[1..8]   value : 8 bytes, big-endian (an fd, a count)
     out[9..12]  errno : the raw errno, opaque to the model
  The C's errno table is TOTAL: an errno it does not list is E_OTHER with
  the raw value; nothing is folded into success, EOF or would-block.

  This theory fixes the encoding and proves it decodable.  The world
  model of the calls (design/36 §4) is a proposal for the endpoint world
  and is not drafted here.
*)
Theory honestL0
Ancestors
  words list mlstring Marshalling
Libs
  preamble

Datatype:
  errcode = E_AGAIN | E_INTR | E_INPROGRESS | E_CONNREFUSED | E_CONNRESET
          | E_PIPE | E_CONNABORTED | E_TIMEDOUT | E_NOTCONN | E_MFILE
          | E_NFILE | E_NOBUFS | E_NOMEM | E_ADDRINUSE | E_ACCES | E_BADF
          | E_NOTSOCK | E_INVAL | E_NETUNREACH | E_HOSTUNREACH | E_NETDOWN
          | E_PROTO | E_OTHER
End

(* The code byte of each error; 0 is reserved for success *)
Definition err_code_def:
  err_code E_AGAIN = 1n ∧ err_code E_INTR = 2 ∧ err_code E_INPROGRESS = 3 ∧
  err_code E_CONNREFUSED = 4 ∧ err_code E_CONNRESET = 5 ∧
  err_code E_PIPE = 6 ∧ err_code E_CONNABORTED = 7 ∧
  err_code E_TIMEDOUT = 8 ∧ err_code E_NOTCONN = 9 ∧ err_code E_MFILE = 10 ∧
  err_code E_NFILE = 11 ∧ err_code E_NOBUFS = 12 ∧ err_code E_NOMEM = 13 ∧
  err_code E_ADDRINUSE = 14 ∧ err_code E_ACCES = 15 ∧ err_code E_BADF = 16 ∧
  err_code E_NOTSOCK = 17 ∧ err_code E_INVAL = 18 ∧
  err_code E_NETUNREACH = 19 ∧ err_code E_HOSTUNREACH = 20 ∧
  err_code E_NETDOWN = 21 ∧ err_code E_PROTO = 22 ∧ err_code E_OTHER = 255
End

Definition code_err_def:
  code_err (n:num) =
    FIND (λe. err_code e = n)
      [E_AGAIN; E_INTR; E_INPROGRESS; E_CONNREFUSED; E_CONNRESET; E_PIPE;
       E_CONNABORTED; E_TIMEDOUT; E_NOTCONN; E_MFILE; E_NFILE; E_NOBUFS;
       E_NOMEM; E_ADDRINUSE; E_ACCES; E_BADF; E_NOTSOCK; E_INVAL;
       E_NETUNREACH; E_HOSTUNREACH; E_NETDOWN; E_PROTO; E_OTHER]
End

Theorem err_code_range:
  0 < err_code e ∧ err_code e < 256
Proof
  Cases_on ‘e’ >> simp[err_code_def]
QED

Theorem code_err_err_code[simp]:
  code_err (err_code e) = SOME e
Proof
  Cases_on ‘e’ >> EVAL_TAC
QED

(* An L0 result: success with a value, or an error with the raw errno *)
Datatype:
  l0_res = Ok num | Fail errcode (word8 list)
End

Definition l0_res_ok_def:
  l0_res_ok (Ok v) = (v < 256 ** 8) ∧
  l0_res_ok (Fail e raw) = (LENGTH raw = 4)
End

Definition enc_res_def:
  enc_res (Ok v) = 0w :: n2w8 v ++ [0w; 0w; 0w; 0w] ∧
  enc_res (Fail e raw) = n2w (err_code e) :: n2w8 0 ++ raw
End

Definition dec_res_def:
  dec_res (out : word8 list) =
    if LENGTH out < 13 then NONE
    else if HD out = 0w then SOME (Ok (w82n (TAKE 8 (TL out))))
    else OPTION_MAP (λe. Fail e (TAKE 4 (DROP 9 out))) (code_err (w2n (HD out)))
End

Theorem LENGTH_enc_res:
  l0_res_ok r ⇒ LENGTH (enc_res r) = 13
Proof
  Cases_on ‘r’ >> rw[l0_res_ok_def, enc_res_def, LENGTH_n2w8]
QED

(* The header is decodable: the C's encoding loses nothing the model
   distinguishes *)
Theorem dec_enc_res:
  l0_res_ok r ⇒ dec_res (enc_res r ++ rest) = SOME r
Proof
  Cases_on ‘r’ >> rw[l0_res_ok_def, enc_res_def, dec_res_def, LENGTH_n2w8]
  >- (‘TAKE 8 (n2w8 n ++ [0w; 0w; 0w; 0w] ++ rest) = n2w8 n’
        by (simp[TAKE_APPEND, LENGTH_n2w8]
            >> ‘TAKE 8 (n2w8 n) = n2w8 n’ by metis_tac[TAKE_LENGTH_ID, LENGTH_n2w8]
            >> simp[])
      >> simp[] >> irule w82n_n2w8 >> fs[])
  >- (qspec_then ‘e’ strip_assume_tac (GEN_ALL err_code_range)
      >> fs[LESS_MOD])
  >> qspec_then ‘e’ strip_assume_tac (GEN_ALL err_code_range)
  >> simp[LESS_MOD, n2w8_def]
  >> ‘TAKE 4 (l ++ rest) = l’ by simp[TAKE_APPEND, TAKE_LENGTH_ID]
  >> fs[]
QED

(* poll's per-fd revents byte: bit0 IN, bit1 OUT, bit2 ERR, bit3 HUP,
   bit4 NVAL; passed through from poll(2) *)
Datatype:
  revents = <| rin : bool; rout : bool; rerr : bool; rhup : bool; rnval : bool |>
End

Definition revents_byte_def:
  revents_byte r : word8 =
    n2w ((if r.rin then 1 else 0) + (if r.rout then 2 else 0) +
         (if r.rerr then 4 else 0) + (if r.rhup then 8 else 0) +
         (if r.rnval then 16 else 0))
End

Definition byte_revents_def:
  byte_revents (b : word8) =
    <| rin := word_bit 0 b; rout := word_bit 1 b; rerr := word_bit 2 b;
       rhup := word_bit 3 b; rnval := word_bit 4 b |>
End

Theorem byte_revents_revents_byte[simp]:
  byte_revents (revents_byte r) = r
Proof
  simp[revents_byte_def, byte_revents_def, theorem "revents_component_equality"]
  >> rw[] >> EVAL_TAC
QED

(* The calls of L0, by name.  sys_connect and sys_connerr come later. *)
Definition l0_calls_def:
  l0_calls = [«sys_listen»; «sys_poll»; «sys_accept»; «sys_recv»;
              «sys_send»; «sys_shutdown»; «sys_close»]
End

(* What L1 sees of each call's result (decoded) *)
Datatype:
  acc_res = AccFd word64 | AccErr errcode     (* E_AGAIN: queue empty *)
End

Datatype:
  recv_res = RecvData (word8 list) | RecvEof | RecvErr errcode
End

Datatype:
  send_res = SendCount num | SendErr errcode
End
