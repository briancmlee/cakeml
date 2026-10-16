(*
  The prefetching L1 (honestL1PFModel) in CakeML: the pure parts, translated.

  L1's state is the model's own (l1p, with honestL1Model's l1st inside),
  registered with the translator, so the bookkeeping the model does
  between calls (buffers, tables, the poll set, the ready set, decoding
  the C's results) is the model's definitions themselves, translated.  The
  code that makes the L0 calls (honestL0Prog's L0 module) mirrors the
  model's world functions one by one (honestL1PFCode), and its CF specs
  are against them (honestL1PFSpec).

  Appended to honestL0Proof's translation state (the servers' chain, then
  the L0 wrappers).
*)
Theory honestL1PFProg
Ancestors
  ml_translator honestL0 honestL1Model honestL1PFModel honestL0Proof
  ffiSpikeSocketFFI Marshalling
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestL0Proof";

(* ------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------ *)

val _ = register_type “:errcode”;
val _ = register_type “:l0_res”;
val _ = register_type “:revents”;
val _ = register_type “:l1st”;
val _ = register_type “:l1p”;

(* ------------------------------------------------------------------------
   Bytes and strings at the L0 boundary
   ------------------------------------------------------------------------ *)

(* The configuration string of a call, and the bytes of a result *)
Definition bytes_to_str_def:
  bytes_to_str (bs : word8 list) = implode (MAP (CHR o w2n) bs)
End

Definition str_to_bytes_def:
  str_to_bytes s = MAP (n2w o ORD) (explode s) : word8 list
End

Theorem str_to_bytes_bytes_to_str:
  str_to_bytes (bytes_to_str bs) = bs
Proof
  simp[str_to_bytes_def, bytes_to_str_def, MAP_MAP_o, combinTheory.o_DEF,
       ORD_CHR_RWT, w2n_lt_256 |> SIMP_RULE (srw_ss()) [],
       wordsTheory.w2n_lt |> INST_TYPE [alpha |-> “:8”] |> SIMP_RULE (srw_ss()) []] >>
  Induct_on ‘bs’ >> simp[] >> rpt strip_tac >>
  ‘w2n h < 256’ by (assume_tac (INST_TYPE [alpha |-> “:8”] wordsTheory.w2n_lt) >> fs[]) >>
  simp[ORD_CHR_RWT]
QED

(* Membership, translatable (the translator reads MEM as a set) *)
Definition lmem_def:
  lmem x [] = F ∧
  lmem x (y :: ys) = (x = y ∨ lmem x ys)
End

Theorem lmem_MEM:
  ∀l. lmem x l ⇔ MEM x l
Proof
  Induct >> simp[lmem_def]
QED

val r = translate lmem_def;

(* Translate with TAKE / DROP as the basis's mllist take / drop and MEM as
   lmem *)
fun tr th = translate (th |> REWRITE_RULE [GSYM mllistTheory.take_def,
                                          GSYM mllistTheory.drop_def,
                                          GSYM lmem_MEM]);

(* ------------------------------------------------------------------------
   Decoding results (honestL0's dec_res, l0_res_of)
   ------------------------------------------------------------------------ *)

val r = tr err_code_def;
val r = tr code_err_def;
val r = tr w82n_def;
val r = tr n2w8_def;
val r = tr fd_bytes_def;
val r = tr dec_res_def;
val r = tr l0_res_of_def;

(* byte_revents, with word_bit as arithmetic *)
Theorem byte_revents_arith:
  byte_revents b =
    <| rin := ODD (w2n b); rout := ODD (w2n b DIV 2); rerr := ODD (w2n b DIV 4);
       rhup := ODD (w2n b DIV 8); rnval := ODD (w2n b DIV 16) |>
Proof
  simp[byte_revents_def, revents_component_equality] >>
  Cases_on ‘b’ >> fs[wordsTheory.word_bit_n2w, bitTheory.BIT_def, bitTheory.BITS_THM,
                     bitTheory.ODD_MOD2_LEM]
QED

val r = tr byte_revents_arith;
val r = tr poll_revents_def;
val r = tr readable_fds_def;
val r = tr writable_fds_def;
val r = tr poll_conf_def;
val r = tr (poll_chunks_def |> CONV_RULE (DEPTH_CONV ETA_CONV));

(* ------------------------------------------------------------------------
   L1's bookkeeping
   ------------------------------------------------------------------------ *)

val r = tr alistTheory.ADELKEY_def;
val r = tr l1hdln_def;
val r = tr l1hdl_def;
val r = tr outbox_of_def;
val r = tr set_outbox_def;
val r = tr l1_transient_def;
val r = tr forget_def;
val r = tr after_send_def;
val r = tr inb_of_def;
val r = tr set_inb_def;
val r = tr pf_chunk_def;
val r = tr wants_input_def;
val r = tr pf_poll_set_def;
val r = tr in_fds_def;
val r = tr pf_ready_def;
