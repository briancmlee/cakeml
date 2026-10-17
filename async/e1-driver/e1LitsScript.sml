(*
  Literal byte data in a program: a list of byte strings (word8 list list)
  encoded as one string literal (lits_enc), and its decoder (lits_dec),
  which a program translates and calls on the literal at startup.

  Each byte string is its length (vnum: base 128, low digit first, the
  top bit set on every byte but the last) followed by its bytes.
  lits_dec_enc: decoding an encoding gives the list back, with no bound on
  the lengths.
*)
Theory e1Lits
Ancestors
  words mllist
Libs
  preamble

Definition vnum_def:
  vnum (n : num) : word8 list =
    if n < 128 then [n2w n] else n2w (128 + n MOD 128) :: vnum (n DIV 128)
End

Definition unvnum_def:
  unvnum [] = (0n, []) ∧
  unvnum ((b : word8) :: bs) =
    if w2n b < 128 then (w2n b, bs)
    else case unvnum bs of (n, rest) => (w2n b - 128 + 128 * n, rest)
End

Definition lits_enc_def:
  lits_enc [] = [] ∧
  lits_enc (bs :: bss) = vnum (LENGTH bs) ++ bs ++ lits_enc bss : word8 list
End

Theorem unvnum_LENGTH:
  ∀bs. LENGTH (SND (unvnum bs)) ≤ LENGTH bs ∧
       (bs ≠ [] ⇒ LENGTH (SND (unvnum bs)) < LENGTH bs)
Proof
  Induct >> rw[unvnum_def] >> Cases_on ‘unvnum bs’ >> gvs[] >>
  Cases_on ‘bs’ >> gvs[unvnum_def]
QED

Definition lits_dec_def:
  lits_dec (bs : word8 list) =
    if NULL bs then []
    else case unvnum bs of (n, rest) => take rest n :: lits_dec (drop rest n)
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rpt strip_tac >>
  qspec_then ‘bs’ mp_tac unvnum_LENGTH >> Cases_on ‘bs’ >> gvs[] >>
  simp[drop_def, LENGTH_DROP]
End

Theorem unvnum_vnum:
  ∀n rest. unvnum (vnum n ++ rest) = (n, rest)
Proof
  completeInduct_on ‘n’ >> rpt gen_tac >> simp[Once vnum_def] >>
  Cases_on ‘n < 128’ >> simp[unvnum_def] >>
  ‘n MOD 128 < 128’ by simp[] >>
  ‘(n MOD 128 + 128) MOD 256 = n MOD 128 + 128’ by simp[] >>
  ‘n DIV 128 < n’ by simp[DIV_LESS] >>
  simp[] >>
  qspec_then ‘128’ mp_tac DIVISION >> simp[] >>
  disch_then (qspec_then ‘n’ mp_tac) >> simp[]
QED

Theorem vnum_NOT_NIL[local]:
  vnum n ≠ []
Proof
  simp[Once vnum_def] >> rw[]
QED

Theorem lits_dec_enc:
  ∀bss. lits_dec (lits_enc bss) = bss
Proof
  Induct >- simp[lits_enc_def, Once lits_dec_def] >>
  rpt gen_tac >> REWRITE_TAC [lits_enc_def] >> ONCE_REWRITE_TAC [lits_dec_def] >>
  REWRITE_TAC [GSYM APPEND_ASSOC, unvnum_vnum] >>
  simp[NULL_EQ, vnum_NOT_NIL, take_def, drop_def,
       TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED
