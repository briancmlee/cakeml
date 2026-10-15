(*
  For the model-based tester of socket_ffi.c (ffi_model_test.py,
  hol_check.py): the version-2 model's lowest_free is defined with LEAST,
  which EVAL cannot compute.  This lemma lets a concrete instance be decided
  by EVAL: f is the lowest free fd if all smaller ones are used and f is not.
*)
Theory ffiModelTest
Ancestors
  socketV2FFI rich_list
Libs
  preamble

Theorem lowest_free_intro:
  EVERY (λm. MEM (n2w m : word64) used) (COUNT_LIST f) ∧ ¬MEM (n2w f : word64) used ⇒
  lowest_free used = n2w f
Proof
  rw[EVERY_MEM, MEM_COUNT_LIST] >> simp[lowest_free_def] >>
  ‘(LEAST n. ¬MEM (n2w n : word64) used) = f’ suffices_by simp[] >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rw[] >> CCONTR_TAC >>
  ‘n < f ∨ f < n’ by simp[] >> metis_tac[]
QED
