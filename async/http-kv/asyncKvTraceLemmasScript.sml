(*
  Lemmas for asyncKvSafe: strings and bytes, printed requests and replies,
  the store's answers.
*)
Theory asyncKvTraceLemmas
Ancestors
  list rich_list words EchoSpec HttpSpec HttpSpecBodies HttpKvSpec
  asyncHttpParse asyncHttpParseH asyncHttpParseB asyncWithStore asyncKvModel
Libs
  preamble

(* ------------------------------------------------------------------------
   Strings and bytes
   ------------------------------------------------------------------------ *)

Theorem bytes_prefix_iff:
  ∀s t. bytes s ≼ bytes t ⇔ s ≼ t
Proof
  simp[bytes_def] >> Induct >> Cases_on ‘t’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >>
  simp[] >> metis_tac[ORD_11]
QED

Theorem bytes_split:
  ∀p s rest. bytes s = bytes p ++ rest ⇒ ∃s'. s = p ++ s' ∧ bytes s' = rest
Proof
  simp[bytes_def] >> Induct >> simp[] >> rpt strip_tac >> Cases_on ‘s’ >> gvs[] >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[ORD_11] >>
  metis_tac[]
QED

Theorem bytes_chars:
  bytes (MAP (CHR o w2n) (bs : word8 list)) = bs
Proof
  simp[bytes_def, MAP_MAP_o, combinTheory.o_DEF, w2n_lt_256, ORD_CHR_RWT]
QED

Theorem LENGTH_bytes[simp]:
  LENGTH (bytes s) = LENGTH s
Proof
  simp[bytes_def]
QED

Theorem bytes_APPEND:
  bytes (a ++ b) = bytes a ++ bytes b
Proof
  simp[bytes_def]
QED

(* ------------------------------------------------------------------------
   Printed requests
   ------------------------------------------------------------------------ *)

Theorem print_brequest_NIL:
  print_brequest r ≠ []
Proof
  Cases_on ‘r’ >> simp[print_brequest_def]
QED

Theorem print_response_NIL:
  print_response a ≠ []
Proof
  Cases_on ‘a’ >> simp[print_response_def]
QED

(* What has been read, as complete requests rs and a rest without a full
   request, parses to exactly rs *)
Theorem read_brequests_parse:
  bytes s = brequests rs ++ rest ∧
  EVERY valid_brequest rs ∧ no_full_brequest rest ⇒
  parse_all_b s = rs
Proof
  rw[brequests_def] >> drule bytes_split >> strip_tac >> gvs[] >>
  irule parse_all_brequests >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[no_full_brequest_def] >> first_x_assum drule >>
  simp[brequests_def, bytes_APPEND, IS_PREFIX_APPEND]
QED

Theorem parse_all_b_prefix:
  s ≼ t ⇒ parse_all_b s ≼ parse_all_b t
Proof
  rw[] >> gvs[IS_PREFIX_APPEND] >>
  metis_tac[parse_all_b_mono, IS_PREFIX_APPEND]
QED

(* MAIN: the requests parsed from s were printed at the front of s *)
Theorem parse_all_b_printed:
  ∀rs s. rs ≼ parse_all_b s ⇒ FLAT (MAP print_brequest rs) ≼ s
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once parse_all_b_def] >> CASE_TAC >> simp[] >> strip_tac >>
  drule parse_bcomplete >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem brequests_TAKE_SUC:
  i < LENGTH rs ∧ brequests (TAKE (SUC i) rs) ≼ x ⇒
  ¬(x ≼ brequests (TAKE i rs))
Proof
  rpt strip_tac >>
  ‘brequests (TAKE (SUC i) rs) ≼ brequests (TAKE i rs)’
    by metis_tac[IS_PREFIX_TRANS] >>
  ‘TAKE (SUC i) rs = TAKE i rs ++ [EL i rs]’ by simp[TAKE_SUC_EL] >>
  gvs[brequests_def, bytes_APPEND] >>
  drule IS_PREFIX_LENGTH >> simp[] >> simp[print_brequest_NIL] >>
  Cases_on ‘print_brequest (EL i rs)’ >> fs[print_brequest_NIL]
QED

(* ------------------------------------------------------------------------
   Printed replies
   ------------------------------------------------------------------------ *)

Theorem TAKE_prefix_mono[local]:
  ∀l a b. a ≤ b ⇒ TAKE a l ≼ TAKE b l
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘a’ >> Cases_on ‘b’ >> simp[]
QED

Theorem reply_bytes_prefix0[local]:
  as1 ≼ as2 ⇒ reply_bytes as1 ≼ reply_bytes as2
Proof
  rw[IS_PREFIX_APPEND, reply_bytes_def] >> simp[bytes_APPEND]
QED

Theorem reply_bytes_TAKE:
  i < LENGTH R ∧ j ≤ i ∧ reply_bytes (TAKE (SUC i) R) ≼ x ⇒
  ¬(x ≼ reply_bytes (TAKE j R))
Proof
  rpt strip_tac >>
  ‘TAKE (SUC i) R = TAKE i R ++ [EL i R]’ by simp[TAKE_SUC_EL] >>
  ‘LENGTH (reply_bytes (TAKE j R)) ≤ LENGTH (reply_bytes (TAKE i R))’
    by metis_tac[reply_bytes_prefix0, IS_PREFIX_LENGTH, TAKE_prefix_mono] >>
  ‘LENGTH (reply_bytes (TAKE (SUC i) R)) =
   LENGTH (reply_bytes (TAKE i R)) + LENGTH (print_response (EL i R))’
    by (pop_assum kall_tac >> asm_rewrite_tac[] >>
        simp[reply_bytes_def, bytes_APPEND, FLAT_APPEND]) >>
  ‘0 < LENGTH (print_response (EL i R))’
    by (Cases_on ‘print_response (EL i R)’ >> fs[print_response_NIL]) >>
  imp_res_tac IS_PREFIX_LENGTH >> decide_tac
QED

Theorem reply_bytes_prefix:
  as1 ≼ as2 ⇒ reply_bytes as1 ≼ reply_bytes as2
Proof
  rw[IS_PREFIX_APPEND, reply_bytes_def] >> simp[bytes_APPEND]
QED

(* ------------------------------------------------------------------------
   The store
   ------------------------------------------------------------------------ *)

Theorem kv_run_store:
  ∀qs st. kv_run st (MAP SND qs) = FST (run_store kv_delta st qs)
Proof
  Induct >> simp[kv_run_def, run_store_def, kv_delta_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem LENGTH_kv_run[simp]:
  ∀rs st. LENGTH (kv_run st rs) = LENGTH rs
Proof
  Induct >> simp[kv_run_def] >> rpt gen_tac >> pairarg_tac >> simp[]
QED

Theorem fd_answers_prefix:
  G1 ≼ G2 ⇒ fd_answers fd G1 ≼ fd_answers fd G2
Proof
  rw[IS_PREFIX_APPEND, fd_answers_def] >> REWRITE_TAC[run_store_APPEND_FST] >>
  qmatch_goalsub_abbrev_tac ‘ZIP (G1 ++ l, A1 ++ A2)’ >>
  ‘ZIP (G1 ++ l, A1 ++ A2) = ZIP (G1, A1) ++ ZIP (l, A2)’
    by (irule (GSYM ZIP_APPEND) >> simp[Abbr ‘A1’, Abbr ‘A2’, LENGTH_run_store]) >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[FILTER_APPEND, MAP_APPEND] >> metis_tac[]
QED

Theorem LENGTH_FILTER_ZIP_FST[local]:
  ∀G A. LENGTH A = LENGTH G ⇒
        LENGTH (FILTER (λp. FST (FST p) = fd) (ZIP (G, A))) =
        LENGTH (FILTER (λq. FST q = fd) G)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘A’ >> simp[] >> rw[]
QED

Theorem LENGTH_fd_answers:
  LENGTH (fd_answers fd G) = LENGTH (FILTER (λq. FST q = fd) G)
Proof
  simp[fd_answers_def] >> irule LENGTH_FILTER_ZIP_FST >> simp[LENGTH_run_store]
QED
