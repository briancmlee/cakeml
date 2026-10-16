(*
  HTTP's per-connection safety survives relaying (http_relay_closed):
  reading more can only complete more requests, in order, because a
  printed valid request is never a proper prefix of another (parsing is
  monotone, parse_mono).
*)
Theory peerBufferHttp
Ancestors
  HttpGetSpec HttpSpec httpParse peerBuffer
Libs
  preamble

Theorem byte_11[local]:
  (n2w (ORD c1) : word8) = n2w (ORD c2) ⇔ c1 = c2
Proof
  ‘ORD c1 < 256 ∧ ORD c2 < 256’ by simp[ORD_BOUND] >>
  simp[n2w_11, dimword_8, ORD_11]
QED

Theorem bytes_prefix_iff:
  ∀s1 s2. bytes s1 ≼ bytes s2 ⇔ s1 ≼ s2
Proof
  Induct >> simp[bytes_def] >> gen_tac >> Cases >> simp[byte_11] >>
  fs[bytes_def]
QED

Theorem bytes_APPEND_l[local]:
  bytes (a ++ b) = bytes a ++ bytes b
Proof
  simp[bytes_def]
QED

Theorem brequests_CONS_l[local]:
  brequests (h :: t) = brequests [h] ++ brequests t
Proof
  simp[brequests_def, bytes_APPEND_l]
QED

Theorem print_prefix_free:
  valid_brequest x ∧ valid_brequest h ∧ print_brequest x ≼ print_brequest h ⇒ x = h
Proof
  rw[IS_PREFIX_APPEND] >>
  ‘parse_brequest (print_brequest h ++ []) = BComplete h []’ by simp[parse_bprint] >>
  ‘parse_brequest (print_brequest x ++ l) = BComplete x l’ by simp[parse_bprint] >>
  gvs[]
QED

Theorem prefix_APPEND_cases:
  r ≼ a ++ b ⇒ r ≼ a ∨ ∃r1. r = a ++ r1 ∧ r1 ≼ b
Proof
  strip_tac >> Cases_on ‘r ≼ a’ >> simp[] >> fs[IS_PREFIX_APPEND] >>
  qpat_x_assum ‘a ++ b = _’ (strip_assume_tac o REWRITE_RULE [APPEND_EQ_APPEND]) >>
  metis_tac[]
QED

(* MAIN: parsing is monotone *)
Theorem parse_mono:
  ∀rs' r rest'. EVERY valid_brequest rs' ∧ no_full_brequest rest' ∧
                r ≼ brequests rs' ++ rest' ⇒
                ∃rs rest. rs ≼ rs' ∧ EVERY valid_brequest rs ∧
                          r = brequests rs ++ rest ∧ no_full_brequest rest
Proof
  Induct
  >- (rw[] >> qexists_tac ‘r’ >>
      fs[brequests_def, bytes_def, no_full_brequest_def] >> rpt strip_tac >>
      res_tac >> metis_tac[IS_PREFIX_TRANS, brequests_def, bytes_def]) >>
  rpt strip_tac >> fs[] >>
  qpat_x_assum ‘r ≼ _’ mp_tac >> ONCE_REWRITE_TAC[brequests_CONS_l] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> strip_tac >>
  Cases_on ‘brequests [h] ≼ r’
  >- (fs[IS_PREFIX_APPEND] >> rveq >>
      ‘brequests rs' ++ rest' = l' ++ l’ by fs[] >>
      first_x_assum (qspecl_then [‘l'’, ‘rest'’] mp_tac) >>
      impl_tac >- (conj_tac >- fs[] >> qexists_tac ‘l’ >> fs[]) >> strip_tac >>
      qexistsl_tac [‘h :: rs’, ‘rest’] >> rveq >> simp[] >>
      ONCE_REWRITE_TAC[brequests_CONS_l] >> simp[brequests_def, bytes_def]) >>
  qexistsl_tac [‘[]’, ‘r’] >> simp[brequests_def, bytes_def] >>
  rw[no_full_brequest_def] >> strip_tac >>
  drule prefix_APPEND_cases >> strip_tac
  >- (‘brequests [r'] ≼ brequests [h]’ by metis_tac[IS_PREFIX_TRANS] >>
      fs[brequests_def, bytes_prefix_iff] >>
      ‘r' = h’ by metis_tac[print_prefix_free] >> fs[brequests_def])
  >> fs[IS_PREFIX_APPEND]
QED

Theorem bresponses_mono:
  rs ≼ rs' ⇒ bresponses files rs ≼ bresponses files rs'
Proof
  rw[IS_PREFIX_APPEND, bresponses_def] >> simp[MAP_APPEND, bytes_APPEND_l]
QED

(* MAIN: HTTP's per-connection safety is relay-closed *)
Theorem http_relay_closed:
  relay_closed (http_conn_safe files)
Proof
  rw[relay_closed_def, http_conn_safe_def] >>
  ‘r ≼ brequests rs ++ rest’ by fs[] >>
  drule_all parse_mono >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[IS_PREFIX_TRANS, bresponses_mono]
QED

Theorem http_relay_closed_claim_holds:
  http_relay_closed_claim
Proof
  simp[http_relay_closed_claim_def, http_relay_closed]
QED
