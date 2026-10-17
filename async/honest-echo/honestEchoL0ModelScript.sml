(*
  The echo server's model safety, per handle (route (d), design/46): in the
  socket-vocabulary transcript of srelabel (server k), if the handles it
  was handed are distinct, then per handle the bytes it wrote are exactly
  the bytes it read (asyncServerSafety's echo_server_safety, through the
  relabelling).
*)
Theory honestEchoL0Model
Ancestors
  words asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncM4Relabel asyncM4RelabelDist asyncM3World asyncM4SockModel
Libs
  preamble

(* Per handle: the bytes written, the bytes read; and the handles accepted *)
Definition hwritten_def:
  hwritten (hd : word64) (tr : (sact # sresp option) list) =
    FLAT (MAP (λp. case FST p of Write hd' bs => if hd' = hd then bs else [] | _ => []) tr)
End

Definition hread_def:
  hread (hd : word64) (tr : (sact # sresp option) list) =
    FLAT (MAP (λp. case p of (Read hd' n, SOME (Got (SOME bs))) => if hd' = hd then bs else []
                           | _ => []) tr)
End

Definition haccepted_def:
  haccepted (tr : (sact # sresp option) list) =
    FLAT (MAP (λp. case p of (Accept l, SOME (Accepted (SOME c))) => [c] | _ => []) tr)
End

Theorem hwritten_APPEND[simp]:
  hwritten hd (t1 ++ t2) = hwritten hd t1 ++ hwritten hd t2
Proof
  simp[hwritten_def]
QED

Theorem hread_APPEND[simp]:
  hread hd (t1 ++ t2) = hread hd t1 ++ hread hd t2
Proof
  simp[hread_def]
QED

Theorem haccepted_APPEND[simp]:
  haccepted (t1 ++ t2) = haccepted t1 ++ haccepted t2
Proof
  simp[haccepted_def]
QED

Overload rl = “λxs ys. MAP (λ(a,r). (sfa a, r)) xs = MAP (λ(a,r). (a, OPTION_MAP sfr r)) ys”

Theorem w2n_lt64[local]:
  w2n (c : word64) < 18446744073709551616
Proof
  assume_tac (INST_TYPE [alpha |-> “:64”] w2n_lt) >> fs[]
QED

Theorem rl_written[local]:
  ∀xs ys. rl xs ys ∧ (∀fd d r. MEM (Write fd d, r) xs ⇒ fd < dimword (:64)) ⇒
        hwritten hd ys = FLAT (MAP (MAP (n2w o ORD)) (written (w2n hd) xs))
Proof
  Induct >> Cases_on ‘ys’ >> simp[hwritten_def, written_def] >>
  gen_tac >> PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  impl_tac >- metis_tac[] >>
  simp[hwritten_def, written_def] >> strip_tac >>
  Cases_on ‘h'0’ >> gvs[sfa_def] >>
  first_x_assum (qspecl_then [‘n’, ‘s’, ‘OPTION_MAP sfr h1’] mp_tac) >> simp[] >> strip_tac >>
  rw[] >> gvs[w2n_n2w] >> CCONTR_TAC >> gvs[w2n_n2w]
QED

Theorem rl_read[local]:
  ∀xs ys. rl xs ys ∧ (∀fd r. MEM (Read fd, r) xs ⇒ fd < dimword (:64)) ⇒
        hread hd ys = FLAT (MAP (MAP (n2w o ORD)) (read (w2n hd) xs))
Proof
  Induct >> Cases_on ‘ys’ >> simp[hread_def, read_def] >>
  gen_tac >> PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  impl_tac >- metis_tac[] >>
  simp[hread_def, read_def] >> strip_tac >>
  Cases_on ‘h'0’ >> gvs[sfa_def] >> Cases_on ‘h1’ >> gvs[] >>
  first_x_assum (qspecl_then [‘n’, ‘SOME (sfr x)’] mp_tac) >> simp[] >> strip_tac >>
  Cases_on ‘x’ >> gvs[sfr_def] >>
  TRY (rename1 ‘Got oo’ >> Cases_on ‘oo’) >> TRY (rename1 ‘Accepted oo’ >> Cases_on ‘oo’) >>
  gvs[sfr_def] >>
  ‘n2w n = hd ⇔ n = w2n hd’ by (eq_tac >> rw[] >> simp[w2n_n2w]) >>
  rw[] >> gvs[bytes_round_trip]
QED

Theorem rl_accepted:
  ∀xs ys. rl xs ys ⇒ accepted xs = MAP w2n (haccepted ys)
Proof
  Induct >> Cases_on ‘ys’ >> simp[haccepted_def, accepted_def] >>
  gen_tac >> PairCases_on ‘h’ >> PairCases_on ‘h'’ >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >>
  simp[haccepted_def, accepted_def] >> strip_tac >>
  Cases_on ‘h'0’ >> gvs[sfa_def] >> Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘x’ >> gvs[sfr_def] >>
  TRY (rename1 ‘Got oo’ >> Cases_on ‘oo’) >> TRY (rename1 ‘Accepted oo’ >> Cases_on ‘oo’) >>
  gvs[sfr_def] >> rw[]
QED

(* MAIN: per handle, the echo server writes exactly what it read *)
Theorem server_handle_echo:
  ALL_DISTINCT (haccepted (trans (srelabel (server k)) h)) ⇒
  hwritten hd (trans (srelabel (server k)) h) = hread hd (trans (srelabel (server k)) h)
Proof
  strip_tac >>
  ‘rl (trans (server k) (MAP sfs h)) (trans (srelabel (server k)) h)’
    by (irule trans_relabel >> simp[snap_map_def]) >>
  drule rl_accepted >> strip_tac >>
  qspecl_then [‘MAP sfs h’] mp_tac (Q.INST [‘lfd’ |-> ‘k’] server_echoes) >>
  impl_tac >- (simp[fresh_def] >> irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  strip_tac >>
  ‘∀fd. EXISTS (on_fd fd) (trans (server k) (MAP sfs h)) ⇒ fd < dimword (:64)’
    by (rpt strip_tac >> first_x_assum drule >>
        qpat_x_assum ‘accepted _ = _’ (fn th => rewrite_tac[th]) >>
        simp[MEM_MAP, PULL_EXISTS, w2n_lt64]) >>
  drule rl_written >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[EXISTS_MEM] >>
               first_assum (irule_at Any) >> simp[on_fd_def]) >>
  strip_tac >>
  drule rl_read >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[EXISTS_MEM] >>
               first_assum (irule_at Any) >> simp[on_fd_def]) >>
  strip_tac >> simp[]
QED
