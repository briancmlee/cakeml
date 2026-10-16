(*
  The echo server's select set: the listener and the live connections.

  The loop keeps a list of live fds (lstep, over the pairs of actions and
  responses of each round):
  - an accept that hands out c adds c;
  - a read of c that returns EOF removes one occurrence of c.
  It starts with the listener.  live_of l0 U is this list after the pairs U.

  MAIN:
  - quiet_secho: the echo server, in the socket vocabulary, is a quiet
    Level 2 computation (secho: srelabel (server lfd), with the Level 2
    server's declared interest);
  - sel_covers_echo: the live fds after the server's transcript cover
    everything it waits for, so the loop may select on them
    (loopSelectSet).
  This uses echoBlockingWaits's server_live, with the transcripts related
  by relabel's trans_relabel.  No assumption on the history.
*)
Theory echoBlockingSet
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServer2 relabel relabelDist echoSockModel
  loopPollWorld echoBlockingWaits loopSelectSet echoSelectIdle
  loopSelectWorld
Libs
  preamble

(* ------------------------------------------------------------------------
   The live list
   ------------------------------------------------------------------------ *)

Definition remove_one_def:
  remove_one c [] = [] ∧
  remove_one c (x :: xs) = if x = c then xs else x :: remove_one c xs
End

Definition lstep_def:
  lstep (live : word64 list) ((a, r) : sact # sresp option) =
    case (a, r) of
    | (Accept l, SOME (Accepted (SOME c))) => c :: live
    | (Read c n, SOME (Got (SOME bs))) => if bs = [] then remove_one c live else live
    | _ => live
End

Definition live_of_def:
  live_of l0 U = FOLDL lstep l0 U
End

Theorem live_of_APPEND:
  live_of l0 (U1 ++ U2) = live_of (live_of l0 U1) U2
Proof
  simp[live_of_def, FOLDL_APPEND]
QED

(* Counting in the socket vocabulary *)
Definition occ_def:
  occ w (l : word64 list) = LENGTH (FILTER (λx. x = w) l)
End

Definition s_is_acc_def:
  s_is_acc w (p : sact # sresp option) ⇔
    (∃l. FST p = Accept l) ∧ SND p = SOME (Accepted (SOME w))
End

Definition s_is_eof_def:
  s_is_eof w (p : sact # sresp option) ⇔
    (∃n. FST p = Read w n) ∧ SND p = SOME (Got (SOME []))
End

Theorem occ_remove_one:
  ∀c w l. occ w l ≤ occ w (remove_one c l) + (if c = w then 1 else 0)
Proof
  ntac 2 gen_tac >> Induct >> simp[remove_one_def, occ_def] >> gen_tac >>
  Cases_on ‘h = c’ >> simp[] >>
  Cases_on ‘h = w’ >> fs[occ_def] >>
  Cases_on ‘c = w’ >> fs[]
QED

Theorem lstep_occ:
  occ w l0 + (if s_is_acc w p then 1 else 0) ≤
  occ w (lstep l0 p) + (if s_is_eof w p then 1 else 0)
Proof
  PairCases_on ‘p’ >> simp[lstep_def] >> every_case_tac >>
  gvs[s_is_acc_def, s_is_eof_def] >>
  TRY (simp[occ_def] >> Cases_on ‘w = x’ >> gvs[] >> NO_TAC)
  >> TRY (qspecl_then [‘c’, ‘w’, ‘l0’] mp_tac occ_remove_one >> simp[] >> NO_TAC)
  >> qspecl_then [‘c’, ‘c’, ‘l0’] mp_tac occ_remove_one >> simp[]
QED

(* MAIN: the live list counts at least the accepts not yet matched by an
   EOF *)
Theorem live_of_occ:
  ∀U l0. occ w l0 + LENGTH (FILTER (s_is_acc w) U) ≤
         occ w (live_of l0 U) + LENGTH (FILTER (s_is_eof w) U)
Proof
  Induct >> simp[live_of_def] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘lstep l0 h’ mp_tac) >>
  simp[GSYM live_of_def] >>
  qspecl_then [‘w’, ‘l0’, ‘h’] mp_tac (Q.GENL [‘w’, ‘l0’, ‘p’] lstep_occ) >>
  rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   Counts in the two vocabularies
   ------------------------------------------------------------------------ *)

Overload TRELS = “λtt U. MAP (λ(a, r). (sfa a, r)) tt =
                         MAP (λ(a, r). (a, OPTION_MAP sfr r)) U”

Theorem sfa_Accept[local]:
  sfa a0 = Accept l ⇔ ∃l0. a0 = Accept l0 ∧ l = n2w l0
Proof
  Cases_on ‘a0’ >> simp[sfa_def] >> metis_tac[]
QED

Theorem sfa_Read[local]:
  sfa a0 = Read w n ⇔ ∃fd. a0 = Read fd ∧ w = n2w fd ∧ n = bufsz
Proof
  Cases_on ‘a0’ >> simp[sfa_def] >> metis_tac[]
QED

Theorem sfr_Accepted[local]:
  sfr r = Accepted fd ⇔ ∃c. r = Accepted (SOME c) ∧ fd = w2n c
Proof
  Cases_on ‘r’ >> simp[sfr_def]
  >- (Cases_on ‘o'’ >> simp[sfr_def] >> metis_tac[])
  >- (Cases_on ‘o'’ >> simp[sfr_def] >> rw[])
QED

Theorem sfr_Eof[local]:
  sfr r = Eof ⇔ r = Got (SOME [])
Proof
  Cases_on ‘r’ >> simp[sfr_def]
  >- (Cases_on ‘o'’ >> simp[sfr_def])
  >- (Cases_on ‘o'’ >> simp[sfr_def] >> rw[])
QED

(* Pointwise: a socket pair and the model pair it corresponds to *)
Theorem pair_acc[local]:
  (sfa a0, r0) = (a, OPTION_MAP sfr ro) ⇒
  (s_is_acc w (a, ro) ⇔ is_acc (w2n w) (a0, r0))
Proof
  rw[s_is_acc_def, is_acc_def] >> eq_tac >> rw[] >> gvs[sfa_Accept, sfa_def, sfr_def]
  >> TRY (qpat_x_assum ‘_ = sfr _’ (assume_tac o GSYM) >> gvs[sfr_Accepted])
QED

Definition is_eof_alias_def:
  is_eof_alias (w : word64) (p : action # response option) ⇔
    (∃fd. FST p = Read fd ∧ n2w fd = w) ∧ SND p = SOME Eof
End

Theorem pair_eof[local]:
  (sfa a0, r0) = (a, OPTION_MAP sfr ro) ⇒
  (s_is_eof w (a, ro) ⇔ is_eof_alias w (a0, r0))
Proof
  rw[s_is_eof_def, is_eof_alias_def] >> eq_tac >> rw[] >> gvs[sfa_Read, sfa_def, sfr_def]
  >> metis_tac[sfr_Eof]
QED

Theorem TRELS_counts:
  ∀U tt. TRELS tt U ⇒
    LENGTH (FILTER (s_is_acc w) U) = accs (w2n w) tt ∧
    LENGTH (FILTER (s_is_eof w) U) = LENGTH (FILTER (is_eof_alias w) tt)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘tt’ >> simp[] >>
  PairCases_on ‘h'’ >> PairCases_on ‘h’ >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  ‘(sfa h'0, h'1) = (h0, OPTION_MAP sfr h1)’ by simp[] >>
  drule pair_acc >> drule pair_eof >> rpt strip_tac >>
  simp[] >> rw[] >> gvs[]
QED

(* In a transcript related to a socket one, every accepted fd is small *)
Theorem TRELS_accs_big:
  ∀U tt. TRELS tt U ∧ dimword(:64) ≤ fd ⇒ accs fd tt = 0
Proof
  Induct >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> Cases_on ‘tt’ >> simp[] >>
  PairCases_on ‘h'’ >> PairCases_on ‘h’ >> simp[] >> strip_tac >>
  simp[is_acc_def] >> rw[] >> gvs[] >>
  qpat_x_assum ‘_ = sfr _’ (assume_tac o GSYM) >> gvs[sfr_Accepted] >>
  rename1 ‘w2n cc’ >>
  ‘w2n cc < dimword(:64)’ by simp[w2n_lt] >> fs[wordsTheory.dimword_64]
QED

Theorem eof_alias_eofs:
  (∀fd. eofs fd tt ≤ accs fd tt) ∧ (∀fd. dimword(:64) ≤ fd ⇒ accs fd tt = 0) ⇒
  LENGTH (FILTER (is_eof_alias w) tt) = eofs (w2n w) tt
Proof
  strip_tac >> simp[eofs_def] >> AP_TERM_TAC >> simp[rich_listTheory.FILTER_EQ] >>
  PairCases >> rw[is_eof_alias_def, is_eof_def] >> eq_tac >> rw[] >> simp[] >>
  CCONTR_TAC >>
  ‘eofs fd tt = 0’
    by (first_x_assum (qspec_then ‘fd’ mp_tac) >>
        first_x_assum (qspec_then ‘fd’ mp_tac) >> simp[]) >>
  gvs[eofs_def, FILTER_EQ_NIL, EVERY_MEM] >>
  first_x_assum drule >> simp[is_eof_def]
QED

(* ------------------------------------------------------------------------
   The echo server as a quiet Level 2 computation, socket vocabulary
   ------------------------------------------------------------------------ *)

Definition secho_def:
  secho lfd =
    <| run := srelabel (server lfd);
       interest := λh. { w : word64 | Readable (w2n w) ∈ (server2 lfd).interest (MAP sfs h) } |>
End

Definition sel_echo_def:
  sel_echo lfd h = live_of [n2w lfd] (trans (srelabel (server lfd)) h)
End

Theorem secho_run:
  (secho lfd).run = srelabel (server lfd)
Proof
  simp[secho_def]
QED

Theorem quiet_server2[local]:
  quiet (server2 lfd)
Proof
  metis_tac[wf2_server2, wf2_def]
QED

(* MAIN: the echo server, relabelled, is quiet for its declared interest *)
Theorem quiet_secho:
  quiet (secho lfd)
Proof
  ‘quiet (server2 lfd)’ by metis_tac[wf2_server2, wf2_def] >>
  fs[quiet_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [‘MAP sfs h’, ‘sfs s’, ‘MAP sfs h'’] mp_tac) >>
  impl_tac
  >- (gvs[secho_def, relabel_def, new_actions_relabel, snap_map_def, sfe_def,
          IN_DISJOINT] >> metis_tac[])
  >> strip_tac >> fs[secho_def, relabel_def]
QED

Theorem wf_secho:
  wf (secho lfd).run
Proof
  simp[wf_echo, secho_run]
QED

Theorem occ_MEM:
  ∀l. 0 < occ w l ⇒ MEM w l
Proof
  Induct >> simp[occ_def] >> gen_tac >> Cases_on ‘h = w’ >> simp[] >>
  fs[occ_def]
QED

(* MAIN: the live fds cover what the server waits for *)
Theorem sel_covers_echo:
  lfd < dimword(:64) ⇒ sel_covers (secho lfd) (sel_echo lfd)
Proof
  rw[sel_covers_def, SUBSET_DEF] >> rename1 ‘w ∈ _’ >>
  gvs[secho_def, sel_echo_def] >>
  qabbrev_tac ‘U = trans (srelabel (server lfd)) h’ >>
  ‘TRELS (trans (server lfd) (MAP sfs h)) U’
    by (simp[Abbr ‘U’] >> irule trans_relabel >> simp[snap_map_def]) >>
  qspec_then ‘MAP sfs h’ strip_assume_tac server_live >>
  ‘∀fd. dimword(:64) ≤ fd ⇒ accs fd (trans (server lfd) (MAP sfs h)) = 0’
    by (rpt strip_tac >> irule TRELS_accs_big >> simp[] >> metis_tac[]) >>
  drule TRELS_counts >> disch_then (qspec_then ‘w’ strip_assume_tac) >>
  ‘LENGTH (FILTER (is_eof_alias w) (trans (server lfd) (MAP sfs h))) =
   eofs (w2n w) (trans (server lfd) (MAP sfs h))’
    by (irule eof_alias_eofs >> simp[]) >>
  qspecl_then [‘U’, ‘[n2w lfd]’] mp_tac live_of_occ >> simp[] >> strip_tac >>
  irule occ_MEM >>
  qpat_x_assum ‘∀x. Readable x ∈ _ ⇒ _’ drule >> strip_tac
  >- (‘w = n2w lfd’ by metis_tac[n2w_w2n] >> pop_assum SUBST_ALL_TAC >>
      qpat_x_assum ‘∀g. eofs g _ ≤ _’ (qspec_then ‘lfd’ mp_tac) >>
      gvs[occ_def])
  >> gvs[occ_def]
QED
