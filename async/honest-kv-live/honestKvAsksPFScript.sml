(*
  K-asks on the PF KV run (pol_self hw): L1 cannot stop asking on f for
  good while f's handle stays in the interest set and f is no longer
  fetched (quiet_from), as long as f's inbox empties once f is no longer
  fetched (S3f's premise; kv_S3f gives it for f's connection when what L1
  fetched on f is valid).

  From round N on f's inbox only shrinks (quiet_fkeep), so once empty it
  stays empty; then every round pauses f (quiet_round), so f's outbox is
  over hw or the round wrote bytes on h (paused_self); S4w at f
  (kv_S4w_f) rules out both from some round on.

  MAIN: kv_S3f, kv_asks_pf.
*)
Theory honestKvAsksPF
Ancestors
  honestKvStop honestKvPeerValid honestKvL0AsksRun honestKvReadSoonPF honestKvL0Obl
  honestL1PFS4w honestL1PFOutLive honestL1PFObl honestL1PFLive honestL1PFRound
  honestL1PFModel
Libs
  preamble

(* S3f's premise at f, for f connected in round a and never again, if what
   L1 fetched on f is always a prefix of printed valid requests *)
Theorem kv_S3f:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧
  MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 a) ∧
  (∀k. a < k ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 k)) ∧
  (∀M. ∃rqs. EVERY valid_brequest rqs ∧
             fdata f (rlogs (n2w lfdn) pol KI KS w0 a M) ≼
             HttpSpec$bytes (FLAT (MAP print_brequest rqs))) ⇒
  ∀n. (∀k. n ≤ k ⇒ ¬fetched_at (n2w lfdn) pol KI KS w0 k f) ⇒
      ∃n'. n ≤ n' ∧ inb_of (rstate (n2w lfdn) pol KI KS w0 n') f = []
Proof
  rpt strip_tac >>
  qspecl_then [‘a’, ‘f’, ‘lfdn’, ‘MAX n (SUC a)’, ‘pol’, ‘w0’] mp_tac
    (Q.GENL [‘a’, ‘f’, ‘lfdn’, ‘n’, ‘pol’, ‘w0’] kv_S3w_conn) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >- simp[] >>
      rpt strip_tac >> qpat_x_assum ‘∀k. n ≤ k ⇒ ¬_’ (qspec_then ‘k’ mp_tac) >>
      fs[MAX_LE]) >>
  strip_tac >> qexists_tac ‘n'’ >> fs[MAX_LE]
QED

(* MAIN: L1 does not stop asking on f for good *)
Theorem kv_asks_pf:
  kv_run lfdn (pol_self hw) w0 ∧ qfresh w0 ∧
  quiet_from (n2w lfdn) (pol_self hw) KI KS w0 N h f ∧
  (∀k. N ≤ k ⇒ ¬fetched_at (n2w lfdn) (pol_self hw) KI KS w0 k f) ∧
  (∀n. (∀k. n ≤ k ⇒ ¬fetched_at (n2w lfdn) (pol_self hw) KI KS w0 k f) ⇒
       ∃n'. n ≤ n' ∧ inb_of (rstate (n2w lfdn) (pol_self hw) KI KS w0 n') f = []) ⇒
  F
Proof
  strip_tac >>
  ‘oassm (n2w lfdn) (pol_self hw) KI KS w0’
    by (qpat_x_assum ‘quiet_from _ _ _ _ _ _ _ _’ mp_tac >> simp[quiet_from_def]) >>
  (* f's inbox is empty from n1 on *)
  qpat_assum ‘∀n. (∀k. _) ⇒ _’ (qspec_then ‘N’ mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> rename1 ‘N ≤ n1’ >>
  drule quiet_fkeep >> strip_tac >>
  ‘∀k. n1 ≤ k ⇒ inb_of (rstate (n2w lfdn) (pol_self hw) KI KS w0 k) f = []’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀d. fkeep _ _ _ _ ∧ _’ (qspec_then ‘n1 − N’ (mp_tac o CONJUNCT2)) >>
        disch_then (qspec_then ‘k − N’ mp_tac) >>
        ‘N + (n1 − N) = n1 ∧ N + (k − N) = k ∧ n1 − N ≤ k − N’ by decide_tac >>
        asm_rewrite_tac[] >> simp[]) >>
  (* S4w at f *)
  ‘S4w (n2w lfdn) (pol_self hw) hw KI KS w0 f’
    by (irule kv_S4w_f >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘S4w _ _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [S4w_def]) >>
  disch_then (qspec_then ‘N’ mp_tac) >>
  impl_tac >- (rpt strip_tac >> qpat_x_assum ‘∀k. N ≤ k ⇒ ¬_’ (qspec_then ‘k’ mp_tac) >>
               simp[fetched_at_def]) >>
  strip_tac >> rename1 ‘N ≤ n2’ >>
  (* round n1 + n2 pauses f, yet its outbox is ≤ hw and it writes no bytes *)
  qabbrev_tac ‘k = n1 + n2’ >>
  ‘N ≤ k ∧ n1 ≤ k ∧ n2 ≤ k’ by simp[Abbr ‘k’] >>
  ‘fkeep (n2w lfdn) h f (rstate (n2w lfdn) (pol_self hw) KI KS w0 k)’
    by (qpat_x_assum ‘∀d. fkeep _ _ _ _ ∧ _’ (qspec_then ‘k − N’ (mp_tac o CONJUNCT1)) >>
        ‘N + (k − N) = k’ by decide_tac >> asm_rewrite_tac[]) >>
  qspecl_then [‘k’, ‘N’, ‘KI’, ‘h’, ‘f’, ‘n2w lfdn’, ‘KS’, ‘pol_self hw’, ‘w0’] mp_tac
    (Q.GENL [‘k’, ‘N’, ‘ifds’, ‘h’, ‘f’, ‘lfd’, ‘m’, ‘pol’, ‘w0’] quiet_round) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac
  >- (qpat_x_assum ‘inb_of _ f ≠ []’ mp_tac >> simp[]) >>
  qspecl_then [‘k’, ‘KI’, ‘h’, ‘f’, ‘hw’, ‘n2w lfdn’, ‘KS’, ‘w0’] mp_tac
    (Q.GENL [‘k’, ‘ifds’, ‘h’, ‘f’, ‘hw’, ‘lfd’, ‘m’, ‘w0’] paused_self) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘∀n''. n2 ≤ n'' ⇒ _’ (qspec_then ‘k’ mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  ‘ALOOKUP (rstate (n2w lfdn) (pol_self hw) KI KS w0 k).b.tbl h = SOME f’
    by fs[fkeep_def] >>
  strip_tac
  >- (qpat_x_assum ‘hw < _’ mp_tac >> simp[]) >>
  qpat_x_assum ‘∀h bs. _’ (qspecl_then [‘h’, ‘bs’] mp_tac) >> simp[]
QED
