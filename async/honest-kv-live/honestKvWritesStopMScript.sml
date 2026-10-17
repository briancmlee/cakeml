(*
  KV stops writing on a connection that gets no more input (M4, any
  interest function): every Write on c from some round on carries no
  bytes.  The premise of honest-ffi's S4w_of_stop, at M4, for KV (the
  echo's is honestEchoL0Stop's echo_round_written_read).

  KV's model writes one response per query it answered (kv_server_serves:
  what it wrote on c is a prefix of the responses to c's queries, and c's
  queries a prefix of the requests parsed from what it read on c).  Once
  c's input stops, what was read on c is fixed, so c has boundedly many
  queries; their responses only grow (run_store over more queries extends
  the answers), so they settle, and so does what was written on c.

  MAIN: kv_m4_writes_stop, and uniformly over a set of connections,
  kv_m4_writes_stop_all.
*)
Theory honestKvWritesStopM
Ancestors
  asyncRunOkGen asyncKvModel asyncWithStore asyncM4Account
  asyncM4GTrans asyncM4GRounds asyncM4SockInv asyncM4SockModel asyncM4Relabel
  asyncM4LiveWorld asyncM3World ffiSpikeSocketFFI asyncServerSafety asyncCore HttpSpec HttpSpecBodies
Libs
  preamble

Overload KM[local] = “srelabel (kv_server lfdn)”

(* honestEchoL0Stop's (not an ancestor here) *)
Theorem sock_do_conns_none[local]:
  sock_do s a = SOME (r, s') ∧ ALOOKUP s.conns c = NONE ⇒ ALOOKUP s'.conns c = NONE
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs()] >>
  gvs[AFUPDKEY_ALOOKUP]
QED

Theorem sock_acts_noread[local]:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧
    (∀cn. ALOOKUP s.conns c = SOME cn ⇒ cn.incoming = []) ⇒
    pread_all c (ZIP (acts, rs)) = []
Proof
  Induct >> simp[sock_acts_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> conj_tac
  >- (Cases_on ‘h’ >> simp[pread_def] >> Cases_on ‘r’ >> simp[pread_def] >>
      rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[pread_def] >> rw[] >>
      gvs[sock_do_def, sock_read_def, AllCaseEqs()]) >>
  first_x_assum irule >> qexistsl_tac [‘evs'’, ‘s1’, ‘s'’] >> simp[] >>
  rpt strip_tac >>
  Cases_on ‘ALOOKUP s.conns c’
  >- (drule_all sock_do_conns_none >> simp[]) >>
  drule_all sock_do_conn >> strip_tac >> gvs[] >>
  Cases_on ‘∃k. h = Read c k’ >> gvs[]
QED

Theorem pwritten_all_mem[local]:
  ∀acts rs. MEM (Write c bs) acts ∧ LENGTH rs = LENGTH acts ⇒
            ∃p q. pwritten_all c (ZIP (acts, rs)) = p ++ bs ++ q
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[] >> strip_tac >> gvs[]
  >- (simp[pwritten_def] >> qexistsl_tac [‘[]’, ‘pwritten_all c (ZIP (acts, t))’] >>
      simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [‘pwritten c (h, h') ++ p’, ‘q’] >> simp[]
QED

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

(* A ≼-chain bounded in length from k0 on settles *)
Theorem chain_stable[local]:
  (∀n1 n2:num. n1 ≤ n2 ⇒ f n1 ≼ f n2) ∧ (∀n. k0 ≤ n ⇒ LENGTH (f n) ≤ (bnd:num)) ⇒
  ∃N. k0 ≤ N ∧ ∀n. N ≤ n ⇒ f n = f N
Proof
  strip_tac >>
  ‘∀D n. k0 ≤ n ∧ bnd − LENGTH (f n) ≤ D ⇒ ∃N. k0 ≤ N ∧ ∀m. N ≤ m ⇒ f m = f N’
    suffices_by (disch_then (qspecl_then [‘bnd’, ‘k0’] mp_tac) >> impl_tac >- (conj_tac >- simp[] >> irule SUB_LESS_EQ) >>
                 disch_then ACCEPT_TAC) >>
  Induct >> rpt strip_tac
  >- (qexists_tac ‘n’ >> simp[] >> rpt strip_tac >>
      ‘f n ≼ f m’ by simp[] >>
      ‘LENGTH (f n) ≤ LENGTH (f m)’ by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH (f m) ≤ bnd’ by simp[] >>
      ‘LENGTH (f m) = LENGTH (f n)’ by simp[] >>
      metis_tac[IS_PREFIX_LENGTH_ANTI]) >>
  Cases_on ‘∃m. n ≤ m ∧ LENGTH (f n) < LENGTH (f m)’
  >- (pop_assum strip_assume_tac >>
      qpat_x_assum ‘∀n. k0 ≤ n ∧ _ ⇒ _’ (qspec_then ‘m’ mp_tac) >>
      ‘LENGTH (f m) ≤ bnd’ by simp[] >> simp[]) >>
  qexists_tac ‘n’ >> simp[] >> rpt strip_tac >>
  ‘f n ≼ f m’ by simp[] >>
  ‘LENGTH (f n) ≤ LENGTH (f m)’ by metis_tac[IS_PREFIX_LENGTH] >>
  ‘LENGTH (f m) = LENGTH (f n)’ by (CCONTR_TAC >> fs[] >> first_x_assum (qspec_then ‘m’ mp_tac) >> simp[]) >>
  metis_tac[IS_PREFIX_LENGTH_ANTI]
QED

Theorem FLAT_prefix[local]:
  l1 ≼ l2 ⇒ FLAT l1 ≼ FLAT l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[FLAT_APPEND]
QED

Theorem bytes_inj[local]:
  ∀s t. HttpSpec$bytes s = HttpSpec$bytes t ⇒ s = t
Proof
  simp[HttpSpecTheory.bytes_def] >> Induct >> Cases_on ‘t’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256 ∧ ORD h' < 256’ by simp[ORD_BOUND] >> gvs[] >> metis_tac[ORD_11]
QED

Theorem fd_answers_prefix[local]:
  G1 ≼ G2 ⇒ fd_answers fd G1 ≼ fd_answers fd G2
Proof
  rw[IS_PREFIX_APPEND] >> simp[fd_answers_def, run_store_APPEND_FST] >>
  DEP_REWRITE_TAC[GSYM ZIP_APPEND] >> simp[FILTER_APPEND, MAP_APPEND]
QED

Theorem filter_zip_length[local]:
  ∀G A. LENGTH A = LENGTH G ⇒
        LENGTH (FILTER (λp. FST (FST p) = fd) (ZIP (G, A))) =
        LENGTH (FILTER (λq. FST q = fd) G)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘A’ >> simp[] >> rw[]
QED

Theorem fd_answers_length[local]:
  LENGTH (fd_answers fd G) = LENGTH (FILTER (λq. FST q = fd) G)
Proof
  simp[fd_answers_def] >> irule filter_zip_length >> simp[]
QED

Theorem gperf_mono[local]:
  ∀d n. gperf ifds m s0 n ≼ gperf ifds m s0 (n + d)
Proof
  Induct >> simp[ADD_CLAUSES, gperf_SUC] >> rpt gen_tac >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘gperf ifds m s0 (n + d)’ >> simp[]
QED

Theorem pwritten_nil[local]:
  ∀c acts rs bs. pwritten_all c (ZIP (acts, rs)) = [] ∧ LENGTH rs = LENGTH acts ∧
                 MEM (Write c bs) acts ⇒ bs = []
Proof
  rpt strip_tac >> drule_all pwritten_all_mem >> strip_tac >> gvs[]
QED

Theorem parse_all_b_nil[local]:
  parse_all_b "" = []
Proof
  simp[Once asyncHttpParseBTheory.parse_all_b_def] >> EVAL_TAC
QED

(* Only finitely many connections have been read from *)
Theorem pread_finite[local]:
  ∀P. ∃L. ∀c. pread_all c P ≠ [] ⇒ MEM c L
Proof
  Induct >- simp[] >> rpt strip_tac >> qpat_x_assum ‘∃L. _’ strip_assume_tac >> PairCases_on ‘h’ >> rename1 ‘(q, r) :: P’ >>
  Cases_on ‘q’ >> simp[pread_def] >>
  TRY (qexists_tac ‘L’ >> simp[] >> NO_TAC) >>
  qexists_tac ‘c :: L’ >> gen_tac >> Cases_on ‘c' = c’ >> simp[] >>
  ‘pread c' (Read c n, r) = []’
    by (Cases_on ‘r’ >> gvs[pread_def] >> rename1 ‘Got ro’ >> Cases_on ‘ro’ >> gvs[pread_def]) >>
  simp[]
QED

(* A bound for each of finitely many eventual properties bounds them all *)
Theorem list_bound[local]:
  ∀L. (∀x. MEM x L ⇒ ∃n. ∀k. n ≤ k ⇒ G x (k:num)) ⇒
      ∃n. ∀x k. MEM x L ∧ n ≤ k ⇒ G x k
Proof
  Induct >> simp[] >> rpt strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rename1 ‘∀k. n1 ≤ k ⇒ G h k’ >> rename1 ‘∀x k. MEM x L ∧ n2 ≤ k ⇒ G x k’ >>
  qexists_tac ‘MAX n1 n2’ >> rw[] >> simp[]
QED

(* ------------------------------------------------------------------------
   MAIN
   ------------------------------------------------------------------------ *)

Theorem kv_m4_writes_gen[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  (∀k cn. k0 ≤ k ∧ ALOOKUP (gstate ifds KM s0 k).conns c = SOME cn ⇒ cn.incoming = []) ⇒
  (pread_all c (gperf ifds KM s0 k0) = [] ⇒
   ∀k bs. k0 ≤ k ∧ MEM (Write c bs) (gacts ifds KM s0 k) ⇒ bs = []) ∧
  ∃n0. ∀k bs. n0 ≤ k ∧ MEM (Write c bs) (gacts ifds KM s0 k) ⇒ bs = []
Proof
  strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  ‘grun_ok ifds KM s0’ by metis_tac[gen_grun_ok] >>
  (* reads on c stop at k0 *)
  ‘∀d. pread_all c (gperf ifds KM s0 (k0 + d)) = pread_all c (gperf ifds KM s0 k0)’
    by (Induct >- simp[] >>
        REWRITE_TAC[ADD_CLAUSES, gperf_SUC, MAP_APPEND, FLAT_APPEND] >>
        qpat_x_assum ‘pread_all _ _ = _’ SUBST1_TAC >>
        ‘pread_all c (ZIP (gacts ifds KM s0 (k0 + d), gres ifds KM s0 (k0 + d))) = []’
          suffices_by simp[] >>
        drule_then (qspec_then ‘k0 + d’ strip_assume_tac) grun_ok_sock_acts >>
        qspecl_then [‘gacts ifds KM s0 (k0 + d)’, ‘gstate ifds KM s0 (k0 + d)’,
                     ‘gres ifds KM s0 (k0 + d)’, ‘evs’, ‘s'’] mp_tac sock_acts_noread >>
        impl_tac
        >- (conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
            qpat_x_assum ‘∀k cn. k0 ≤ k ∧ _ ⇒ _’ (qspecl_then [‘k0 + d’, ‘cn’] mp_tac) >>
            simp[]) >>
        simp[]) >>
  ‘∀n. HttpSpec$bytes (FLAT (read (w2n c) (TSg (kv_server lfdn) ifds s0 n))) =
       pread_all c (gperf ifds KM s0 n)’
    by (gen_tac >>
        ‘bytes_read_from c (FLAT (GENLIST (grounds_events ifds KM s0) n)) =
         HttpSpec$bytes (FLAT (read (w2n c) (TSg (kv_server lfdn) ifds s0 n)))’
          by (drule_all gen_rounds_bytes >>
              disch_then (qspecl_then [‘n’, ‘ifds’, ‘c’] strip_assume_tac) >> fs[bytes_def]) >>
        pop_assum (SUBST1_TAC o SYM) >> irule bytes_read_from_rounds >> first_assum ACCEPT_TAC) >>
  qabbrev_tac ‘R = FLAT (read (w2n c) (TSg (kv_server lfdn) ifds s0 k0))’ >>
  ‘∀n. k0 ≤ n ⇒ FLAT (read (w2n c) (TSg (kv_server lfdn) ifds s0 n)) = R’
    by (rpt strip_tac >> simp[Abbr ‘R’] >> irule bytes_inj >>
        qpat_assum ‘∀n. HttpSpec$bytes _ = _’ (fn th => REWRITE_TAC [th]) >>
        ‘n = k0 + (n − k0)’ by simp[] >> pop_assum SUBST1_TAC >>
        qpat_x_assum ‘∀d. pread_all _ _ = _’ (fn th => REWRITE_TAC [th])) >>
  (* what KV served on c *)
  qabbrev_tac ‘Q = λn. kv_queries lfdn (MAP sfs (ghist ifds KM s0 n))’ >>
  ‘∀n. MAP SND (FILTER (λq. FST q = w2n c) (Q n)) ≼
         parse_all_b (FLAT (read (w2n c) (TSg (kv_server lfdn) ifds s0 n))) ∧
       written (w2n c) (TSg (kv_server lfdn) ifds s0 n) ≼
         MAP print_response (fd_answers (w2n c) (Q n))’
    by (gen_tac >> simp[Abbr ‘Q’] >>
        ‘fresh (TSg (kv_server lfdn) ifds s0 n)’ by metis_tac[gen_fresh] >>
        drule kv_server_serves >> simp[]) >>
  qabbrev_tac ‘A = λn. fd_answers (w2n c) (Q n)’ >>
  ‘∀n1 n2. n1 ≤ n2 ⇒ A n1 ≼ A n2’
    by (rpt strip_tac >> simp[Abbr ‘A’, Abbr ‘Q’] >> irule fd_answers_prefix >>
        ‘MAP sfs (ghist ifds KM s0 n1) = TAKE n1 (MAP sfs (ghist ifds KM s0 n2))’
          by simp[GSYM MAP_TAKE, ghist_TAKE] >>
        pop_assum SUBST1_TAC >> simp[kv_queries_TAKE]) >>
  ‘∀n. k0 ≤ n ⇒ LENGTH (A n) ≤ LENGTH (parse_all_b R)’
    by (rpt strip_tac >> simp[Abbr ‘A’, fd_answers_length] >>
        qpat_x_assum ‘∀n. MAP SND _ ≼ _ ∧ _’ (qspec_then ‘n’ (mp_tac o CONJUNCT1)) >>
        qpat_x_assum ‘∀n. k0 ≤ n ⇒ FLAT _ = R’ (qspec_then ‘n’ mp_tac) >> simp[] >>
        disch_then kall_tac >> strip_tac >> drule IS_PREFIX_LENGTH >> simp[]) >>
  qspecl_then [‘A’, ‘k0’, ‘LENGTH (parse_all_b R)’] mp_tac
    (Q.GENL [‘f’, ‘k0’, ‘bnd’] chain_stable) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 ‘∀n. N1 ≤ n ⇒ A n = A N1’ >>
  (* what KV wrote on c settles *)
  qabbrev_tac ‘WB = λn. pwritten_all c (gperf ifds KM s0 n)’ >>
  ‘∀n1 n2. n1 ≤ n2 ⇒ WB n1 ≼ WB n2’
    by (rpt strip_tac >> simp[Abbr ‘WB’] >> irule FLAT_prefix >>
        irule isPREFIX_MAP >> ‘n2 = n1 + (n2 − n1)’ by simp[] >>
        pop_assum SUBST1_TAC >> simp[gperf_mono]) >>
  ‘∀n. WB (SUC n) = HttpSpec$bytes (FLAT (written (w2n c) (TSg (kv_server lfdn) ifds s0 n)))’
    by (gen_tac >> simp[Abbr ‘WB’] >>
        ‘bytes_written_to c (FLAT (GENLIST (grounds_events ifds KM s0) (SUC n))) =
         HttpSpec$bytes (FLAT (written (w2n c) (TSg (kv_server lfdn) ifds s0 n)))’
          by (drule_all gen_rounds_bytes >>
              disch_then (qspecl_then [‘n’, ‘ifds’, ‘c’] strip_assume_tac) >> fs[bytes_def]) >>
        pop_assum (SUBST1_TAC o SYM) >> irule (GSYM bytes_written_to_rounds) >>
        first_assum ACCEPT_TAC) >>
  conj_tac
  >- ((* nothing read on c by k0: nothing to answer, nothing written *)
      rpt strip_tac >>
      ‘HttpSpec$bytes R = HttpSpec$bytes ""’
        by (qunabbrev_tac ‘R’ >> qpat_assum ‘∀n. HttpSpec$bytes _ = _’ (fn th => REWRITE_TAC [th]) >>
            qpat_x_assum ‘pread_all c _ = []’ SUBST1_TAC >> simp[HttpSpecTheory.bytes_def]) >>
      ‘R = ""’ by (irule bytes_inj >> first_assum ACCEPT_TAC) >>
      ‘A k = []’
        by (qpat_x_assum ‘∀n. k0 ≤ n ⇒ LENGTH (A n) ≤ _’ (qspec_then ‘k’ mp_tac) >>
            qpat_x_assum ‘R = ""’ (fn th => REWRITE_TAC [th, parse_all_b_nil]) >> simp[]) >>
      ‘written (w2n c) (TSg (kv_server lfdn) ifds s0 k) = []’
        by (qpat_x_assum ‘∀n. MAP SND _ ≼ _ ∧ _’ (qspec_then ‘k’ (mp_tac o CONJUNCT2)) >>
            ‘fd_answers (w2n c) (Q k) = []’
              by (qpat_x_assum ‘A k = []’ mp_tac >> qunabbrev_tac ‘A’ >> BETA_TAC >> simp[]) >>
            pop_assum (fn th => REWRITE_TAC [th]) >> simp[]) >>
      ‘WB (SUC k) = []’
        by (qpat_x_assum ‘∀n. WB (SUC n) = _’ (qspec_then ‘k’ SUBST1_TAC) >>
            qpat_x_assum ‘written _ _ = []’ SUBST1_TAC >> simp[HttpSpecTheory.bytes_def]) >>
      ‘pwritten_all c (ZIP (gacts ifds KM s0 k, gres ifds KM s0 k)) = []’
        by (qpat_x_assum ‘WB (SUC k) = []’ mp_tac >> qunabbrev_tac ‘WB’ >> BETA_TAC >>
            REWRITE_TAC[gperf_SUC, MAP_APPEND, FLAT_APPEND, APPEND_eq_NIL] >> strip_tac) >>
      irule pwritten_nil >>
      qexistsl_tac [‘gacts ifds KM s0 k’, ‘c’, ‘gres ifds KM s0 k’] >>
      rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, drule_then (qspec_then ‘k’ ACCEPT_TAC) LENGTH_gres]) >>
  ‘∀n. N1 ≤ n ⇒ LENGTH (WB (SUC n)) ≤ LENGTH (FLAT (MAP print_response (A N1)))’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀n. WB (SUC n) = _’ (qspec_then ‘n’ SUBST1_TAC) >>
        simp[HttpSpecTheory.bytes_def] >>
        irule IS_PREFIX_LENGTH >> irule FLAT_prefix >>
        ‘A n = A N1’ by simp[] >>
        qpat_x_assum ‘A n = A N1’ (SUBST1_TAC o SYM) >>
        qunabbrev_tac ‘A’ >> BETA_TAC >> qpat_x_assum ‘∀n. MAP SND _ ≼ _ ∧ _’ (qspec_then ‘n’ (ACCEPT_TAC o CONJUNCT2))) >>
  qspecl_then [‘WB’, ‘SUC N1’, ‘LENGTH (FLAT (MAP print_response (A N1)))’] mp_tac
    (Q.GENL [‘f’, ‘k0’, ‘bnd’] chain_stable) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
      ‘n = SUC (n − 1)’ by simp[] >> pop_assum SUBST1_TAC >>
      qpat_x_assum ‘∀n. N1 ≤ n ⇒ LENGTH (WB (SUC n)) ≤ _’ irule >> simp[]) >>
  strip_tac >> rename1 ‘∀n. N2 ≤ n ⇒ WB n = WB N2’ >>
  qexists_tac ‘N2’ >> rpt strip_tac >>
  ‘WB (SUC k) = WB k’ by (‘WB (SUC k) = WB N2 ∧ WB k = WB N2’ by (conj_tac >> qpat_assum ‘∀n. N2 ≤ n ⇒ _’ irule >> simp[]) >> qpat_x_assum ‘WB k = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  ‘pwritten_all c (ZIP (gacts ifds KM s0 k, gres ifds KM s0 k)) = []’
    by (qpat_x_assum ‘WB (SUC k) = WB k’ mp_tac >> qunabbrev_tac ‘WB’ >> BETA_TAC >> REWRITE_TAC[gperf_SUC, MAP_APPEND, FLAT_APPEND, APPEND_EQ_SELF]) >>
  irule pwritten_nil >>
  qexistsl_tac [‘gacts ifds KM s0 k’, ‘c’, ‘gres ifds KM s0 k’] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, drule_then (qspec_then ‘k’ ACCEPT_TAC) LENGTH_gres]
QED

Theorem kv_m4_writes_stop:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  (∀k cn. k0 ≤ k ∧ ALOOKUP (gstate ifds KM s0 k).conns c = SOME cn ⇒ cn.incoming = []) ⇒
  ∃n0. ∀k bs. n0 ≤ k ∧ MEM (Write c bs) (gacts ifds KM s0 k) ⇒ bs = []
Proof
  strip_tac >> drule_all kv_m4_writes_gen >> strip_tac >> metis_tac[]
QED

(* MAIN: the same, uniformly over any set P of connections that get no
   more input from k0 on: only finitely many of them were read from by k0,
   and the others never write a byte from k0 on *)
Theorem kv_m4_writes_stop_all:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  (∀c k cn. P c ∧ k0 ≤ k ∧ ALOOKUP (gstate ifds KM s0 k).conns c = SOME cn ⇒
            cn.incoming = []) ⇒
  ∃n0. ∀k c bs. P c ∧ n0 ≤ k ∧ MEM (Write c bs) (gacts ifds KM s0 k) ⇒ bs = []
Proof
  strip_tac >>
  qspec_then ‘gperf ifds KM s0 k0’ strip_assume_tac pread_finite >>
  qspecl_then [‘λc k. P c ⇒ ∀bs. MEM (Write c bs) (gacts ifds KM s0 k) ⇒ bs = []’, ‘L’] mp_tac
    (Q.GEN ‘G’ list_bound) >>
  impl_tac
  >- (rpt strip_tac >> BETA_TAC >> Cases_on ‘P x’ >> simp[] >>
      qspecl_then [‘x’, ‘ifds’, ‘k0’, ‘lfdn’, ‘s0’] mp_tac
        (Q.GENL [‘c’, ‘ifds’, ‘k0’, ‘lfdn’, ‘s0’] kv_m4_writes_stop) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
                   rename1 ‘ALOOKUP (gstate _ _ _ kk).conns cc = SOME cn’ >>
                   qpat_assum ‘∀c k cn. P c ∧ _ ⇒ _’ (qspecl_then [‘cc’, ‘kk’, ‘cn’] mp_tac) >>
                   impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
      metis_tac[]) >>
  BETA_TAC >> strip_tac >> qexists_tac ‘MAX n k0’ >> rpt strip_tac >>
  Cases_on ‘pread_all c (gperf ifds KM s0 k0) = []’
  >- (qspecl_then [‘c’, ‘ifds’, ‘k0’, ‘lfdn’, ‘s0’] mp_tac
        (Q.GENL [‘c’, ‘ifds’, ‘k0’, ‘lfdn’, ‘s0’] kv_m4_writes_gen) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
                   rename1 ‘ALOOKUP (gstate _ _ _ kk).conns cc = SOME cn’ >>
                   qpat_assum ‘∀c k cn. P c ∧ _ ⇒ _’ (qspecl_then [‘cc’, ‘kk’, ‘cn’] mp_tac) >>
                   impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
      strip_tac >> qpat_x_assum ‘pread_all c _ = [] ⇒ _’ mp_tac >>
      impl_tac >- first_assum ACCEPT_TAC >> disch_then (qspecl_then [‘k’, ‘bs’] mp_tac) >> fs[MAX_LE]) >>
  ‘MEM c L’ by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘∀x k. MEM x L ∧ n ≤ k ⇒ _’ (qspecl_then [‘c’, ‘k’] mp_tac) >>
  simp[] >> impl_tac >- fs[MAX_LE] >> disch_then irule >> first_assum ACCEPT_TAC
QED
