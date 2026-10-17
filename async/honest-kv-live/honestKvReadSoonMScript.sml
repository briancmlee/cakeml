(*
  KV reads soon, on the M4 rounds: an accepted connection with unread input
  is read from again, provided what its client sent is always a prefix of
  printed valid requests (so the handler never stops on an invalid
  buffer).  The M4 counterpart of asyncM4LiveSoon's read_soon_live, for
  the KV server: the library's view of the handler (view_wrap,
  m_view_henv), the KV handler as the query machine (kv_proto_agree), and
  the query machine's read bound (honestKvReadQ's q_read_grow_valid).

  MAIN: kv_read_soon_m.
*)
Theory honestKvReadSoonM
Ancestors
  honestKvReadQ asyncKvLiveStore asyncKvLive asyncServerVKv asyncServerVLiveP
  asyncServerVLiveL asyncServerVLiveA asyncServerVLive asyncServerWithLive asyncM4LiveWorld
  asyncM4Drain asyncM4Account asyncRunOkGen asyncM4GTrans asyncKvModel
  asyncProtoB asyncProtoDrainV asyncProtoMachineV asyncProtoV asyncProto
  asyncServerV asyncServerVProgress asyncServerSafety asyncKvHandler asyncTranscript
  asyncLevel1 asyncCore HttpSpec
Libs
  preamble

Overload KVM[local] = “kv_server lfdn”
Overload KVH[local] = “λfd. kv_handler (fd, "")”
Overload SKV[local] =
  “sockV : ((asyncServer$action, num # brequest) kact, HttpSpec$response, num # brequest,
            (HttpSpec$response, asyncServer$response) kres) vocab”

Theorem kv_server_v:
  kv_server lfdn =
    with_store kv_delta (λk. NONE) (server_v sockV (λfd. kv_handler (fd, "")) lfdn)
Proof
  simp[kv_server_def, kv_inner_def, server_with_k_eq_v]
QED

(* ------------------------------------------------------------------------
   Reads, round by round
   ------------------------------------------------------------------------ *)

Theorem pread_reads[local]:
  ∀ps. pread_all c ps ≠ [] ⇒ ∃k. MEM (Read c k) (MAP FST ps)
Proof
  Induct >- simp[] >> Cases >> rename1 ‘(a, r)’ >> rpt strip_tac >>
  Cases_on ‘pread c (a, r) = []’ >- (fs[] >> metis_tac[]) >>
  ‘∃k. a = Read c k’
    by (Cases_on ‘a’ >> fs[pread_def] >> Cases_on ‘r’ >> fs[pread_def] >>
        rename1 ‘Got x’ >> Cases_on ‘x’ >> gvs[pread_def, AllCaseEqs()]) >>
  qexists_tac ‘k’ >> simp[]
QED

(* More read from c by round k' than by round k: c was read in between *)
Theorem pread_grow_reads:
  grun_ok ifds m s0 ⇒
  ∀k'. k ≤ k' ∧
       LENGTH (pread_all c (gperf ifds m s0 k)) < LENGTH (pread_all c (gperf ifds m s0 k')) ⇒
       ∃r. k ≤ r ∧ r < k' ∧ reads_c c (gacts ifds m s0 r)
Proof
  strip_tac >> Induct >- simp[] >> strip_tac >>
  Cases_on ‘k = SUC k'’ >- fs[] >>
  ‘k ≤ k'’ by simp[] >>
  Cases_on ‘pread_all c (ZIP (gacts ifds m s0 k', gres ifds m s0 k')) = []’
  >- (fs[gperf_SUC] >> qexists_tac ‘r’ >> simp[]) >>
  drule pread_reads >> strip_tac >> qexists_tac ‘k'’ >> simp[reads_c_def] >>
  ‘LENGTH (gres ifds m s0 k') = LENGTH (gacts ifds m s0 k')’ by simp[LENGTH_gres] >>
  qexists_tac ‘k''’ >> gvs[MAP_ZIP]
QED

(* ------------------------------------------------------------------------
   The handler's view
   ------------------------------------------------------------------------ *)

(* henv_t looks at t only on the prefixes of g *)
Theorem henv_t_cong:
  (∀j. j ≤ LENGTH g ⇒ t1 (TAKE j g) = t2 (TAKE j g)) ⇒
  (henv_t fd t1 g j0 D ⇔ henv_t fd t2 g j0 D)
Proof
  strip_tac >>
  ‘∀j. j ≤ LENGTH g ⇒ hread_t fd t1 g j = hread_t fd t2 g j’ by simp[hread_t_def] >>
  ‘∀j. j < LENGTH g ⇒ hread_t fd t1 g (SUC j) = hread_t fd t2 g (SUC j) ∧
                      t1 (TAKE j g) = t2 (TAKE j g)’ by simp[] >>
  simp[henv_t_def] >> eq_tac >> rpt strip_tac >> gvs[]
QED

(* What the view has read is what the loop has read (m_view_henv's first
   step; it needs no interest hypothesis) *)
Theorem m_view_read:
  uses_ok lfdn (M : 'mx smach) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  (∀j. j ≤ LENGTH g ⇒ FILTER (on_fd (w2n c)) (TSg M ifds s0 (a + j)) = t (TAKE j g)) ⇒
  ∀j. j ≤ LENGTH g ⇒ HttpSpec$bytes (hread_t (w2n c) t g j) = pread_all c (SPg M ifds s0 (a + j))
Proof
  strip_tac >>
  ‘grun_ok ifds (srelabel M) s0’ by (irule gen_grun_ok >> metis_tac[]) >>
  rpt strip_tac >> simp[hread_t_def] >>
  qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER _ _ = _’ (qspec_then ‘j’ mp_tac) >>
  impl_tac >- simp[] >> disch_then (SUBST1_TAC o SYM) >>
  simp[read_FILTER] >>
  ‘bytes_read_from c (FLAT (GENLIST (grounds_events ifds (srelabel M) s0) (a + j))) =
   pread_all c (SPg M ifds s0 (a + j))’
    by (irule bytes_read_from_rounds >> first_assum ACCEPT_TAC) >>
  drule_all m_rounds_bytes >> strip_tac >>
  first_x_assum (qspecl_then [‘ifds’, ‘c’, ‘a + j’] strip_assume_tac) >> metis_tac[]
QED

(* The parser waits on no input *)
Theorem proto_parse_nil:
  proto_ok P ∧ P.valid r ⇒ P.parse "" = PIncomplete
Proof
  strip_tac >>
  qspecl_then [‘P’, ‘r’, ‘""’, ‘P.print r’] mp_tac (Q.GENL [‘P’, ‘r’, ‘s’, ‘u’] proto_prefix) >>
  simp[] >> disch_then irule >> irule proto_nonempty >> simp[]
QED

(* The HttpSpec$bytes of a string, back *)
Theorem bytes_onto:
  ∀ws : word8 list. ∃D. HttpSpec$bytes D = ws
Proof
  Induct >- (qexists_tac ‘""’ >> simp[bytes_def]) >>
  rpt strip_tac >> fs[] >> qexists_tac ‘CHR (w2n h) :: D’ >>
  qspec_then ‘h’ assume_tac w2n_lt >> fs[bytes_def, ORD_CHR_RWT]
QED

Theorem wf_kv_sv[local]:
  asyncLevel1$wf (server_v SKV KVH lfdn)
Proof
  metis_tac[hokv_wf, wf_server_v, hokv_kv]
QED

(* view_wrap_ans for the KV server *)
Theorem kv_view[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
  MEM c (wacc (SPg KVM ifds s0 n)) ∧ n ≤ N ⇒
  ∃a g. a ≤ n ∧ LENGTH g + a = N ∧ prompt (kv_handler (w2n c, "")) g ∧
    (∀i. i < LENGTH g ⇒
         (EL i g).ready = (EL (a + i) (MAP sfs (ghist ifds (srelabel KVM) s0 N))).ready) ∧
    (∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd (w2n c)) (TSg KVM ifds s0 (a + j)) =
      sproj SKV (trans (kv_handler (w2n c, "")) (TAKE j g))) ∧
    ∀j. j ≤ LENGTH g ⇒
      FILTER (on_fd_v SKV (w2n c))
        (trans (server_v SKV KVH lfdn)
          (inner_hist kv_delta (λk. NONE) (server_v SKV KVH lfdn)
             (MAP sfs (ghist ifds (srelabel KVM) s0 (a + j))))) =
      trans (kv_handler (w2n c, "")) (TAKE j g)
Proof
  rewrite_tac[kv_server_v] >> strip_tac >>
  drule_at (Pos (el 6)) view_wrap_ans >>
  disch_then (fn th => drule_at (Pos last) th) >>
  disch_then (qspec_then ‘inner_hist kv_delta (λk. NONE)’ mp_tac) >>
  impl_tac >- simp[vocab_ok_sockV, wrap_ok_with_store, hokv_kv] >>
  strip_tac >> qexistsl_tac [‘a’, ‘g’] >> rpt conj_tac >> fs[]
QED

(* ------------------------------------------------------------------------
   MAIN
   ------------------------------------------------------------------------ *)

(* MAIN: an accepted KV connection with unread input, whose client only
   ever sent a prefix of printed valid requests, is read from again *)
Theorem kv_read_soon_m:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧ sched_wf s0 ∧
  interest_covers_e ifds (srelabel KVM) s0 ∧
  MEM c (wacc (SPg KVM ifds s0 n)) ∧
  ALOOKUP (gstate ifds (srelabel KVM) s0 n).conns c = SOME cn ∧ cn.incoming ≠ [] ∧
  (∀k. ∃rqs. EVERY valid_brequest rqs ∧
             sent_upto c k s0 ≼ HttpSpec$bytes (FLAT (MAP print_brequest rqs))) ⇒
  ∃i. reads_c c (SAg KVM ifds s0 (n + i))
Proof
  strip_tac >>
  ‘∃D. HttpSpec$bytes D = sent_upto c n s0’ by metis_tac[bytes_onto] >>
  qabbrev_tac ‘B = 2 * LENGTH (proto_all P_b D) + 4’ >>
  ‘uses_ok lfdn KVM’ by simp[kv_server_uses_ok] >>
  ‘grun_ok ifds (srelabel KVM) s0’ by (irule gen_grun_ok >> metis_tac[]) >>
  (* the handler's view, B + 1 rounds past n *)
  ‘n ≤ n + B + 1’ by simp[] >>
  drule_all kv_view >> strip_tac >>
  qabbrev_tac ‘fd = w2n c’ >>
  qabbrev_tac ‘t = λq. sproj SKV (trans (KVH fd) q)’ >>
  ‘henv_t fd t g (n − a) D’
    by (qspecl_then [‘lfdn’, ‘KVM’, ‘s0’, ‘ifds’, ‘c’, ‘n’, ‘D’, ‘a’, ‘g’, ‘n + B + 1’, ‘t’]
          mp_tac (Q.GENL [‘lfdn’, ‘M’, ‘s0’, ‘ifds’, ‘c’, ‘n’, ‘D’, ‘a’, ‘g’, ‘N’, ‘t’]
                    m_view_henv_e) >>
        impl_tac >- (simp[Abbr ‘t’, Abbr ‘fd’] >> gvs[]) >>
        simp[Abbr ‘fd’]) >>
  ‘∀j. j ≤ LENGTH g ⇒ HttpSpec$bytes (hread_t fd t g j) = pread_all c (SPg KVM ifds s0 (a + j))’
    by (qspecl_then [‘lfdn’, ‘KVM’, ‘s0’, ‘g’, ‘c’, ‘ifds’, ‘a’, ‘t’]
          mp_tac (Q.GENL [‘lfdn’, ‘M’, ‘s0’, ‘g’, ‘c’, ‘ifds’, ‘a’, ‘t’] m_view_read) >>
        impl_tac >- (simp[Abbr ‘t’, Abbr ‘fd’] >> gvs[]) >>
        simp[Abbr ‘fd’]) >>
  (* the store answered the handler's queries *)
  ‘∀j. j ≤ LENGTH g ⇒ kans_ok SKV (trans (KVH fd) (TAKE j g))’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ FILTER (on_fd_v _ _) _ = _’
          (qspec_then ‘j’ mp_tac) >>
        simp[Abbr ‘fd’] >> disch_then (SUBST1_TAC o SYM) >>
        irule kans_ok_FILTER >>
        irule (REWRITE_RULE [wrap_kans_def] wrap_kans_with_store) >>
        simp[wf_kv_sv]) >>
  (* so the handler is the query machine on g *)
  qabbrev_tac ‘qm = qcomp SKV P_b (λreq. SOME (fd, req)) kfin fd (QA "")’ >>
  ‘∀j. j ≤ LENGTH g ⇒ trans (KVH fd) (TAKE j g) = trans qm (TAKE j g)’
    by (rpt strip_tac >>
        ‘qm = kvq fd (fd, "")’ by simp[Abbr ‘qm’, qcomp_def] >>
        pop_assum SUBST1_TAC >> 
        irule kv_proto_agree >> metis_tac[]) >>
  ‘prompt qm g’
    by (‘prompt (KVH fd) g ⇔ prompt qm g’ suffices_by (strip_tac >> fs[Abbr ‘fd’]) >>
        irule prompt_cong >> simp[Abbr ‘qm’, wf_kv_handler, wf_qcomp]) >>
  ‘∀j. j ≤ LENGTH g ⇒
       Rq SKV P_b (λreq. SOME (fd, req)) kfin fd g j = hread_t fd t g j’
    by (rpt strip_tac >> simp[hread_t_def, Abbr ‘t’] >> fs[Abbr ‘qm’]) >>
  ‘qenv SKV P_b (λreq. SOME (fd, req)) kfin fd g (n − a) D’
    by (simp[GSYM henv_t_qenv] >>
        qpat_x_assum ‘henv_t _ _ _ _ _’ mp_tac >>
        ‘∀j. j ≤ LENGTH g ⇒ t (TAKE j g) = (λq. sproj SKV (trans qm q)) (TAKE j g)’
          by (rpt strip_tac >> simp[Abbr ‘t’] >>
              qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ trans (KVH fd) _ = _’ (qspec_then ‘j’ mp_tac) >>
              simp[]) >>
        drule henv_t_cong >> simp[]) >>
  (* what was sent by round n is not all read *)
  ‘∃inc. sent_upto c n s0 = pread_all c (SPg KVM ifds s0 n) ++ inc ∧
         (∀cn. ALOOKUP (gstate ifds (srelabel KVM) s0 n).conns c = SOME cn ⇒ inc = cn.incoming)’
    by (qspecl_then [‘s0’, ‘ifds’, ‘srelabel KVM’, ‘c’, ‘n’] mp_tac
          (Q.GENL [‘s0’, ‘ifds’, ‘m’, ‘c’, ‘k’] sent_split_sw) >>
        impl_tac >- simp[] >> strip_tac >>
        qexists_tac ‘inc’ >> simp[]) >>
  ‘inc = cn.incoming’ by (first_x_assum drule >> simp[]) >>
  ‘n − a ≤ LENGTH g ∧ a + (n − a) = n’ by simp[] >>
  ‘¬(D ≼ Rq SKV P_b (λreq. SOME (fd, req)) kfin fd g (n − a))’
    by (strip_tac >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ Rq _ _ _ _ _ _ j = _’ (qspec_then ‘n − a’ mp_tac) >>
        impl_tac >- simp[] >> disch_then SUBST_ALL_TAC >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ HttpSpec$bytes _ = _’ (qspec_then ‘n − a’ mp_tac) >>
        impl_tac >- simp[] >> asm_rewrite_tac[] >> strip_tac >>
        ‘HttpSpec$bytes D ≼ pread_all c (SPg KVM ifds s0 n)’
          by (qpat_x_assum ‘HttpSpec$bytes (hread_t _ _ _ _) = _’ (SUBST1_TAC o SYM) >>
              REWRITE_TAC[bytes_prefix_sw] >> first_assum ACCEPT_TAC) >>
        ‘LENGTH (HttpSpec$bytes D) = LENGTH (pread_all c (SPg KVM ifds s0 n)) + LENGTH cn.incoming’
          by (qpat_x_assum ‘HttpSpec$bytes D = _’ SUBST1_TAC >>
              qpat_x_assum ‘sent_upto _ _ _ = _ ++ _’ SUBST1_TAC >>
              qpat_x_assum ‘inc = _’ SUBST1_TAC >> simp[]) >>
        ‘LENGTH cn.incoming ≠ 0’
          by (qpat_x_assum ‘cn.incoming ≠ []’ mp_tac >> simp[LENGTH_NIL]) >>
        drule IS_PREFIX_LENGTH >>
        qpat_x_assum ‘LENGTH (HttpSpec$bytes D) = _’ SUBST1_TAC >> simp[]) >>
  (* and what was read is always a prefix of printed valid requests *)
  ‘∀i. i ≤ LENGTH g ⇒
       ∃rqs. EVERY P_b.valid rqs ∧
             Rq SKV P_b (λreq. SOME (fd, req)) kfin fd g i ≼ FLAT (MAP P_b.print rqs)’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀k. ∃rqs. _’ (qspec_then ‘a + i’ strip_assume_tac) >>
        qexists_tac ‘rqs’ >> simp[P_b_def] >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ Rq _ _ _ _ _ _ j = _’ (qspec_then ‘i’ mp_tac) >>
        impl_tac >- simp[] >> disch_then SUBST1_TAC >>
        REWRITE_TAC[GSYM bytes_prefix_sw] >>
        qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ HttpSpec$bytes _ = _’ (qspec_then ‘i’ mp_tac) >>
        impl_tac >- simp[] >> disch_then SUBST1_TAC >>
        irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c (a + i) s0’ >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qspecl_then [‘s0’, ‘ifds’, ‘srelabel KVM’, ‘c’, ‘a + i’] mp_tac
          (Q.GENL [‘s0’, ‘ifds’, ‘m’, ‘c’, ‘k’] sent_split_sw) >>
        impl_tac >- simp[] >> strip_tac >> asm_rewrite_tac[IS_PREFIX_APPEND3]) >>
  ‘P_b.parse "" ≠ PInvalid’ by (simp[P_b_def] >> EVAL_TAC) >>
  qspecl_then [‘SKV’, ‘P_b’, ‘λreq. SOME (fd, req)’, ‘kfin’, ‘fd’, ‘g’, ‘n − a’, ‘D’, ‘n − a’]
    mp_tac (Q.GENL [‘V’, ‘P’, ‘ansq’, ‘fin’, ‘fd’, ‘g’, ‘j0’, ‘D’, ‘j’] q_read_grow_valid) >>
  impl_tac
  >- (simp[proto_ok_b, vocab_ok_sockV, vocab_qok_sockV] >> fs[Abbr ‘qm’, Abbr ‘B’]) >>
  strip_tac >>
  ‘LENGTH (pread_all c (SPg KVM ifds s0 n)) < LENGTH (pread_all c (SPg KVM ifds s0 (a + j')))’
    by (‘j' ≤ LENGTH g’ by fs[Abbr ‘B’] >>
        metis_tac[LENGTH_bytes_sw]) >>
  ‘n ≤ a + j'’ by simp[] >>
  ‘∃r. n ≤ r ∧ r < a + j' ∧ reads_c c (SAg KVM ifds s0 r)’
    by (irule pread_grow_reads >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  qexists_tac ‘r − n’ >> ‘n + (r − n) = r’ by simp[] >> simp[]
QED

(* MAIN: kv_read_soon_m on the live interest list (D26) *)
Theorem kv_read_soon_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧ sched_wf s0 ∧
  MEM c (wacc (SPg KVM (LVg KVM lfdn) s0 n)) ∧
  ALOOKUP (gstate (LVg KVM lfdn) (srelabel KVM) s0 n).conns c = SOME cn ∧ cn.incoming ≠ [] ∧
  (∀k. ∃rqs. EVERY valid_brequest rqs ∧
             sent_upto c k s0 ≼ HttpSpec$bytes (FLAT (MAP print_brequest rqs))) ⇒
  ∃i. reads_c c (SAg KVM (LVg KVM lfdn) s0 (n + i))
Proof
  strip_tac >>
  ‘grun_ok (LVg KVM lfdn) (srelabel KVM) s0’
    by (irule gen_grun_ok >> simp[] >> qexists_tac ‘lfdn’ >> fs[kv_server_uses_ok]) >>
  irule kv_read_soon_m >> simp[] >>
  irule interest_covers_e_live >> first_assum ACCEPT_TAC
QED
