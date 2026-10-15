(*
  The HTTP handler answers every complete request it receives, as a fact
  about the state machine (asyncHttpMachine) given four facts about its
  environment.

  hmachine_live: let D be data that has arrived on the connection (by the
  start of round j0), and K the number of complete requests at its front.
  If
   - D extends what the handler has read by round j0;
   - whenever the handler waits with an incomplete buffer and fd is not
     reported readable, it has already read all of D;
   - whenever it reads, it then has read all of D;
   - whenever it stops at end-of-file, it has read all of D;
  then within 2K + 2 rounds it has written the responses to all K
  requests.  The closed loop (asyncHttpLiveness) provides these four facts.

  The rounds: answer the complete requests already buffered (at most K
  rounds, one response each), wait one round for readiness, read (one
  round for the response), then answer the rest (at most K rounds).
*)
Theory asyncHttpDrain
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncCfActModel asyncProgress HttpSpec asyncHttpParse
  asyncHttpServer asyncHttpMachine
Libs
  BasicProvers

(* The handler of fd, started with an empty buffer, on history g: its state,
   what it has read, and what it has written, after the first j snapshots *)
Overload Sj = “λfiles fd g j. hrun files fd (HA "") (TAKE j g)”
Overload Rj = “λfiles fd g j.
  CONCAT (read fd (trans (hcomp files fd (HA "")) (TAKE j g)))”
Overload Wj = “λfiles fd g j. written fd (trans (hcomp files fd (HA "")) (TAKE j g))”

(* ------------------------------------------------------------------------
   Parsing facts
   ------------------------------------------------------------------------ *)

Theorem parse_all_prefix:
  ∀s t. s ≼ t ⇒ parse_all s ≼ parse_all t
Proof
  gen_tac >> measureInduct_on ‘LENGTH s’ >> rw[] >>
  simp[Once parse_all_def] >> CASE_TAC >> simp[] >>
  rename1 ‘Complete r rest’ >> fs[IS_PREFIX_APPEND] >>
  drule_then (qspec_then ‘l’ assume_tac) parse_extend >>
  drule parse_all_Complete >> simp[] >> disch_then kall_tac >>
  imp_res_tac parse_complete_shorter >>
  first_x_assum (qspec_then ‘rest’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘rest ++ l’ mp_tac) >> simp[IS_PREFIX_APPEND]
QED

Theorem parse_all_not_complete:
  (∀r rest. parse_request b ≠ Complete r rest) ⇒ parse_all b = []
Proof
  simp[Once parse_all_def] >> CASE_TAC >> simp[]
QED

Theorem parse_all_invalid_ext:
  parse_request b = Invalid ⇒ parse_all (b ++ x) = []
Proof
  strip_tac >> irule parse_all_not_complete >> rpt strip_tac >>
  drule parse_complete >> strip_tac >>
  drule parse_invalid >> disch_then (qspecl_then [‘x’, ‘r’, ‘rest’] mp_tac) >>
  simp[]
QED

(* Two prefixes of the same list: the shorter is a prefix of the longer *)
Theorem prefix_common:
  ∀l1 l2 l3. l1 ≼ l3 ∧ l2 ≼ l3 ∧ LENGTH l1 ≤ LENGTH l2 ⇒ l1 ≼ l2
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘l2’ >> Cases_on ‘l3’ >> simp[] >>
  rw[] >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The machine, round by round
   ------------------------------------------------------------------------ *)

Theorem Sj_SUC:
  j < LENGTH g ⇒ Sj files fd g (SUC j) = hstep files fd (Sj files fd g j) (EL j g)
Proof
  strip_tac >> simp[GSYM SNOC_EL_TAKE, SNOC_APPEND, hrun_SNOC]
QED

Theorem Rj_Wj_SUC:
  prompt (hcomp files fd (HA "")) g ∧ j < LENGTH g ⇒
  Wj files fd g (SUC j) = Wj files fd g j ++ hpend files (Sj files fd g (SUC j)) ∧
  ((∀b. Sj files fd g j ≠ HB b) ⇒ Rj files fd g (SUC j) = Rj files fd g j)
Proof
  strip_tac >> drule_all hmachine_trans_SUC >> simp[] >> strip_tac >>
  simp[written_zipr] >> rpt strip_tac >>
  Cases_on ‘hrun files fd (HA "") (TAKE j g)’ >> gvs[hacts_def, hpend_def] >>
  TRY (CASE_TAC >> simp[]) >>
  qspec_tac (‘(EL j g).results’, ‘rs’) >> Cases >> simp[zipr_def]
QED

Theorem Wj_mono:
  prompt (hcomp files fd (HA "")) g ⇒
  ∀k j. j + k ≤ LENGTH g ⇒ Wj files fd g j ≼ Wj files fd g (j + k)
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >>
  drule_then (qspec_then ‘j + k’ mp_tac) Rj_Wj_SUC >> simp[ADD_CLAUSES] >>
  metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS, APPEND_ASSOC]
QED

(* What the handler has written is a prefix of the responses to what it
   has read *)
Theorem Wj_responses:
  prompt (hcomp files fd (HA "")) g ∧ j ≤ LENGTH g ⇒
  Wj files fd g j ≼ responses_to files (Rj files fd g j)
Proof
  strip_tac >> drule_then (qspec_then ‘j’ mp_tac) hmachine_inv >> simp[] >>
  strip_tac >> simp[parse_all_print] >>
  Cases_on ‘hrun files fd (HA "") (TAKE j g)’ >> simp[hbuf_def, hpend_def] >>
  CASE_TAC >> simp[] >> drule parse_all_Complete >> simp[]
QED

(* Answering buffered requests: in state HA b, the next k ≤ (number of
   complete requests in b) rounds each answer one of them *)
Theorem hdrain:
  prompt (hcomp files fd (HA "")) g ⇒
  ∀k j b. Sj files fd g j = HA b ∧ k ≤ LENGTH (parse_all b) ∧ j + k ≤ LENGTH g ⇒
          ∃rq b'. Sj files fd g (j + k) = HA b' ∧ LENGTH rq = k ∧
                  parse_all b = rq ++ parse_all b' ∧
                  Rj files fd g (j + k) = Rj files fd g j
Proof
  strip_tac >> Induct >- (rw[] >> qexists_tac ‘[]’ >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  ‘parse_all b' ≠ []’ by (strip_tac >> gvs[]) >>
  ‘∃r rest. parse_request b' = Complete r rest’
    by (qpat_x_assum ‘parse_all b' ≠ []’ mp_tac >> simp[Once parse_all_def] >>
        CASE_TAC >> simp[]) >>
  drule parse_all_Complete >> strip_tac >>
  ‘j + k < LENGTH g’ by simp[] >>
  ‘Sj files fd g (SUC (j + k)) = hstep files fd (Sj files fd g (j + k)) (EL (j + k) g)’
    by (irule Sj_SUC >> simp[]) >>
  gvs[ADD_CLAUSES, hstep_def] >>
  TRY (qexistsl [‘rq ++ [r]’, ‘rest’] >> gvs[]) >>
  drule_then (qspec_then ‘j + LENGTH rq’ mp_tac) Rj_Wj_SUC >> simp[]
QED

(* ------------------------------------------------------------------------
   Liveness of the machine
   ------------------------------------------------------------------------ *)

Theorem responses_to_prefix:
  s ≼ t ⇒ responses_to files s ≼ responses_to files t
Proof
  strip_tac >> drule parse_all_prefix >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* If what the handler has written at round j contains as many responses as
   there are complete requests in D, and D extends no further than what it
   has read, then it has written the responses to D *)
Theorem responses_by_length:
  prompt (hcomp files fd (HA "")) g ∧ j ≤ LENGTH g ∧
  D ≼ Rj files fd g j ∧ LENGTH (parse_all D) ≤ LENGTH (Wj files fd g j) ⇒
  responses_to files D ≼ Wj files fd g j
Proof
  strip_tac >>
  ‘responses_to files D ≼ responses_to files (Rj files fd g j)’
    by simp[responses_to_prefix] >>
  ‘Wj files fd g j ≼ responses_to files (Rj files fd g j)’ by simp[Wj_responses] >>
  metis_tac[prefix_common, LENGTH_MAP]
QED

(* After a read: within NK rounds, the responses to D are written *)
Theorem drain_after:
  prompt (hcomp files fd (HA "")) g ∧ j2 + LENGTH (parse_all D) ≤ LENGTH g ∧
  D ≼ Rj files fd g j2 ∧ (∀b. Sj files fd g j2 ≠ HB b) ⇒
  ∃j. j2 ≤ j ∧ j ≤ j2 + LENGTH (parse_all D) ∧ responses_to files D ≼ Wj files fd g j
Proof
  strip_tac >> qabbrev_tac ‘NK = LENGTH (parse_all D)’ >>
  drule_then (qspec_then ‘j2’ mp_tac) hmachine_inv >> simp[] >> strip_tac >>
  ‘parse_all D ≼ rs ++ parse_all (hbuf (Sj files fd g j2))’
    by metis_tac[parse_all_prefix, parse_all_print] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  Cases_on ‘NK ≤ LENGTH rs’
  >- (qexists_tac ‘j2’ >> simp[] >>
      qpat_assum ‘written _ _ = _’ (SUBST1_TAC o SYM) >>
      irule responses_by_length >> simp[] >>
      qpat_x_assum ‘written _ _ = _’ (fn th => REWRITE_TAC[th]) >> simp[])
  >> Cases_on ‘Sj files fd g j2’ >> gvs[hbuf_def]
  >- (rename1 ‘hrun files fd (HA "") (TAKE j2 g) = HA b’ >>
      drule_then (qspecl_then [‘NK − LENGTH rs’, ‘j2’, ‘b’] mp_tac) hdrain >>
      simp[] >> strip_tac >>
      qexists_tac ‘j2 + (NK − LENGTH rs)’ >> simp[] >>
      irule responses_by_length >> simp[] >>
      drule_then (qspec_then ‘j2 + (NK − LENGTH rs)’ mp_tac) hmachine_inv >>
      simp[] >> strip_tac >> gvs[hbuf_def] >>
      ‘rs' ++ parse_all b' = rs ++ rq ++ parse_all b'’
        by metis_tac[parse_all_print, APPEND_ASSOC] >>
      gvs[])
  >> rename1 ‘hrun files fd (HA "") (TAKE j2 g) = HD b’ >>
  ‘parse_all b = []’ by (irule parse_all_not_complete >> metis_tac[]) >>
  gvs[]
QED

(* If D is no longer than what has been read, its responses are among
   those to the requests read so far *)
Theorem responses_upto:
  EVERY valid_request rs ∧ D ≼ FLAT (MAP print_request rs) ++ b ⇒
  responses_to files D ≼
    MAP (print_response o handle files) rs ++ responses_to files b ++ p
Proof
  strip_tac >> drule_then (qspec_then ‘files’ assume_tac) responses_to_prefix >>
  gs[parse_all_print] >> irule IS_PREFIX_TRANS >>
  first_assum (irule_at Any) >> simp[IS_PREFIX_APPEND]
QED

(* An invalid request ends what can be answered: the responses to any D
   extending it are those to the requests before it *)
Theorem responses_invalid:
  EVERY valid_request rs ∧ parse_request b = Invalid ∧
  FLAT (MAP print_request rs) ++ b ≼ D ⇒
  responses_to files D = MAP (print_response o handle files) rs
Proof
  rw[IS_PREFIX_APPEND] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
  drule_then (fn th => REWRITE_TAC[th]) parse_all_print >>
  drule_then (fn th => REWRITE_TAC[th]) parse_all_invalid_ext >> simp[]
QED

(* After a read at round j1 (state HB) that leaves all of D read, the
   responses to D are written within 1 + K rounds *)
Theorem after_read_live:
  prompt (hcomp files fd (HA "")) g ∧ j1 + 2 + LENGTH (parse_all D) ≤ LENGTH g ∧
  Sj files fd g j1 = HB b1 ∧ D ≼ Rj files fd g (SUC j1) ⇒
  ∃j. j ≤ j1 + 1 + LENGTH (parse_all D) ∧ responses_to files D ≼ Wj files fd g j
Proof
  strip_tac >>
  ‘∀b. Sj files fd g (SUC j1) ≠ HB b’
    by (‘j1 < LENGTH g’ by simp[] >>
        drule_then (qspecl_then [‘files’, ‘fd’] SUBST1_TAC) Sj_SUC >>
        pop_assum kall_tac >> asm_rewrite_tac[] >>
        simp[hstep_def] >> every_case_tac >> simp[]) >>
  drule_then (qspecl_then [‘SUC j1’, ‘D’] mp_tac) drain_after >>
  simp[] >> strip_tac >> qexists_tac ‘j’ >> simp[]
QED

(* MAIN: the machine answers every complete request in D within 2K + 2
   rounds of round j0, given the four environment facts (see the header) *)
Theorem hmachine_live:
  prompt (hcomp files fd (HA "")) g ∧
  j0 + 2 * LENGTH (parse_all D) + 2 ≤ LENGTH g ∧
  Rj files fd g j0 ≼ D ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sj files fd g j = HA b ∧
         parse_request b = Incomplete ∧ Readable fd ∉ (EL j g).ready ⇒
         D ≼ Rj files fd g j) ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sj files fd g j = HB b ⇒
         D ≼ Rj files fd g (SUC j)) ∧
  (∀j b. j0 ≤ j ∧ j ≤ LENGTH g ∧ Sj files fd g j = HD b ∧
         parse_request b = Incomplete ⇒ D ≼ Rj files fd g j) ⇒
  ∃j. j ≤ j0 + 2 * LENGTH (parse_all D) + 2 ∧
      responses_to files D ≼ Wj files fd g j
Proof
  strip_tac >> qabbrev_tac ‘NK = LENGTH (parse_all D)’ >>
  drule_then (qspec_then ‘j0’ mp_tac) hmachine_inv >> simp[] >> strip_tac >>
  (* the requests completed by round j0 are among D's *)
  ‘rs ++ parse_all (hbuf (Sj files fd g j0)) ≼ parse_all D’
    by (‘parse_all (Rj files fd g j0) ≼ parse_all D’ by simp[parse_all_prefix] >>
        gvs[parse_all_print]) >>
  imp_res_tac IS_PREFIX_LENGTH >> gvs[] >>
  (* after a read at round j1 (state HB), drain_after finishes *)
  ‘∀j1 b1. j0 ≤ j1 ∧ j1 + 2 + NK ≤ LENGTH g ∧ Sj files fd g j1 = HB b1 ⇒
           ∃j. j ≤ j1 + 1 + NK ∧ responses_to files D ≼ Wj files fd g j’
    by (rpt strip_tac >>
        ‘D ≼ Rj files fd g (SUC j1)’
          by (qpat_x_assum ‘∀j b. _ ∧ _ ∧ Sj _ _ _ _ = HB _ ⇒ _’
                (qspecl_then [‘j1’, ‘b1’] mp_tac) >> simp[]) >>
        ‘j1 + 2 + LENGTH (parse_all D) ≤ LENGTH g’ by fs[Abbr ‘NK’] >>
        drule_all after_read_live >> strip_tac >>
        qexists_tac ‘j’ >> fs[Abbr ‘NK’]) >>
  Cases_on ‘Sj files fd g j0’ >> gvs[hbuf_def]
  (* waiting or answering, with buffer b *)
  >- (rename1 ‘hrun files fd (HA "") (TAKE j0 g) = HA b’ >>
      drule_then (qspecl_then [‘LENGTH (parse_all b)’, ‘j0’, ‘b’] mp_tac) hdrain >>
      simp[] >> strip_tac >>
      qabbrev_tac ‘j1 = j0 + LENGTH (parse_all b)’ >>
      ‘parse_all b' = []’
        by (qpat_x_assum ‘parse_all b = _’ (fn th =>
              qpat_x_assum ‘LENGTH rq = _’ (mp_tac o REWRITE_RULE [th])) >>
            simp[]) >>
      (* LENGTH rq = LENGTH (parse_all b) would make the simplifier loop *)
      qpat_x_assum ‘LENGTH rq = _’ kall_tac >>
      drule_then (qspec_then ‘j1’ mp_tac) hmachine_inv >>
      impl_tac >- fs[Abbr ‘j1’] >>
      qpat_x_assum ‘Sj _ _ _ j1 = _’ (fn th => simp[th, hbuf_def] >> assume_tac th) >>
      strip_tac >>
      ‘∀r rest. parse_request b' ≠ Complete r rest’
        by (rpt strip_tac >> drule parse_all_Complete >> simp[]) >>
      ‘FLAT (MAP print_request rs') ++ b' = FLAT (MAP print_request rs) ++ b’
        by metis_tac[] >>
      ‘rs' = rs ++ rq’
        by (qpat_x_assum ‘FLAT _ ++ b' = _’ (mp_tac o AP_TERM “parse_all”) >>
            qpat_x_assum ‘EVERY _ rs'’ (fn th1 => qpat_x_assum ‘EVERY _ rs’ (fn th2 =>
              simp[th1, th2, parse_all_print] >> assume_tac th1 >> assume_tac th2)) >>
            qpat_x_assum ‘parse_all b = _’ (fn th1 => qpat_x_assum ‘parse_all b' = _’
              (fn th2 => simp[th1, th2]))) >>
      pop_assum SUBST_ALL_TAC >>
      qpat_x_assum ‘STRCAT (CONCAT (MAP _ (_ ++ _))) b' = _’ kall_tac >>
      Cases_on ‘parse_request b'’ >> gvs[]
      (* incomplete: either fd is not readable (all of D read), or a read *)
      >- (Cases_on ‘Readable fd ∈ (EL j1 g).ready’
          >- (‘Sj files fd g (SUC j1) = HB b'’ by simp[Sj_SUC, hstep_def, Abbr ‘j1’] >>
              Cases_on ‘LENGTH (parse_all b) < NK’
              (* a read now, then drain_after *)
              >- (qpat_x_assum ‘∀j1 b1. _ ⇒ ∃j. _’ (qspecl_then [‘SUC j1’, ‘b'’] mp_tac) >>
                  impl_tac >- fs[Abbr ‘j1’] >> strip_tac >>
                  qexists_tac ‘j’ >> fs[Abbr ‘j1’])
              (* D's requests were all in hand at round j0: answered by j1 *)
              >> ‘rs ++ parse_all b = parse_all D’
                   by (irule (iffLR IS_PREFIX_LENGTH_ANTI) >> fs[Abbr ‘NK’]) >>
              qexists_tac ‘j1’ >> conj_tac >- fs[Abbr ‘j1’] >>
              qpat_x_assum ‘Wj _ _ _ j1 = _’ SUBST1_TAC >>
              qpat_x_assum ‘_ = parse_all D’ (SUBST1_TAC o SYM) >> simp[])
          >> ‘D ≼ Rj files fd g j1’
               by (qpat_x_assum ‘∀j b. _ ∧ _ ∧ _ = HA _ ∧ _ ⇒ _’
                     (qspecl_then [‘j1’, ‘b'’] mp_tac) >>
                   impl_tac >- fs[Abbr ‘j1’] >> simp[]) >>
          qexists_tac ‘j1’ >> simp[Abbr ‘j1’] >>
          irule responses_upto >> fs[] >>
          qpat_x_assum ‘Rj _ _ _ (_ + _) = _’ (fn th =>
            qpat_x_assum ‘D ≼ _’ (mp_tac o REWRITE_RULE [th])) >>
          qpat_x_assum ‘b = _’ (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
          simp[])
      (* invalid: D's requests are exactly those already answered *)
      >> qexists_tac ‘j1’ >> conj_tac >- fs[Abbr ‘j1’] >>
      ‘responses_to files D = MAP (print_response o handle files) (rs ++ parse_all b)’
        by (irule responses_invalid >> conj_tac >- fs[] >> qexists_tac ‘b'’ >> fs[]) >>
      qpat_x_assum ‘Wj _ _ _ j1 = _’ SUBST1_TAC >> pop_assum SUBST1_TAC >> simp[])
  (* reading this round *)
  >- (first_x_assum (qspecl_then [‘j0’, ‘s’] mp_tac) >> simp[] >>
      strip_tac >> qexists_tac ‘j’ >> simp[])
  (* stopped *)
  >> rename1 ‘hrun files fd (HA "") (TAKE j0 g) = HD b’ >>
  Cases_on ‘parse_request b’ >> gvs[]
  >- (‘D ≼ Rj files fd g j0’ by (first_x_assum irule >> simp[]) >>
      qexists_tac ‘j0’ >> simp[] >>
      ‘parse_all b = []’ by (irule parse_all_not_complete >> fs[]) >>
      ‘responses_to files D ≼
         MAP (print_response o handle files) rs ++ responses_to files b ++
         hpend files (HD b)’ by (irule responses_upto >> simp[] >>
             qpat_x_assum ‘D ≼ _’ mp_tac >>
             qpat_x_assum ‘Rj _ _ _ _ = _’ (fn th => REWRITE_TAC [th])) >>
      gs[])
  >> qexists_tac ‘j0’ >> simp[] >>
  ‘responses_to files D = MAP (print_response o handle files) rs’
    by (irule responses_invalid >> fs[] >> metis_tac[]) >>
  simp[]
QED

(* What the handler has read only grows *)
Theorem Rj_SUC_prefix:
  prompt (hcomp files fd (HA "")) g ∧ j < LENGTH g ⇒
  Rj files fd g j ≼ Rj files fd g (SUC j)
Proof
  strip_tac >> drule_all hmachine_trans_SUC >> simp[] >> strip_tac >> simp[]
QED

(* If the handler has already read all of D by round j0, it answers D's
   requests within K + 1 rounds: it finishes a read in progress, then
   answers the buffered requests *)
Theorem hmachine_live_read:
  prompt (hcomp files fd (HA "")) g ∧
  j0 + LENGTH (parse_all D) + 2 ≤ LENGTH g ∧ D ≼ Rj files fd g j0 ⇒
  ∃j. j ≤ j0 + LENGTH (parse_all D) + 1 ∧
      responses_to files D ≼ Wj files fd g j
Proof
  strip_tac >> Cases_on ‘∃b. Sj files fd g j0 = HB b’
  >- (fs[] >>
      ‘D ≼ Rj files fd g (SUC j0)’
        by (‘j0 < LENGTH g’ by fs[] >> drule_all Rj_SUC_prefix >>
            metis_tac[IS_PREFIX_TRANS]) >>
      mp_tac (Q.INST [‘j1’ |-> ‘j0’, ‘b1’ |-> ‘b’] after_read_live) >>
      impl_tac >- fs[] >> strip_tac >> qexists_tac ‘j’ >> fs[])
  >> ‘∀b. Sj files fd g j0 ≠ HB b’ by metis_tac[] >>
  mp_tac (Q.INST [‘j2’ |-> ‘j0’] drain_after) >>
  impl_tac >- fs[] >> strip_tac >> qexists_tac ‘j’ >> fs[]
QED
