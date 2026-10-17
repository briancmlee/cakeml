(*
  The query handler (proto_handler_v, so KV's handler) keeps reading: given
  henv's four environment facts for data D (asyncProtoDrainV's
  qmachine_live_p_v hypotheses, on the handler's transcript), if D has not
  all been read by round j, then within 2K + 4 rounds (K the number of
  complete requests in D) the handler has read more, or it has stopped on
  an invalid buffer.  The step lemmas are qmachine_live_p_v's cases:
  drain the buffered requests (qdrain), then wait for readiness and read.

  MAIN: q_read_grow.
*)
Theory honestKvReadQ
Ancestors
  asyncProtoDrainV asyncProtoMachineV asyncProto asyncProtoV asyncServerV
  asyncServerVLive asyncTranscript asyncLevel1 asyncCore
Libs
  preamble

(* The handler's state, transcript and reads (asyncProtoDrainV's overloads) *)
Overload Sq = “λV P ansq fin fd g j. qrun V P ansq fin fd (QA "") (TAKE j g)”
Overload Tq = “λV P ansq fin fd g j.
  trans (qcomp V P ansq fin fd (QA "")) (TAKE j g)”
Overload Rq = “λV P ansq fin fd g j.
  CONCAT (read fd (sproj V (trans (qcomp V P ansq fin fd (QA "")) (TAKE j g))))”

(* henv's four facts (henv_t), from round j0, for D *)
Definition qenv_def:
  qenv V P ansq fin fd g j0 D ⇔
    (∀j. j0 ≤ j ∧ j ≤ LENGTH g ⇒
         Rq V P ansq fin fd g j ≼ D ∨ D ≼ Rq V P ansq fin fd g j) ∧
    (∀j. j0 ≤ j ∧ j < LENGTH g ∧ Readable fd ∉ (EL j g).ready ⇒
         D ≼ Rq V P ansq fin fd g (SUC j)) ∧
    (∀j. j0 ≤ j ∧ j < LENGTH g ∧ MEM (Read fd, NONE) (sproj V (Tq V P ansq fin fd g j)) ∧
         ¬(D ≼ Rq V P ansq fin fd g j) ⇒
         D ≼ Rq V P ansq fin fd g (SUC j) ∨
         LENGTH (Rq V P ansq fin fd g j) < LENGTH (Rq V P ansq fin fd g (SUC j))) ∧
    (∀j. j0 ≤ j ∧ j ≤ LENGTH g ∧ MEM (Read fd, SOME Eof) (sproj V (Tq V P ansq fin fd g j)) ⇒
         D ≼ Rq V P ansq fin fd g j)
End

(* henv_t for the handler's socket transcript is qenv *)
Theorem henv_t_qenv:
  henv_t fd (λq. sproj V (trans (qcomp V P ansq fin fd (QA "")) q)) g j0 D ⇔
  qenv V P ansq fin fd g j0 D
Proof
  simp[henv_t_def, hread_t_def, qenv_def]
QED

Theorem prefix_strict_len[local]:
  r ≼ (d : 'a list) ∧ ¬(d ≼ r) ⇒ LENGTH r < LENGTH d
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[NOT_LESS] >>
  ‘LENGTH r = LENGTH d’ by (imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
  metis_tac[IS_PREFIX_LENGTH_ANTI, IS_PREFIX_REFL]
QED

(* What has been read is a prefix of D, while D is not all read *)
Theorem qenv_cmp[local]:
  qenv V P ansq fin fd g j0 D ∧ j0 ≤ j ∧ j ≤ LENGTH g ∧ ¬(D ≼ Rq V P ansq fin fd g j) ⇒
  Rq V P ansq fin fd g j ≼ D
Proof
  rw[qenv_def] >> metis_tac[]
QED

(* A read outstanding (state QB) at j1, D not all read: more is read by
   round SUC j1 *)
Theorem q_read_B[local]:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧ prompt (qcomp V P ansq fin fd (QA "")) g ∧
  qenv V P ansq fin fd g j0 D ∧ j0 ≤ j1 ∧ j1 < LENGTH g ∧
  Sq V P ansq fin fd g j1 = QB b ∧ ¬(D ≼ Rq V P ansq fin fd g j1) ⇒
  LENGTH (Rq V P ansq fin fd g j1) < LENGTH (Rq V P ansq fin fd g (SUC j1))
Proof
  strip_tac >>
  ‘MEM (Read fd, NONE) (sproj V (Tq V P ansq fin fd g j1))’
    by (irule qmachine_reading >> simp[] >> qexists_tac ‘b’ >> simp[]) >>
  ‘Rq V P ansq fin fd g j1 ≼ D’
    by (irule qenv_cmp >> simp[] >> qexists_tac ‘j0’ >> simp[]) >>
  qpat_x_assum ‘qenv _ _ _ _ _ _ _ _’ mp_tac >> simp[qenv_def] >> strip_tac >>
  qpat_x_assum ‘∀j. j0 ≤ j ∧ j < LENGTH g ∧ MEM (Read fd, NONE) _ ∧ _ ⇒ _’
    (qspec_then ‘j1’ mp_tac) >> simp[] >> strip_tac >> simp[] >>
  ‘LENGTH (Rq V P ansq fin fd g j1) < LENGTH D’ by metis_tac[prefix_strict_len] >>
  imp_res_tac IS_PREFIX_LENGTH >> simp[]
QED

(* The complete requests buffered at j1 are among D's *)
Theorem q_buf_bound[local]:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧ prompt (qcomp V P ansq fin fd (QA "")) g ∧
  j1 ≤ LENGTH g ∧ Rq V P ansq fin fd g j1 ≼ D ⇒
  LENGTH (proto_all P (qbuf P (Sq V P ansq fin fd g j1))) ≤ LENGTH (proto_all P D)
Proof
  strip_tac >>
  ‘∃rs ks. EVERY P.valid rs ∧
           Rq V P ansq fin fd g j1 = FLAT (MAP P.print rs) ++ qbuf P (Sq V P ansq fin fd g j1)’
    by (qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
        qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
        qpat_assum ‘j1 ≤ LENGTH g’ (fn t5 =>
          strip_assume_tac (MATCH_MP qinv0 (CONJ (LIST_CONJ [t1, t2, t3, t4]) t5))))))) >>
        metis_tac[]) >>
  ‘proto_all P (Rq V P ansq fin fd g j1) ≼ proto_all P D’
    by (irule proto_all_prefix >> simp[]) >>
  ‘proto_all P (Rq V P ansq fin fd g j1) =
   rs ++ proto_all P (qbuf P (Sq V P ansq fin fd g j1))’
    by (qpat_x_assum ‘Rq _ _ _ _ _ _ _ = _’ SUBST1_TAC >> irule proto_all_print >> simp[]) >>
  qpat_x_assum ‘proto_all P _ ≼ proto_all P D’ mp_tac >>
  qpat_x_assum ‘proto_all P _ = _’ SUBST1_TAC >> strip_tac >>
  drule IS_PREFIX_LENGTH >> simp[]
QED

(* State QA b at j1, nothing new read since j: within 2K + 2 rounds more is
   read, or the handler stops on an invalid buffer *)
Theorem q_read_A[local]:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧ prompt (qcomp V P ansq fin fd (QA "")) g ∧
  qenv V P ansq fin fd g j0 D ∧ j0 ≤ j1 ∧
  Sq V P ansq fin fd g j1 = QA b ∧ ¬(D ≼ Rq V P ansq fin fd g j1) ∧
  j1 + 2 * LENGTH (proto_all P D) + 2 ≤ LENGTH g ⇒
  ∃j'. j1 ≤ j' ∧ j' ≤ j1 + 2 * LENGTH (proto_all P D) + 2 ∧
       (LENGTH (Rq V P ansq fin fd g j1) < LENGTH (Rq V P ansq fin fd g j') ∨
        ∃b'. Sq V P ansq fin fd g j' = QD b' ∧ P.parse b' = PInvalid)
Proof
  strip_tac >>
  ‘Rq V P ansq fin fd g j1 ≼ D’
    by (irule qenv_cmp >> simp[] >> qexists_tac ‘j0’ >> simp[]) >>
  ‘LENGTH (proto_all P b) ≤ LENGTH (proto_all P D)’
    by (‘LENGTH (proto_all P (qbuf P (Sq V P ansq fin fd g j1))) ≤ LENGTH (proto_all P D)’
          suffices_by simp[qbuf_def] >>
        irule q_buf_bound >> simp[]) >>
  (* drain the buffered requests *)
  qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
    qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
      mp_tac (MATCH_MP qdrain (LIST_CONJ [t1, t2, t3, t4])))))) >>
  disch_then (qspecl_then [‘LENGTH (proto_all P b)’, ‘j1’, ‘b’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘proto_all P b' = []’
    by (qpat_x_assum ‘proto_all P b = _’ (mp_tac o Q.AP_TERM ‘LENGTH’) >>
        simp[] >> strip_tac >> fs[LENGTH_NIL]) >>
  ‘∀r rest. P.parse b' ≠ PComplete r rest’
    by (rpt strip_tac >> drule_all proto_all_complete >> simp[]) >>
  ‘j' < LENGTH g’ by simp[] >>
  ‘Sq V P ansq fin fd g (SUC j') =
   qstep V P ansq fin fd (Sq V P ansq fin fd g j') (EL j' g)’
    by (irule Sq_SUC >> simp[]) >>
  ‘Rq V P ansq fin fd g (SUC j') = Rq V P ansq fin fd g j'’
    by (qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
        qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
        qpat_assum ‘j' < LENGTH g’ (fn t5 =>
          mp_tac (MATCH_MP Rq_Wq_SUC (CONJ (LIST_CONJ [t1, t2, t3, t4]) t5))))))) >>
        simp[]) >>
  ‘Rq V P ansq fin fd g (SUC j') = Rq V P ansq fin fd g j1’
    by (qpat_x_assum ‘Rq _ _ _ _ _ _ (SUC j') = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  ‘P.parse b' = PIncomplete ∨ P.parse b' = PInvalid’
    by (Cases_on ‘P.parse b'’ >> simp[] >> rename1 ‘PComplete r0 rest0’ >>
        qpat_x_assum ‘∀r rest. _’ (qspecl_then [‘r0’, ‘rest0’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘Sq _ _ _ _ _ _ (SUC j') = _’ mp_tac >>
  qpat_x_assum ‘Sq _ _ _ _ _ _ j' = _’ (fn th => REWRITE_TAC[th]) >>
  pop_assum strip_assume_tac
  (* incomplete: wait for readiness, then read *)
  >- (Cases_on ‘Readable fd ∈ (EL j' g).ready’
      >- (qpat_assum ‘P.parse b' = _’ (fn th => qpat_assum ‘Readable _ ∈ _’ (fn th2 =>
            simp[qstep_def, th, th2])) >> strip_tac >>
          qexists_tac ‘SUC (SUC j')’ >> simp[] >> disj1_tac >>
          ‘LENGTH (Rq V P ansq fin fd g (SUC j')) <
           LENGTH (Rq V P ansq fin fd g (SUC (SUC j')))’
            suffices_by (qpat_x_assum ‘Rq _ _ _ _ _ _ (SUC j') = _’ SUBST1_TAC >> simp[]) >>
          irule q_read_B >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (simp[] >> NO_TAC) >>
          TRY (qexists_tac ‘b'’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
          qexistsl_tac [‘D’, ‘j0’] >>
          qpat_x_assum ‘Rq _ _ _ _ _ _ (SUC j') = Rq _ _ _ _ _ _ j1’ SUBST1_TAC >>
          rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC]) >>
      (* not readable: D was all read, but nothing new was *)
      strip_tac >>
      qpat_x_assum ‘qenv _ _ _ _ _ _ _ _’ mp_tac >> simp[qenv_def] >> strip_tac >>
      qpat_x_assum ‘∀j. j0 ≤ j ∧ j < LENGTH g ∧ Readable fd ∉ _ ⇒ _’
        (qspec_then ‘j'’ mp_tac) >> simp[])
  (* invalid: the handler stops *)
  >> qpat_assum ‘P.parse b' = _’ (fn th => simp[qstep_def, th]) >> strip_tac >>
  qexists_tac ‘SUC j'’ >> simp[]
QED

(* MAIN: if D has not all been read by round j, within 2K + 4 rounds the
   handler has read more, or stopped on an invalid buffer *)
Theorem q_read_grow:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧ prompt (qcomp V P ansq fin fd (QA "")) g ∧
  qenv V P ansq fin fd g j0 D ∧ j0 ≤ j ∧ ¬(D ≼ Rq V P ansq fin fd g j) ∧
  j + 2 * LENGTH (proto_all P D) + 4 ≤ LENGTH g ⇒
  ∃j'. j ≤ j' ∧ j' ≤ j + 2 * LENGTH (proto_all P D) + 4 ∧
       (LENGTH (Rq V P ansq fin fd g j) < LENGTH (Rq V P ansq fin fd g j') ∨
        ∃b. Sq V P ansq fin fd g j' = QD b ∧ P.parse b = PInvalid)
Proof
  strip_tac >> ‘j < LENGTH g’ by simp[] >>
  Cases_on ‘Sq V P ansq fin fd g j’
  (* QA *)
  >- (‘j + 2 * LENGTH (proto_all P D) + 2 ≤ LENGTH g’ by simp[] >>
      drule_all q_read_A >> strip_tac >> qexists_tac ‘j'’ >> simp[])
  (* QW: the write, then QA *)
  >- (rename1 ‘QW req rest k’ >>
      ‘Sq V P ansq fin fd g (SUC j) = QA rest’
        by (‘Sq V P ansq fin fd g (SUC j) =
             qstep V P ansq fin fd (Sq V P ansq fin fd g j) (EL j g)’
              by (irule Sq_SUC >> simp[]) >>
            gvs[qstep_def]) >>
      ‘Rq V P ansq fin fd g (SUC j) = Rq V P ansq fin fd g j’
        by (qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
            qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
            qpat_assum ‘j < LENGTH g’ (fn t5 =>
              mp_tac (MATCH_MP Rq_Wq_SUC (CONJ (LIST_CONJ [t1, t2, t3, t4]) t5))))))) >>
            simp[]) >>
      ‘¬(D ≼ Rq V P ansq fin fd g (SUC j))’
        by (qpat_x_assum ‘Rq _ _ _ _ _ _ (SUC j) = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      ‘j0 ≤ SUC j ∧ SUC j + 2 * LENGTH (proto_all P D) + 2 ≤ LENGTH g’ by simp[] >>
      drule_all q_read_A >> strip_tac >>
      qexists_tac ‘j'’ >> simp[] >>
      qpat_x_assum ‘Rq _ _ _ _ _ _ (SUC j) = _’ (fn th => fs[th]))
  (* QB: the read *)
  >- (qexists_tac ‘SUC j’ >> simp[] >> disj1_tac >>
      irule q_read_B >> simp[] >> metis_tac[])
  (* QD: invalid, or end-of-file was read (then D was all read) *)
  >> rename1 ‘QD b’ >>
  Cases_on ‘P.parse b = PInvalid’ >- (qexists_tac ‘j’ >> simp[]) >>
  ‘MEM (Read fd, SOME Eof) (sproj V (Tq V P ansq fin fd g j))’
    by (irule qmachine_eof >> simp[] >> qexists_tac ‘b’ >> simp[]) >>
  qpat_x_assum ‘qenv _ _ _ _ _ _ _ _’ mp_tac >> simp[qenv_def] >> strip_tac >>
  qpat_x_assum ‘∀j. j0 ≤ j ∧ j ≤ LENGTH g ∧ MEM (Read fd, SOME Eof) _ ⇒ _’
    (qspec_then ‘j’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Valid input never stops the handler
   ------------------------------------------------------------------------ *)

(* What is left after framing valid requests, of a prefix of printed valid
   requests, is not invalid *)
Theorem proto_valid_noinv:
  ∀rs rqs b.
    proto_ok P ∧ P.parse "" ≠ PInvalid ∧ EVERY P.valid rs ∧ EVERY P.valid rqs ∧
    FLAT (MAP P.print rs) ++ b ≼ FLAT (MAP P.print rqs) ⇒
    P.parse b ≠ PInvalid
Proof
  Induct
  >- (Cases_on ‘rqs’ >> simp[] >> rpt strip_tac >> fs[]
      >> TRY (gvs[] >> NO_TAC) >>
      rename1 ‘P.valid q’ >>
      ‘b ≼ P.print q ∨ P.print q ≼ b’
        by (irule prefixes_is_prefix_total >>
            qexists_tac ‘P.print q ++ FLAT (MAP P.print t)’ >> simp[]) >>
      fs[IS_PREFIX_APPEND]
      >- (qpat_x_assum ‘P.print q = _’ (strip_assume_tac o SYM) >>
          rename1 ‘b ++ u = P.print q’ >>
          Cases_on ‘u = []’
          >- (‘P.parse (P.print q ++ []) = PComplete q []’ by (irule proto_print >> simp[]) >> gvs[]) >>
          ‘P.parse b = PIncomplete’ by (irule proto_prefix >> simp[] >> qexistsl_tac [‘q’, ‘u’] >> simp[]) >>
          gvs[])
      >> qpat_x_assum ‘b = _’ SUBST_ALL_TAC >> rename1 ‘P.parse (P.print q ++ u)’ >>
      ‘P.parse (P.print q ++ u) = PComplete q u’ by (irule proto_print >> simp[]) >> gvs[]) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  Cases_on ‘rqs’
  >- (fs[] >> drule_all proto_nonempty >> strip_tac >> fs[]) >>
  rename1 ‘EVERY P.valid (q :: qs)’ >>
  fs[] >>
  ‘h = q ∧ FLAT (MAP P.print rs) ++ b ≼ FLAT (MAP P.print qs)’
    by (qpat_x_assum ‘_ ≼ _’ mp_tac >> simp[IS_PREFIX_APPEND] >> strip_tac >> fs[] >>
        qspecl_then [‘P’, ‘h’, ‘q’, ‘FLAT (MAP P.print rs) ++ b ++ l’, ‘FLAT (MAP P.print qs)’]
          mp_tac (Q.GENL [‘P’, ‘r1’, ‘r2’, ‘x’, ‘y’] proto_unique) >>
        impl_tac >- fs[] >> strip_tac >> simp[] >> qexists_tac ‘l’ >> simp[]) >>
  first_x_assum irule >> simp[] >> qexists_tac ‘qs’ >> simp[]
QED

(* So a handler stopped on an invalid buffer has read something that is no
   prefix of printed valid requests *)
Theorem q_invalid_read:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧ prompt (qcomp V P ansq fin fd (QA "")) g ∧
  P.parse "" ≠ PInvalid ∧ j ≤ LENGTH g ∧
  Sq V P ansq fin fd g j = QD b ∧ P.parse b = PInvalid ∧
  EVERY P.valid rqs ⇒
  ¬(Rq V P ansq fin fd g j ≼ FLAT (MAP P.print rqs))
Proof
  strip_tac >>
  ‘∃rs. EVERY P.valid rs ∧
        Rq V P ansq fin fd g j = FLAT (MAP P.print rs) ++ qbuf P (Sq V P ansq fin fd g j)’
    by (qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
        qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
        qpat_assum ‘j ≤ LENGTH g’ (fn t5 =>
          strip_assume_tac (MATCH_MP qinv0 (CONJ (LIST_CONJ [t1, t2, t3, t4]) t5))))))) >>
        metis_tac[]) >>
  qpat_x_assum ‘Rq _ _ _ _ _ _ _ = _’ SUBST1_TAC >>
  qpat_x_assum ‘Sq _ _ _ _ _ _ _ = _’ SUBST1_TAC >> simp[qbuf_def] >> strip_tac >>
  qspecl_then [‘rs’, ‘rqs’, ‘b’] mp_tac (Q.GEN ‘P’ proto_valid_noinv |> Q.SPEC ‘P’) >>
  simp[]
QED

(* MAIN: with all that is read a prefix of printed valid requests, the
   handler reads more within 2K + 4 rounds *)
Theorem q_read_grow_valid:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧ prompt (qcomp V P ansq fin fd (QA "")) g ∧
  P.parse "" ≠ PInvalid ∧
  (∀i. i ≤ LENGTH g ⇒
       ∃rqs. EVERY P.valid rqs ∧ Rq V P ansq fin fd g i ≼ FLAT (MAP P.print rqs)) ∧
  qenv V P ansq fin fd g j0 D ∧ j0 ≤ j ∧ ¬(D ≼ Rq V P ansq fin fd g j) ∧
  j + 2 * LENGTH (proto_all P D) + 4 ≤ LENGTH g ⇒
  ∃j'. j ≤ j' ∧ j' ≤ j + 2 * LENGTH (proto_all P D) + 4 ∧
       LENGTH (Rq V P ansq fin fd g j) < LENGTH (Rq V P ansq fin fd g j')
Proof
  strip_tac >> drule_all q_read_grow >> strip_tac >>
  qexists_tac ‘j'’ >> simp[] >>
  ‘j' ≤ LENGTH g’ by simp[] >>
  qpat_x_assum ‘∀i. i ≤ LENGTH g ⇒ _’ (qspec_then ‘j'’ mp_tac) >> simp[] >>
  CCONTR_TAC >> fs[] >>
  drule_all q_invalid_read >> simp[]
QED
