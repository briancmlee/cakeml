(*
  The query handler answers every complete request it receives, given
  the four environment facts (henv) and prompt answers to its queries:
  asyncProtoDrain for proto_handler_v (design/32 §2.3, for KV).

  What is owed for data D, given the answers ks the handler has received,
  is resps ansq fin (proto_all P D) ks: the responses to D's complete
  requests, each query's answer taken in order.  Each request takes one
  round (no query) or two (the query, then the write), so the bound is
  (|D| + 2)(2K + 3) rounds instead of (|D| + 2)(K + 3).
*)
Theory asyncProtoDrainV
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncCfActModel asyncProgress asyncServerV asyncServerVLive
  asyncServerVLiveA asyncProto asyncProtoServer asyncProtoV asyncProtoMachine
  asyncProtoMachineV
Libs
  BasicProvers

(* The handler of fd, started with an empty buffer, on history g, after
   the first j snapshots: its state, its transcript, what it has read and
   written (through the socket projection), and the answers it has *)
Overload Sq = “λV P ansq fin fd g j. qrun V P ansq fin fd (QA "") (TAKE j g)”
Overload Tq = “λV P ansq fin fd g j.
  trans (qcomp V P ansq fin fd (QA "")) (TAKE j g)”
Overload Rq = “λV P ansq fin fd g j.
  CONCAT (read fd (sproj V (trans (qcomp V P ansq fin fd (QA "")) (TAKE j g))))”
Overload Wq = “λV P ansq fin fd g j.
  written fd (sproj V (trans (qcomp V P ansq fin fd (QA "")) (TAKE j g)))”
Overload Kq = “λV P ansq fin fd g j.
  kanswers V (trans (qcomp V P ansq fin fd (QA "")) (TAKE j g))”

(* The hypotheses every lemma below shares *)
Overload qok = “λV P ansq fin fd g.
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧
  prompt (qcomp V P ansq fin fd (QA "")) g”

(* Use a lemma whose hypothesis is qok, from the four assumptions (so that
   its types are the goal's) *)
fun use_qok thm =
  qpat_assum ‘proto_ok _’ (fn t1 => qpat_assum ‘vocab_ok _’ (fn t2 =>
  qpat_assum ‘vocab_qok _’ (fn t3 => qpat_assum ‘prompt _ _’ (fn t4 =>
    mp_tac (MATCH_MP thm (LIST_CONJ [t1, t2, t3, t4]))))));

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem prefix_common_v:
  ∀l1 l2 l3. l1 ≼ l3 ∧ l2 ≼ l3 ∧ LENGTH l1 ≤ LENGTH l2 ⇒ l1 ≼ l2
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘l2’ >> Cases_on ‘l3’ >> simp[] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem resps_LENGTH:
  ∀rs ks. LENGTH (resps ansq fin rs ks) ≤ LENGTH rs
Proof
  Induct >> simp[resps_def] >> rpt gen_tac >> CASE_TAC >> simp[] >>
  CASE_TAC >> simp[]
QED

(* More requests, or more answers, can only add responses at the end *)
Theorem resps_mono:
  ∀rs rs' ks ks'. rs ≼ rs' ∧ ks ≼ ks' ⇒
                  resps ansq fin rs ks ≼ resps ansq fin rs' ks'
Proof
  Induct >> simp[resps_def] >> rpt gen_tac >> Cases_on ‘rs'’ >> simp[] >>
  strip_tac >> gvs[resps_def] >>
  Cases_on ‘ansq h’ >> gvs[] >>
  Cases_on ‘ks’ >> gvs[] >> Cases_on ‘ks'’ >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Transcript entries
   ------------------------------------------------------------------------ *)

Theorem sproj_APPEND_v[local]:
  ∀a b. sproj V (a ++ b) = sproj V a ++ sproj V b
Proof
  Induct >> simp[] >> Cases >> simp[]
QED

Theorem kanswers_APPEND_v[local]:
  kanswers V (a ++ b) = kanswers V a ++ kanswers V b
Proof
  simp[kanswers_def]
QED

(* A round that is not a read reads nothing *)
Theorem qacts_read_notB[local]:
  vocab_ok V ∧ vocab_qok V ∧ (∀b. st ≠ QB b) ⇒
  read fd (sproj V (zipr (qacts V P ansq fin fd st) rs)) = []
Proof
  rw[vocab_ok_def, vocab_qok_def] >>
  Cases_on ‘st’ >> gvs[qacts_def, zipr_def, read_def] >>
  rpt CASE_TAC >> simp[zipr_def, read_def]
QED

(* ------------------------------------------------------------------------
   The machine, round by round
   ------------------------------------------------------------------------ *)

Theorem Sq_SUC:
  j < LENGTH g ⇒
  Sq V P ansq fin fd g (SUC j) =
  qstep V P ansq fin fd (Sq V P ansq fin fd g j) (EL j g)
Proof
  strip_tac >> simp[GSYM SNOC_EL_TAKE, SNOC_APPEND, qrun_SNOC]
QED

Theorem Rq_Wq_SUC:
  qok V P ansq fin fd g ∧ j < LENGTH g ⇒
  Wq V P ansq fin fd g (SUC j) =
    Wq V P ansq fin fd g j ++ qpend P ansq fin (Sq V P ansq fin fd g (SUC j)) ∧
  ((∀b. Sq V P ansq fin fd g j ≠ QB b) ⇒
   Rq V P ansq fin fd g (SUC j) = Rq V P ansq fin fd g j) ∧
  Kq V P ansq fin fd g j ≼ Kq V P ansq fin fd g (SUC j)
Proof
  strip_tac >> ‘prompt (qcomp V P ansq fin fd (QA "")) g ∧ j < LENGTH g’ by simp[] >>
  drule_all qmachine_trans_SUC >> simp[] >> strip_tac >>
  simp[sproj_APPEND_v, written_def, read_def, kanswers_APPEND_v] >>
  simp[GSYM written_def, GSYM read_def, qacts_written, qacts_read_NIL,
       qacts_kanswers_NIL] >>
  rpt strip_tac >> simp[qacts_read_notB]
QED

Theorem Wq_Kq_mono:
  qok V P ansq fin fd g ⇒
  ∀k j. j + k ≤ LENGTH g ⇒
        Wq V P ansq fin fd g j ≼ Wq V P ansq fin fd g (j + k) ∧
        Kq V P ansq fin fd g j ≼ Kq V P ansq fin fd g (j + k)
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  ‘j + k < LENGTH g’ by simp[] >>
  drule_all Rq_Wq_SUC >> simp[ADD_CLAUSES] >> strip_tac >>
  metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS, APPEND_ASSOC]
QED

(* What the handler has written is a prefix of what is owed for what it
   has read, given the answers it has *)
Theorem Wq_resps:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ⇒
  Wq V P ansq fin fd g j ≼
  resps ansq fin (proto_all P (Rq V P ansq fin fd g j)) (Kq V P ansq fin fd g j)
Proof
  strip_tac >>
  ‘proto_ok P ∧ vocab_ok V ∧ vocab_qok V’ by simp[] >>
  qpat_assum ‘proto_ok _’ (fn th1 => qpat_assum ‘vocab_ok _’ (fn th2 =>
    qpat_assum ‘vocab_qok _’ (fn th3 =>
      mp_tac (MATCH_MP (Q.INST [‘b0’ |-> ‘""’] qmachine_inv) (LIST_CONJ [th1, th2, th3]))))) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then ‘j’ mp_tac) >> simp[] >>
  strip_tac >> simp[proto_all_print] >>
  ‘resps ansq fin
     (rs ++ proto_all P (qbuf P (qrun V P ansq fin fd (QA "") (TAKE j g))))
     (ks ++ qlast (qrun V P ansq fin fd (QA "") (TAKE j g))) =
   resps ansq fin rs ks ++
   resps ansq fin (proto_all P (qbuf P (qrun V P ansq fin fd (QA "") (TAKE j g))))
     (qlast (qrun V P ansq fin fd (QA "") (TAKE j g)))’
    by (irule resps_append >> simp[]) >>
  simp[] >>
  Cases_on ‘qrun V P ansq fin fd (QA "") (TAKE j g)’ >>
  simp[qbuf_def, qpend_def, qlast_def]
  >- (CASE_TAC >> simp[] >> drule_all proto_all_complete >> simp[resps_def] >>
      CASE_TAC >> simp[])
  >- (rename1 ‘QW req rest ko’ >> gvs[] >>
      ‘P.parse (P.print req ++ rest) = PComplete req rest’ by simp[proto_print] >>
      drule_all proto_all_complete >> simp[resps_def] >>
      Cases_on ‘ansq req’ >> gvs[])
  >> simp[]
QED

(* qmachine_inv, for the handler started on an empty buffer *)
Theorem qinv0:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ⇒
  ∃rs ks.
    EVERY P.valid rs ∧
    Rq V P ansq fin fd g j = FLAT (MAP P.print rs) ++ qbuf P (Sq V P ansq fin fd g j) ∧
    Kq V P ansq fin fd g j = ks ++ qlast (Sq V P ansq fin fd g j) ∧
    LENGTH ks = nq ansq rs ∧
    Wq V P ansq fin fd g j = resps ansq fin rs ks ++ qpend P ansq fin (Sq V P ansq fin fd g j) ∧
    (∀b. Sq V P ansq fin fd g j = QB b ⇒ P.parse b = PIncomplete) ∧
    (∀b r rest. Sq V P ansq fin fd g j = QD b ⇒ P.parse b ≠ PComplete r rest) ∧
    (∀req rest k. Sq V P ansq fin fd g j = QW req rest k ⇒
                  P.valid req ∧ IS_SOME (ansq req))
Proof
  strip_tac >>
  qpat_assum ‘proto_ok _’ (fn th1 => qpat_assum ‘vocab_ok _’ (fn th2 =>
    qpat_assum ‘vocab_qok _’ (fn th3 =>
      mp_tac (MATCH_MP (Q.INST [‘b0’ |-> ‘""’] qmachine_inv) (LIST_CONJ [th1, th2, th3]))))) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then ‘j’ mp_tac) >> simp[]
QED

(* Answering buffered requests: from state QA b, the first k complete
   requests in b are answered within 2k rounds (one round each, or two
   with a query), reading nothing *)
Theorem qdrain:
  qok V P ansq fin fd g ⇒
  ∀k j b. Sq V P ansq fin fd g j = QA b ∧ k ≤ LENGTH (proto_all P b) ∧
          j + 2 * k ≤ LENGTH g ⇒
          ∃j' rq b'. j ≤ j' ∧ j' ≤ j + 2 * k ∧ Sq V P ansq fin fd g j' = QA b' ∧
                     LENGTH rq = k ∧ proto_all P b = rq ++ proto_all P b' ∧
                     Rq V P ansq fin fd g j' = Rq V P ansq fin fd g j
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >> qexistsl [‘j’, ‘[]’, ‘b’] >> simp[]) >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [‘j’, ‘b’] mp_tac) >> simp[] >> strip_tac >>
  ‘proto_all P b' ≠ []’ by (strip_tac >> gvs[]) >>
  ‘∃r rest. P.parse b' = PComplete r rest’
    by (Cases_on ‘P.parse b'’ >> simp[] >>
        qpat_x_assum ‘proto_all P b' ≠ []’ mp_tac >> simp[Once proto_all_def]) >>
  drule_all proto_all_complete >> strip_tac >>
  ‘j' < LENGTH g’ by simp[] >>
  drule_all Rq_Wq_SUC >> strip_tac >>
  ‘Sq V P ansq fin fd g (SUC j') =
   qstep V P ansq fin fd (Sq V P ansq fin fd g j') (EL j' g)’
    by (irule Sq_SUC >> simp[]) >>
  Cases_on ‘ansq r’ >> gvs[qstep_def]
  (* no query: one round *)
  >- (qexistsl [‘SUC j'’, ‘rq ++ [r]’, ‘rest’] >> gvs[])
  (* a query: the answer, then the write *)
  >> ‘SUC j' < LENGTH g’ by simp[] >>
  drule_all Rq_Wq_SUC >> strip_tac >>
  ‘Sq V P ansq fin fd g (SUC (SUC j')) =
   qstep V P ansq fin fd (Sq V P ansq fin fd g (SUC j')) (EL (SUC j') g)’
    by (irule Sq_SUC >> simp[]) >>
  gvs[qstep_def] >>
  qexistsl [‘SUC (SUC j')’, ‘rq ++ [r]’, ‘rest’] >> gvs[]
QED

(* ------------------------------------------------------------------------
   What is owed, and when it has been written
   ------------------------------------------------------------------------ *)

Overload OUT = “λP ansq fin D ks. resps ansq fin (proto_all P D) ks”

(* With an answer for each query, every request gets its response *)
Theorem resps_LENGTH_full:
  ∀rs ks. LENGTH ks = nq ansq rs ⇒ LENGTH (resps ansq fin rs ks) = LENGTH rs
Proof
  Induct >> simp[resps_def, nq_def] >> rpt gen_tac >> Cases_on ‘ansq h’ >> simp[]
  >- metis_tac[nq_def] >>
  Cases_on ‘ks’ >> simp[] >> metis_tac[nq_def]
QED

(* If D extends no further than what the handler has read, and it has
   written at least as many responses as D has complete requests, it has
   written what is owed for D (given its answers) *)
Theorem out_by_length:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧
  D ≼ Rq V P ansq fin fd g j ∧
  LENGTH (proto_all P D) ≤ LENGTH (Wq V P ansq fin fd g j) ⇒
  OUT P ansq fin D (Kq V P ansq fin fd g j) ≼ Wq V P ansq fin fd g j
Proof
  strip_tac >>
  ‘Wq V P ansq fin fd g j ≼
   OUT P ansq fin (Rq V P ansq fin fd g j) (Kq V P ansq fin fd g j)’
    by (irule Wq_resps >> simp[]) >>
  ‘OUT P ansq fin D (Kq V P ansq fin fd g j) ≼
   OUT P ansq fin (Rq V P ansq fin fd g j) (Kq V P ansq fin fd g j)’
    by (irule resps_mono >> simp[proto_all_prefix]) >>
  ‘LENGTH (OUT P ansq fin D (Kq V P ansq fin fd g j)) ≤ LENGTH (Wq V P ansq fin fd g j)’
    by (irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (proto_all P D)’ >>
        simp[resps_LENGTH]) >>
  metis_tac[prefix_common_v]
QED

(* The responses written once the first n read requests are answered *)
Theorem out_when_answered:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧ EVERY P.valid rs ∧
  Rq V P ansq fin fd g j = FLAT (MAP P.print rs) ++ qbuf P (Sq V P ansq fin fd g j) ∧
  Wq V P ansq fin fd g j = resps ansq fin rs ks ++ qpend P ansq fin (Sq V P ansq fin fd g j) ∧
  LENGTH ks = nq ansq rs ∧
  D ≼ Rq V P ansq fin fd g j ∧ LENGTH (proto_all P D) ≤ LENGTH rs ⇒
  OUT P ansq fin D (Kq V P ansq fin fd g j) ≼ Wq V P ansq fin fd g j
Proof
  strip_tac >> irule out_by_length >> simp[] >>
  qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
  simp[resps_LENGTH_full]
QED

(* After a state that is not a read, with D read: what is owed for D is
   written within 2K + 1 rounds (finish a pending query's write, then
   drain the buffered requests) *)
Theorem drain_after_v:
  qok V P ansq fin fd g ∧
  j2 + 2 * LENGTH (proto_all P D) + 1 ≤ LENGTH g ∧
  D ≼ Rq V P ansq fin fd g j2 ∧ (∀b. Sq V P ansq fin fd g j2 ≠ QB b) ⇒
  ∃j. j2 ≤ j ∧ j ≤ j2 + 2 * LENGTH (proto_all P D) + 1 ∧
      OUT P ansq fin D (Kq V P ansq fin fd g j) ≼ Wq V P ansq fin fd g j
Proof
  strip_tac >> qabbrev_tac ‘NK = LENGTH (proto_all P D)’ >>
  (* from a state QA, at round j1 with D read, within 2K rounds *)
  ‘∀j1 b. j2 ≤ j1 ∧ j1 ≤ j2 + 1 ∧ Sq V P ansq fin fd g j1 = QA b ∧
          Rq V P ansq fin fd g j1 = Rq V P ansq fin fd g j2 ⇒
          ∃j. j1 ≤ j ∧ j ≤ j1 + 2 * NK ∧
              OUT P ansq fin D (Kq V P ansq fin fd g j) ≼ Wq V P ansq fin fd g j’
    by (rpt strip_tac >>
        ‘j1 ≤ LENGTH g’ by simp[] >>
        drule_all qinv0 >> strip_tac >> gvs[qbuf_def, qlast_def, qpend_def] >>
        ‘proto_all P D ≼ rs ++ proto_all P b’
          by metis_tac[proto_all_prefix, proto_all_print] >>
        imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
        Cases_on ‘NK ≤ LENGTH rs’
        >- (qexists_tac ‘j1’ >> simp[] >>
            qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’
              (fn th => SUBST1_TAC (SYM th) >> assume_tac th) >>
            irule out_by_length >> simp[] >>
            qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
            simp[resps_LENGTH_full] >> fs[Abbr ‘NK’]) >>
        use_qok qdrain >> disch_then (qspecl_then [‘NK − LENGTH rs’, ‘j1’, ‘b’] mp_tac) >>
        impl_tac >- fs[Abbr ‘NK’] >> strip_tac >>
        qexists_tac ‘j'’ >> simp[] >>
        ‘j' ≤ LENGTH g’ by simp[] >>
        drule_all qinv0 >> strip_tac >> gvs[qbuf_def, qlast_def, qpend_def] >>
        ‘rs' = rs ++ rq’
          by (‘FLAT (MAP P.print rs') ++ b' = FLAT (MAP P.print rs) ++ b’ by fs[] >>
              ‘proto_all P (FLAT (MAP P.print rs') ++ b') =
               proto_all P (FLAT (MAP P.print rs) ++ b)’ by simp[] >>
              gvs[proto_all_print]) >>
        gvs[] >>
        qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’
          (fn th => SUBST1_TAC (SYM th) >> assume_tac th) >>
        irule out_by_length >> simp[] >>
        qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        simp[resps_LENGTH_full] >> fs[Abbr ‘NK’]) >>
  ‘j2 ≤ LENGTH g’ by simp[] >>
  drule_all qinv0 >> strip_tac >>
  Cases_on ‘Sq V P ansq fin fd g j2’ >> gvs[]
  (* QA b *)
  >- (first_x_assum (qspecl_then [‘j2’, ‘s’] mp_tac) >> simp[] >> strip_tac >>
      qexists_tac ‘j’ >> simp[])
  (* QW: one round, then QA *)
  >- (rename1 ‘QW req rest ko’ >>
      ‘j2 < LENGTH g’ by simp[] >>
      drule_all Rq_Wq_SUC >> strip_tac >>
      ‘Sq V P ansq fin fd g (SUC j2) = QA rest’
        by (simp[Sq_SUC, qstep_def]) >>
      first_x_assum (qspecl_then [‘SUC j2’, ‘rest’] mp_tac) >> simp[] >>
      strip_tac >> qexists_tac ‘j’ >> simp[])
  (* QD b: nothing more is complete *)
  >> rename1 ‘QD b’ >>
  ‘proto_all P b = []’ by (simp[Once proto_all_def] >> CASE_TAC >> gvs[]) >>
  qexists_tac ‘j2’ >> simp[] >>
  TRY (qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’
         (fn th => SUBST1_TAC (SYM th) >> assume_tac th)) >>
  TRY (qpat_x_assum ‘Kq _ _ _ _ _ _ _ = _’
         (fn th => SUBST1_TAC (SYM th) >> assume_tac th)) >>
  irule out_by_length >> simp[] >>
  qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
  gvs[resps_LENGTH_full, qpend_def, qbuf_def, qlast_def] >>
  ‘proto_all P D ≼ rs ++ proto_all P b’
    by metis_tac[proto_all_prefix, proto_all_print] >>
  imp_res_tac IS_PREFIX_LENGTH >> gvs[]
QED
