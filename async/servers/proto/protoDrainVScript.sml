(*
  The query handler answers every complete request it receives, given
  the four environment facts (henv) and prompt answers to its queries:
  protoDrain for proto_handler_v (design/32 §2.3, for KV).

  What is owed for data D, given the answers ks the handler has received,
  is resps ansq fin (proto_all P D) ks: the responses to D's complete
  requests, each query's answer taken in order.  Each request takes one
  round (no query) or two (the query, then the write), so the bound is
  (|D| + 2)(2K + 3) rounds instead of (|D| + 2)(K + 3).
*)
Theory protoDrainV
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript echoServer
  echoServerSafety libModel echoProgress skeletonV skeletonVLive
  skeletonVLiveAns protoInterface protoServer protoV protoMachine
  protoMachineV
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

(* ------------------------------------------------------------------------
   Every query of D's complete requests has been answered
   ------------------------------------------------------------------------ *)

(* What is owed for D is written, and every query of D's complete
   requests has been answered *)
Overload DONE = “λV P ansq fin fd g D j.
  OUT P ansq fin D (Kq V P ansq fin fd g j) ≼ Wq V P ansq fin fd g j ∧
  nq ansq (proto_all P D) ≤ LENGTH (Kq V P ansq fin fd g j)”

Theorem nq_APPEND[local]:
  nq ansq (l1 ++ l2) = nq ansq l1 + nq ansq l2
Proof
  simp[nq_def, FILTER_APPEND_DISTRIB]
QED

Theorem nq_prefix[local]:
  l1 ≼ l2 ⇒ nq ansq l1 ≤ nq ansq l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[nq_APPEND]
QED

(* If the handler has written as many responses as D has complete
   requests, it has received an answer to each of their queries *)
Theorem Kq_full:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧
  D ≼ Rq V P ansq fin fd g j ∧
  LENGTH (proto_all P D) ≤ LENGTH (Wq V P ansq fin fd g j) ⇒
  nq ansq (proto_all P D) ≤ LENGTH (Kq V P ansq fin fd g j)
Proof
  strip_tac >> drule_all qinv0 >> strip_tac >>
  qabbrev_tac ‘qs = Sq V P ansq fin fd g j’ >>
  ‘proto_all P D ≼ rs ++ proto_all P (qbuf P qs)’
    by metis_tac[proto_all_prefix, proto_all_print] >>
  ‘LENGTH (proto_all P D) ≤ LENGTH rs + LENGTH (qpend P ansq fin qs)’
    by (qpat_x_assum ‘LENGTH (proto_all P D) ≤ _’ mp_tac >>
        qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        simp[resps_LENGTH_full]) >>
  qpat_x_assum ‘Kq _ _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
  Cases_on ‘LENGTH (proto_all P D) ≤ LENGTH rs’
  >- (‘proto_all P D ≼ rs’
        by (irule prefix_common_v >> simp[] >>
            qexists_tac ‘rs ++ proto_all P (qbuf P qs)’ >> simp[]) >>
      ‘nq ansq (proto_all P D) ≤ nq ansq rs’ by simp[nq_prefix] >> simp[]) >>
  (* one more: the pending write's request *)
  ‘∃r. proto_all P (qbuf P qs) = r :: TL (proto_all P (qbuf P qs)) ∧
       (IS_SOME (ansq r) ⇒ LENGTH (qlast qs) = 1)’
    by (Cases_on ‘qs’ >> gvs[qpend_def, qbuf_def, qlast_def]
        >- (every_case_tac >> gvs[] >> drule_all proto_all_complete >> simp[])
        >> rename1 ‘QW req rest ko’ >>
        ‘P.parse (P.print req ++ rest) = PComplete req rest’ by simp[proto_print] >>
        drule_all proto_all_complete >> simp[]) >>
  ‘proto_all P D ≼ rs ++ [r]’
    by (irule prefix_common_v >> simp[] >> conj_tac
        >- (‘LENGTH (qpend P ansq fin qs) ≤ 1’
              by (Cases_on ‘qs’ >> simp[qpend_def] >> every_case_tac >> simp[]) >>
            simp[]) >>
        qexists_tac ‘rs ++ r :: TL (proto_all P (qbuf P qs))’ >>
        reverse conj_tac >- simp[IS_PREFIX_APPEND] >>
        qpat_x_assum ‘proto_all P D ≼ _’ mp_tac >>
        qpat_x_assum ‘proto_all P (qbuf P qs) = _’ (fn th => ONCE_REWRITE_TAC[th]) >>
        simp[]) >>
  ‘nq ansq (proto_all P D) ≤ nq ansq (rs ++ [r])’ by simp[nq_prefix] >>
  fs[nq_APPEND] >> fs[nq_def] >> Cases_on ‘IS_SOME (ansq r)’ >> fs[]
QED

Theorem out_by_length_full:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧
  D ≼ Rq V P ansq fin fd g j ∧
  LENGTH (proto_all P D) ≤ LENGTH (Wq V P ansq fin fd g j) ⇒
  DONE V P ansq fin fd g D j
Proof
  strip_tac >> conj_tac
  >- (irule out_by_length >> simp[])
  >> irule Kq_full >> simp[]
QED

(* After a state that is not a read, with D read: what is owed for D is
   written within 2K + 1 rounds (finish a pending query's write, then
   drain the buffered requests) *)
Theorem drain_after_v:
  qok V P ansq fin fd g ∧
  j2 + 2 * LENGTH (proto_all P D) + 1 ≤ LENGTH g ∧
  D ≼ Rq V P ansq fin fd g j2 ∧ (∀b. Sq V P ansq fin fd g j2 ≠ QB b) ⇒
  ∃j. j2 ≤ j ∧ j ≤ j2 + 2 * LENGTH (proto_all P D) + 1 ∧
      DONE V P ansq fin fd g D j
Proof
  strip_tac >> qabbrev_tac ‘NK = LENGTH (proto_all P D)’ >>
  (* from a state QA, at round j1 with D read, within 2K rounds *)
  ‘∀j1 b. j2 ≤ j1 ∧ j1 ≤ j2 + 1 ∧ Sq V P ansq fin fd g j1 = QA b ∧
          Rq V P ansq fin fd g j1 = Rq V P ansq fin fd g j2 ⇒
          ∃j. j1 ≤ j ∧ j ≤ j1 + 2 * NK ∧
              DONE V P ansq fin fd g D j’
    by (rpt strip_tac >>
        ‘j1 ≤ LENGTH g’ by simp[] >>
        drule_all qinv0 >> strip_tac >> gvs[qbuf_def, qlast_def, qpend_def] >>
        ‘proto_all P D ≼ rs ++ proto_all P b’
          by metis_tac[proto_all_prefix, proto_all_print] >>
        imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
        Cases_on ‘NK ≤ LENGTH rs’
        >- (qexists_tac ‘j1’ >> simp[] >>
            ‘DONE V P ansq fin fd g D j1’ suffices_by simp[] >>
            qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’
              (fn th => SUBST1_TAC (SYM th) >> assume_tac th) >>
            irule out_by_length_full >> simp[] >>
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
        ‘DONE V P ansq fin fd g D j'’ suffices_by simp[] >>
        qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’
          (fn th => SUBST1_TAC (SYM th) >> assume_tac th) >>
        irule out_by_length_full >> simp[] >>
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
  ‘DONE V P ansq fin fd g D j2’ suffices_by simp[] >>
  TRY (qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’
         (fn th => SUBST1_TAC (SYM th) >> assume_tac th)) >>
  TRY (qpat_x_assum ‘Kq _ _ _ _ _ _ _ = _’
         (fn th => SUBST1_TAC (SYM th) >> assume_tac th)) >>
  irule out_by_length_full >> simp[] >>
  qpat_x_assum ‘Wq _ _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
  gvs[resps_LENGTH_full, qpend_def, qbuf_def, qlast_def] >>
  ‘proto_all P D ≼ rs ++ proto_all P b’
    by metis_tac[proto_all_prefix, proto_all_print] >>
  imp_res_tac IS_PREFIX_LENGTH >> gvs[]
QED

(* What the handler has read only grows *)
Theorem Rq_SUC_prefix:
  qok V P ansq fin fd g ∧ j < LENGTH g ⇒
  Rq V P ansq fin fd g j ≼ Rq V P ansq fin fd g (SUC j)
Proof
  strip_tac >> ‘prompt (qcomp V P ansq fin fd (QA "")) g ∧ j < LENGTH g’ by simp[] >>
  drule_all qmachine_trans_SUC >> simp[] >> strip_tac >>
  simp[sproj_APPEND_v, read_def] >>
  simp[GSYM read_def, qacts_read_NIL]
QED

(* After a read at round j1 (state QB) that leaves all of D read, what is
   owed for D is written within 2K + 2 rounds *)
Theorem after_read_v:
  qok V P ansq fin fd g ∧
  j1 + 2 * LENGTH (proto_all P D) + 2 ≤ LENGTH g ∧
  Sq V P ansq fin fd g j1 = QB b1 ∧ D ≼ Rq V P ansq fin fd g (SUC j1) ⇒
  ∃j. j ≤ j1 + 2 * LENGTH (proto_all P D) + 2 ∧
      DONE V P ansq fin fd g D j
Proof
  strip_tac >>
  ‘∀b. Sq V P ansq fin fd g (SUC j1) ≠ QB b’
    by (‘j1 < LENGTH g’ by simp[] >> simp[Sq_SUC, qstep_def] >>
        every_case_tac >> simp[]) >>
  ‘∃j. SUC j1 ≤ j ∧ j ≤ SUC j1 + 2 * LENGTH (proto_all P D) + 1 ∧
       DONE V P ansq fin fd g D j’
    by (irule drain_after_v >> simp[]) >>
  qexists_tac ‘j’ >> simp[]
QED

(* With all of D read by round j0, what is owed for D is written within
   2K + 2 rounds *)
Theorem live_read_v:
  qok V P ansq fin fd g ∧
  j0 + 2 * LENGTH (proto_all P D) + 2 ≤ LENGTH g ∧
  D ≼ Rq V P ansq fin fd g j0 ⇒
  ∃j. j ≤ j0 + 2 * LENGTH (proto_all P D) + 2 ∧
      DONE V P ansq fin fd g D j
Proof
  strip_tac >> Cases_on ‘∃b. Sq V P ansq fin fd g j0 = QB b’
  >- (fs[] >>
      ‘D ≼ Rq V P ansq fin fd g (SUC j0)’
        by (‘j0 < LENGTH g’ by simp[] >>
            metis_tac[Rq_SUC_prefix, IS_PREFIX_TRANS]) >>
      ‘∃j. j ≤ j0 + 2 * LENGTH (proto_all P D) + 2 ∧
           DONE V P ansq fin fd g D j’
        by (irule after_read_v >> simp[] >> metis_tac[]) >>
      qexists_tac ‘j’ >> simp[])
  >> ‘∃j. j0 ≤ j ∧ j ≤ j0 + 2 * LENGTH (proto_all P D) + 1 ∧
         DONE V P ansq fin fd g D j’
       by (irule drain_after_v >> simp[] >> metis_tac[]) >>
  qexists_tac ‘j’ >> simp[]
QED

(* Stopped (or about to stop) on an invalid buffer: everything owed has
   been written *)
Theorem stopped_invalid_v:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧
  (Sq V P ansq fin fd g j = QA b ∨ Sq V P ansq fin fd g j = QD b) ∧
  P.parse b = PInvalid ∧ Rq V P ansq fin fd g j ≼ D ⇒
  OUT P ansq fin D (Kq V P ansq fin fd g j) ≼ Wq V P ansq fin fd g j
Proof
  strip_tac >> drule_all qinv0 >> strip_tac >>
  gvs[qbuf_def, qlast_def, qpend_def, IS_PREFIX_APPEND] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> qexists_tac ‘[]’ >>
  ‘proto_all P (FLAT (MAP P.print rs) ++ (b ++ l)) = rs ++ proto_all P (b ++ l)’
    by (irule proto_all_print >> simp[]) >>
  ‘proto_all P (b ++ l) = []’ by (irule proto_all_invalid_ext >> simp[]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> asm_rewrite_tac[APPEND_NIL]
QED

(* stopped_invalid_v, with every query of D's complete requests answered *)
Theorem stopped_invalid_full:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧
  (Sq V P ansq fin fd g j = QA b ∨ Sq V P ansq fin fd g j = QD b) ∧
  P.parse b = PInvalid ∧ Rq V P ansq fin fd g j ≼ D ⇒
  DONE V P ansq fin fd g D j
Proof
  strip_tac >> conj_tac
  >- (irule stopped_invalid_v >> metis_tac[]) >>
  drule_all qinv0 >> strip_tac >>
  gvs[qbuf_def, qlast_def, qpend_def, IS_PREFIX_APPEND] >>
  ‘proto_all P (FLAT (MAP P.print rs) ++ (b ++ l)) = rs ++ proto_all P (b ++ l)’
    by (irule proto_all_print >> simp[]) >>
  ‘proto_all P (b ++ l) = []’ by (irule proto_all_invalid_ext >> simp[]) >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> asm_rewrite_tac[APPEND_NIL] >> simp[]
QED



(* MAIN: liveness of the query machine when a read may return only part
   of the unread data, given the four environment facts (as
   pmachine_live_p).  Each cycle (finish a pending query's write, answer
   at most K buffered requests in at most 2K rounds, wait one round,
   read) takes at most 2K + 3 rounds and either reads all of D or reads
   something. *)
Theorem qmachine_live_p_v:
  qok V P ansq fin fd g ∧
  (∀j. j0 ≤ j ∧ j ≤ LENGTH g ⇒
       Rq V P ansq fin fd g j ≼ D ∨ D ≼ Rq V P ansq fin fd g j) ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sq V P ansq fin fd g j = QA b ∧
         P.parse b = PIncomplete ∧ Readable fd ∉ (EL j g).ready ⇒
         D ≼ Rq V P ansq fin fd g j) ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sq V P ansq fin fd g j = QB b ∧
         ¬(D ≼ Rq V P ansq fin fd g j) ⇒
         D ≼ Rq V P ansq fin fd g (SUC j) ∨
         LENGTH (Rq V P ansq fin fd g j) < LENGTH (Rq V P ansq fin fd g (SUC j))) ∧
  (∀j b. j0 ≤ j ∧ j ≤ LENGTH g ∧ Sq V P ansq fin fd g j = QD b ∧
         P.parse b = PIncomplete ⇒ D ≼ Rq V P ansq fin fd g j) ⇒
  ∀m j. j0 ≤ j ∧ LENGTH D ≤ LENGTH (Rq V P ansq fin fd g j) + m ∧
        j + (m + 2) * (2 * LENGTH (proto_all P D) + 3) ≤ LENGTH g ⇒
        ∃j'. j' ≤ LENGTH g ∧
             DONE V P ansq fin fd g D j'
Proof
  strip_tac >> completeInduct_on ‘m’ >> rpt strip_tac >>
  qabbrev_tac ‘NK = LENGTH (proto_all P D)’ >>
  ‘j + 2 * NK + 3 ≤ LENGTH g’ by (Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
  (* finishing: once all of D has been read, by round j1 *)
  ‘∀j1. j1 ≤ j + 2 * NK + 3 ∧ D ≼ Rq V P ansq fin fd g j1 ⇒
        ∃j'. j' ≤ LENGTH g ∧
             DONE V P ansq fin fd g D j'’
    by (rpt strip_tac >>
        ‘∃j'. j' ≤ j1 + 2 * LENGTH (proto_all P D) + 2 ∧
              DONE V P ansq fin fd g D j'’
          by (irule live_read_v >> fs[Abbr ‘NK’] >>
              Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
        qexists_tac ‘j'’ >> fs[Abbr ‘NK’] >> Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
  Cases_on ‘D ≼ Rq V P ansq fin fd g j’
  >- (first_x_assum irule >> qexists_tac ‘j’ >> simp[]) >>
  ‘j ≤ LENGTH g’ by simp[] >>
  ‘Rq V P ansq fin fd g j ≼ D’ by metis_tac[] >>
  ‘LENGTH (Rq V P ansq fin fd g j) < LENGTH D’
    by (CCONTR_TAC >> fs[NOT_LESS] >>
        ‘LENGTH (Rq V P ansq fin fd g j) = LENGTH D’
          by (imp_res_tac IS_PREFIX_LENGTH >> simp[]) >>
        ‘Rq V P ansq fin fd g j = D’ by metis_tac[IS_PREFIX_LENGTH_ANTI] >>
        fs[]) >>
  ‘0 < m’ by simp[] >>
  (* growing: a read at round j2 (state QB), nothing read since j *)
  ‘∀j2 b2. j ≤ j2 ∧ j2 ≤ j + 2 * NK + 2 ∧ Sq V P ansq fin fd g j2 = QB b2 ∧
           Rq V P ansq fin fd g j2 = Rq V P ansq fin fd g j ⇒
           ∃j'. j' ≤ LENGTH g ∧
                DONE V P ansq fin fd g D j'’
    by (rpt strip_tac >>
        ‘j2 < LENGTH g’ by simp[] >>
        qpat_x_assum ‘∀j b. _ ∧ _ ∧ Sq _ _ _ _ _ _ _ = QB _ ∧ _ ⇒ _’
          (qspecl_then [‘j2’, ‘b2’] mp_tac) >>
        impl_tac >- simp[] >> strip_tac
        >- (qpat_x_assum ‘∀j1. _ ⇒ ∃j'. _’ irule >> qexists_tac ‘SUC j2’ >> simp[]) >>
        qpat_x_assum ‘∀m'. m' < m ⇒ _’ (qspec_then ‘m − 1’ mp_tac) >>
        impl_tac >- simp[] >>
        disch_then (qspec_then ‘SUC j2’ mp_tac) >> impl_tac
        >- (rpt conj_tac >- simp[]
            >- (qpat_x_assum ‘Rq _ _ _ _ _ _ j2 = _’ (fn th => fs[th]))
            >> Cases_on ‘m’ >> fs[MULT_CLAUSES, ADD1, Abbr ‘NK’]) >>
        simp[]) >>
  (* from a state QA at round j1 ≤ j + 1, nothing read since j *)
  ‘∀j1 b. j ≤ j1 ∧ j1 ≤ j + 1 ∧ Sq V P ansq fin fd g j1 = QA b ∧
          Rq V P ansq fin fd g j1 = Rq V P ansq fin fd g j ⇒
          ∃j'. j' ≤ LENGTH g ∧
               DONE V P ansq fin fd g D j'’
    by (rpt strip_tac >>
        ‘j1 ≤ LENGTH g’ by simp[] >>
        drule_all qinv0 >> strip_tac >> gvs[qbuf_def, qlast_def, qpend_def] >>
        ‘LENGTH (proto_all P b) ≤ NK’
          by (‘rs ++ proto_all P b ≼ proto_all P D’
                by (‘proto_all P (Rq V P ansq fin fd g j) ≼ proto_all P D’
                      by (irule proto_all_prefix >> simp[]) >>
                    ‘proto_all P (Rq V P ansq fin fd g j) = rs ++ proto_all P b’
                      by (qpat_x_assum ‘STRCAT _ b = _’ (SUBST1_TAC o SYM) >>
                          irule proto_all_print >> simp[]) >>
                    gvs[]) >>
              imp_res_tac IS_PREFIX_LENGTH >> fs[Abbr ‘NK’]) >>
        use_qok qdrain >>
        disch_then (qspecl_then [‘LENGTH (proto_all P b)’, ‘j1’, ‘b’] mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        ‘proto_all P b' = []’
          by (qpat_x_assum ‘LENGTH rq = _’ mp_tac >>
              qpat_x_assum ‘proto_all P b = _’ (fn th => REWRITE_TAC[th]) >>
              REWRITE_TAC[LENGTH_APPEND] >> strip_tac >>
              ‘LENGTH (proto_all P b') = 0’ by decide_tac >>
              fs[LENGTH_NIL]) >>
        (* these two would make the simplifier loop *)
        qpat_x_assum ‘LENGTH rq = _’ kall_tac >>
        qpat_x_assum ‘proto_all P b = _’ kall_tac >>
        ‘∀r rest. P.parse b' ≠ PComplete r rest’
          by (rpt strip_tac >>
              ‘proto_all P b' = r :: proto_all P rest’
                by (irule proto_all_complete >> simp[]) >>
              gvs[]) >>
        Cases_on ‘P.parse b'’ >> fs[]
        (* incomplete: wait for readiness, then read *)
        >- (‘j' < LENGTH g’ by simp[] >>
            Cases_on ‘Readable fd ∈ (EL j' g).ready’
            >- (‘Sq V P ansq fin fd g (SUC j') = QB b'’
                  by simp[Sq_SUC, qstep_def] >>
                ‘Rq V P ansq fin fd g (SUC j') = Rq V P ansq fin fd g j'’
                  by (drule_all Rq_Wq_SUC >> simp[]) >>
                qpat_x_assum ‘∀j2 b2. _ ∧ _ ∧ Sq _ _ _ _ _ _ j2 = QB b2 ∧ Rq _ _ _ _ _ _ j2 = _ ⇒ _’ (qspecl_then [‘SUC j'’, ‘b'’] mp_tac) >>
                simp[]) >>
            qpat_x_assum ‘∀j b. _ ∧ _ ∧ _ = QA _ ∧ _ ⇒ _’
              (qspecl_then [‘j'’, ‘b'’] mp_tac) >> simp[] >> strip_tac >>
            qpat_x_assum ‘∀j1. _ ⇒ ∃j'. _’ irule >> qexists_tac ‘j'’ >> simp[]) >>
        (* invalid: everything owed has been written *)
        qexists_tac ‘j'’ >> simp[] >>
        irule stopped_invalid_full >> simp[] >> qexists_tac ‘b'’ >> simp[]) >>
  Cases_on ‘Sq V P ansq fin fd g j’
  (* about to act on buffer b *)
  >- (first_x_assum (qspecl_then [‘j’, ‘s’] mp_tac) >> simp[])
  (* a query's write: one round, then QA *)
  >- (rename1 ‘QW req rest ko’ >>
      ‘j < LENGTH g’ by simp[] >>
      drule_all Rq_Wq_SUC >> strip_tac >>
      ‘Sq V P ansq fin fd g (SUC j) = QA rest’ by simp[Sq_SUC, qstep_def] >>
      first_x_assum (qspecl_then [‘SUC j’, ‘rest’] mp_tac) >> simp[])
  (* reading this round *)
  >- (qpat_x_assum ‘∀j2 b2. _ ∧ _ ∧ Sq _ _ _ _ _ _ j2 = QB b2 ∧ Rq _ _ _ _ _ _ j2 = _ ⇒ _’ (qspecl_then [‘j’, ‘s’] mp_tac) >> simp[])
  (* stopped: on end-of-file (all of D read), or on invalid input *)
  >> rename1 ‘QD b’ >>
  drule_all qinv0 >> strip_tac >>
  Cases_on ‘P.parse b’
  >- (res_tac >> fs[])
  >- (qpat_x_assum ‘∀j b. _ ∧ _ ∧ _ = QD _ ∧ _ ⇒ _’ (qspecl_then [‘j’, ‘b’] mp_tac) >>
      simp[])
  >> qexists_tac ‘j’ >> conj_tac >- simp[] >>
  irule stopped_invalid_full >> simp[] >> qexists_tac ‘b’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Reading and end-of-file in the socket part of the transcript
   ------------------------------------------------------------------------ *)

Theorem MEM_sproj:
  ∀tr. MEM (a, r) tr ∧ V.sact a = SOME x ⇒
       MEM (x, OPTION_BIND r V.sres) (sproj V tr)
Proof
  Induct >> simp[] >> Cases >> rw[] >> gvs[] >> CASE_TAC >> simp[]
QED

Theorem MEM_sproj_rd:
  ∀tr. vocab_ok V ∧ MEM (V.rd fd, r) tr ⇒
       MEM (Read fd, OPTION_BIND r V.sres) (sproj V tr)
Proof
  Induct >> simp[] >> Cases >> rw[] >> gvs[vocab_ok_def] >> CASE_TAC >> simp[]
QED

(* In state QB the handler has a read of fd outstanding *)
Theorem qmachine_reading:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧ Sq V P ansq fin fd g j = QB b ⇒
  MEM (Read fd, NONE) (sproj V (Tq V P ansq fin fd g j))
Proof
  strip_tac >>
  ‘prompt (qcomp V P ansq fin fd (QA "")) g ∧ j ≤ LENGTH g’ by simp[] >>
  drule_all qmachine_trans_TAKE >> disch_then SUBST1_TAC >>
  ‘MEM (V.rd fd, NONE)
     (FLAT (GENLIST (λi. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd (QA "") (TAKE i g)))
                              (if i < j then (EL i g).results else [])) (SUC j)))’
    by (simp[MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> qexists_tac ‘j’ >>
        simp[qacts_def, zipr_def]) >>
  drule_all MEM_sproj_rd >> simp[]
QED

(* The handler stops on a buffer that is not invalid only after reading
   end-of-file *)
Theorem qmachine_stopped_eof:
  ∀j b. j ≤ LENGTH g ∧ Sq V P ansq fin fd g j = QD b ∧ P.parse b ≠ PInvalid ⇒
        ∃i b'. i < j ∧ Sq V P ansq fin fd g i = QB b' ∧
               OPTION_BIND (oHD (EL i g).results) V.sres = SOME Eof
Proof
  Induct >- simp[qrun_def] >>
  rpt strip_tac >>
  ‘j < LENGTH g’ by simp[] >>
  qpat_x_assum ‘Sq _ _ _ _ _ _ (SUC j) = _’ mp_tac >>
  drule_then (fn th => REWRITE_TAC[th]) Sq_SUC >>
  Cases_on ‘Sq V P ansq fin fd g j’ >> simp[qstep_def]
  >- (every_case_tac >> simp[] >> strip_tac >> gvs[])
  >- (every_case_tac >> simp[] >> strip_tac >> gvs[] >>
      qexists_tac ‘j’ >> simp[])
  >> strip_tac >> gvs[] >>
  metis_tac[DECIDE “i < j ⇒ i < SUC j”]
QED

(* So the socket part of its transcript has the read that returned
   end-of-file *)
Theorem qmachine_eof:
  qok V P ansq fin fd g ∧ j ≤ LENGTH g ∧
  Sq V P ansq fin fd g j = QD b ∧ P.parse b ≠ PInvalid ⇒
  MEM (Read fd, SOME Eof) (sproj V (Tq V P ansq fin fd g j))
Proof
  strip_tac >>
  ‘∃i b'. i < j ∧ Sq V P ansq fin fd g i = QB b' ∧
          OPTION_BIND (oHD (EL i g).results) V.sres = SOME Eof’
    by (irule qmachine_stopped_eof >> simp[] >> qexists_tac ‘b’ >> simp[]) >>
  ‘prompt (qcomp V P ansq fin fd (QA "")) g ∧ j ≤ LENGTH g’ by simp[] >>
  drule_all qmachine_trans_TAKE >> disch_then SUBST1_TAC >>
  ‘MEM (V.rd fd, oHD (EL i g).results)
     (FLAT (GENLIST (λi'. zipr (qacts V P ansq fin fd (qrun V P ansq fin fd (QA "") (TAKE i' g)))
                               (if i' < j then (EL i' g).results else [])) (SUC j)))’
    by (simp[MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> qexists_tac ‘i’ >>
        simp[qacts_def, zipr_def]) >>
  drule_all MEM_sproj_rd >> simp[]
QED
