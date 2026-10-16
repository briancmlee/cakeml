(*
  The generic handler answers every complete request it receives, as a
  fact about the state machine (protoMachine) given four facts about
  its environment: asyncHttpDrainB for every protocol with proto_ok
  (design/32 phase 3).

  pmachine_live_p: let D be data that has arrived on the connection (by
  round j0), K the number of complete requests at its front.  If
   - what has been read and D are always comparable;
   - waiting with an incomplete buffer while fd is not reported readable
     means all of D has been read;
   - a read, unless D has been read already, reads all of D or reads
     something;
   - stopping at end-of-file means D has been read;
  then within (|D| + 2)(K + 3) rounds the handler has written the
  responses to all K requests.  These are design/34's henv facts.
*)
Theory protoDrain
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncChoose asyncLoop asyncTranscript echoServer
  echoServerSafety libModel echoProgress protoInterface protoServer
  protoMachine
Libs
  BasicProvers

(* Lemmas that need proto_ok P, with that hypothesis undischarged: they are
   used inside proofs whose goals have proto_ok P as an assumption *)
fun ok th = th |> SPEC_ALL |> UNDISCH_ALL_OK |> GEN_ALL
and UNDISCH_ALL_OK th =
  let val (a, _) = dest_imp (concl th)
  in if is_conj a andalso same_const (fst (strip_comb (fst (dest_conj a)))) “proto_ok”
     then UNDISCH (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th)
     else UNDISCH th
  end


val pcomplete = ok proto_complete;
val pextend = ok proto_extend;
val pshorter = ok proto_complete_shorter;
val pall_print = ok proto_all_print;
val pall_complete = ok proto_all_complete;
val pall_eqn = ok proto_all_eqn;
val pall_prefix = ok proto_all_prefix;
val pall_invalid_ext = ok proto_all_invalid_ext;

(* The handler of fd, started with an empty buffer, on history g: its state,
   what it has read, and what it has written, after the first j snapshots *)
Overload Sj = “λP resp fd g j. prun P resp fd (PA "") (TAKE j g)”
Overload Rj = “λP resp fd g j.
  CONCAT (read fd (trans (pcomp P resp fd (PA "")) (TAKE j g)))”
Overload Wj = “λP resp fd g j. written fd (trans (pcomp P resp fd (PA "")) (TAKE j g))”

(* ------------------------------------------------------------------------
   Parsing facts
   ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------
   Parsing facts: protoInterface's, generic
   ------------------------------------------------------------------------ *)

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
  j < LENGTH g ⇒ Sj P resp fd g (SUC j) = pstep P resp fd (Sj P resp fd g j) (EL j g)
Proof
  strip_tac >> simp[GSYM SNOC_EL_TAKE, SNOC_APPEND, prun_SNOC]
QED

Theorem Rj_Wj_SUC:
  prompt (pcomp P resp fd (PA "")) g ∧ j < LENGTH g ⇒
  Wj P resp fd g (SUC j) = Wj P resp fd g j ++ ppend P resp (Sj P resp fd g (SUC j)) ∧
  ((∀b. Sj P resp fd g j ≠ PB b) ⇒ Rj P resp fd g (SUC j) = Rj P resp fd g j)
Proof
  strip_tac >> drule_all pmachine_trans_SUC >> simp[] >> strip_tac >>
  simp[written_zipr] >> rpt strip_tac >>
  Cases_on ‘prun P resp fd (PA "") (TAKE j g)’ >> gvs[pacts_def, ppend_def] >>
  TRY (CASE_TAC >> simp[]) >>
  qspec_tac (‘(EL j g).results’, ‘rs’) >> Cases >> simp[zipr_def]
QED

Theorem Wj_mono:
  prompt (pcomp P resp fd (PA "")) g ⇒
  ∀k j. j + k ≤ LENGTH g ⇒ Wj P resp fd g j ≼ Wj P resp fd g (j + k)
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >>
  drule_then (qspec_then ‘j + k’ mp_tac) Rj_Wj_SUC >> simp[ADD_CLAUSES] >>
  metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS, APPEND_ASSOC]
QED

(* What the handler has written is a prefix of the responses to what it
   has read *)
Theorem Wj_responses:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧ j ≤ LENGTH g ⇒
  Wj P resp fd g j ≼ proto_responses_to P resp (Rj P resp fd g j))
Proof
  DISCH_TAC >>
  strip_tac >> drule_then (qspec_then ‘j’ mp_tac) (ok pmachine_inv) >> simp[] >>
  strip_tac >> simp[pall_print] >>
  Cases_on ‘prun P resp fd (PA "") (TAKE j g)’ >> simp[pbuf_def, ppend_def] >>
  CASE_TAC >> simp[] >> drule pall_complete >> simp[]
QED

(* Answering buffered requests: in state PA b, the next k ≤ (number of
   complete requests in b) rounds each answer one of them *)
Theorem pdrain:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ⇒
  ∀k j b. Sj P resp fd g j = PA b ∧ k ≤ LENGTH (proto_all P b) ∧ j + k ≤ LENGTH g ⇒
          ∃rq b'. Sj P resp fd g (j + k) = PA b' ∧ LENGTH rq = k ∧
                  proto_all P b = rq ++ proto_all P b' ∧
                  Rj P resp fd g (j + k) = Rj P resp fd g j)
Proof
  DISCH_TAC >>
  strip_tac >> Induct >- (rw[] >> qexists_tac ‘[]’ >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  ‘proto_all P b' ≠ []’ by (strip_tac >> gvs[]) >>
  ‘∃r rest. P.parse b' = PComplete r rest’
    by (qpat_x_assum ‘proto_all P b' ≠ []’ mp_tac >> simp[Once pall_eqn] >>
        CASE_TAC >> simp[]) >>
  drule pall_complete >> strip_tac >>
  ‘j + k < LENGTH g’ by simp[] >>
  ‘Sj P resp fd g (SUC (j + k)) = pstep P resp fd (Sj P resp fd g (j + k)) (EL (j + k) g)’
    by (irule Sj_SUC >> simp[]) >>
  gvs[ADD_CLAUSES, pstep_def] >>
  TRY (qexistsl [‘rq ++ [r]’, ‘rest’] >> gvs[]) >>
  drule_then (qspec_then ‘j + LENGTH rq’ mp_tac) Rj_Wj_SUC >> simp[]
QED

(* ------------------------------------------------------------------------
   Liveness of the machine
   ------------------------------------------------------------------------ *)

Theorem presponses_prefix:
  proto_ok P ⇒
  (s ≼ t ⇒ proto_responses_to P resp s ≼ proto_responses_to P resp t)
Proof
  DISCH_TAC >>
  strip_tac >> drule pall_prefix >> rw[IS_PREFIX_APPEND] >> simp[]
QED

(* If what the handler has written at round j contains as many responses as
   there are complete requests in D, and D extends no further than what it
   has read, then it has written the responses to D *)
Theorem responses_by_length:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧ j ≤ LENGTH g ∧
  D ≼ Rj P resp fd g j ∧ LENGTH (proto_all P D) ≤ LENGTH (Wj P resp fd g j) ⇒
  proto_responses_to P resp D ≼ Wj P resp fd g j)
Proof
  DISCH_TAC >>
  strip_tac >>
  ‘proto_responses_to P resp D ≼ proto_responses_to P resp (Rj P resp fd g j)’
    by simp[(ok presponses_prefix)] >>
  ‘Wj P resp fd g j ≼ proto_responses_to P resp (Rj P resp fd g j)’ by simp[(ok Wj_responses)] >>
  metis_tac[prefix_common, LENGTH_MAP]
QED

(* After a read: within NK rounds, the responses to D are written *)
Theorem drain_after:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧ j2 + LENGTH (proto_all P D) ≤ LENGTH g ∧
  D ≼ Rj P resp fd g j2 ∧ (∀b. Sj P resp fd g j2 ≠ PB b) ⇒
  ∃j. j2 ≤ j ∧ j ≤ j2 + LENGTH (proto_all P D) ∧ proto_responses_to P resp D ≼ Wj P resp fd g j)
Proof
  DISCH_TAC >>
  strip_tac >> qabbrev_tac ‘NK = LENGTH (proto_all P D)’ >>
  drule_then (qspec_then ‘j2’ mp_tac) (ok pmachine_inv) >> simp[] >> strip_tac >>
  ‘proto_all P D ≼ rs ++ proto_all P (pbuf (Sj P resp fd g j2))’
    by metis_tac[pall_prefix, pall_print] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  Cases_on ‘NK ≤ LENGTH rs’
  >- (qexists_tac ‘j2’ >> simp[] >>
      qpat_assum ‘written _ _ = _’ (SUBST1_TAC o SYM) >>
      irule (ok responses_by_length) >> simp[] >>
      qpat_x_assum ‘written _ _ = _’ (fn th => REWRITE_TAC[th]) >> simp[])
  >> Cases_on ‘Sj P resp fd g j2’ >> gvs[pbuf_def]
  >- (rename1 ‘prun P resp fd (PA "") (TAKE j2 g) = PA b’ >>
      drule_then (qspecl_then [‘NK − LENGTH rs’, ‘j2’, ‘b’] mp_tac) (ok pdrain) >>
      simp[] >> strip_tac >>
      qexists_tac ‘j2 + (NK − LENGTH rs)’ >> simp[] >>
      irule (ok responses_by_length) >> simp[] >>
      drule_then (qspec_then ‘j2 + (NK − LENGTH rs)’ mp_tac) (ok pmachine_inv) >>
      simp[] >> strip_tac >> gvs[pbuf_def] >>
      ‘rs' ++ proto_all P b' = rs ++ rq ++ proto_all P b'’
        by metis_tac[pall_print, APPEND_ASSOC] >>
      gvs[])
  >> rename1 ‘prun P resp fd (PA "") (TAKE j2 g) = PD b’ >>
  ‘proto_all P b = []’ by (irule proto_all_not_complete >> metis_tac[]) >>
  gvs[]
QED

(* If D is no longer than what has been read, its responses are among
   those to the requests read so far *)
Theorem responses_upto:
  proto_ok P ⇒
  (EVERY P.valid rs ∧ D ≼ FLAT (MAP P.print rs) ++ b ⇒
  proto_responses_to P resp D ≼
    MAP (resp) rs ++ proto_responses_to P resp b ++ p)
Proof
  DISCH_TAC >>
  strip_tac >> drule_then (qspec_then ‘resp’ assume_tac) (ok presponses_prefix) >>
  gs[pall_print] >> irule IS_PREFIX_TRANS >>
  first_assum (irule_at Any) >> simp[IS_PREFIX_APPEND]
QED

(* An invalid request ends what can be answered: the responses to any D
   extending it are those to the requests before it *)
Theorem responses_invalid:
  proto_ok P ⇒
  (EVERY P.valid rs ∧ P.parse b = PInvalid ∧
  FLAT (MAP P.print rs) ++ b ≼ D ⇒
  proto_responses_to P resp D = MAP (resp) rs)
Proof
  DISCH_TAC >>
  rw[IS_PREFIX_APPEND] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
  drule_then (fn th => REWRITE_TAC[th]) pall_print >>
  drule_then (fn th => REWRITE_TAC[th]) pall_invalid_ext >> simp[]
QED

(* After a read at round j1 (state PB) that leaves all of D read, the
   responses to D are written within 1 + K rounds *)
Theorem after_read_live:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧ j1 + 2 + LENGTH (proto_all P D) ≤ LENGTH g ∧
  Sj P resp fd g j1 = PB b1 ∧ D ≼ Rj P resp fd g (SUC j1) ⇒
  ∃j. j ≤ j1 + 1 + LENGTH (proto_all P D) ∧ proto_responses_to P resp D ≼ Wj P resp fd g j)
Proof
  DISCH_TAC >>
  strip_tac >>
  ‘∀b. Sj P resp fd g (SUC j1) ≠ PB b’
    by (‘j1 < LENGTH g’ by simp[] >>
        drule_then (fn th => REWRITE_TAC[th]) Sj_SUC >>
        pop_assum kall_tac >> asm_rewrite_tac[] >>
        simp[pstep_def] >> every_case_tac >> simp[]) >>
  drule_then (qspecl_then [‘SUC j1’, ‘D’] mp_tac) (ok drain_after) >>
  simp[] >> strip_tac >> qexists_tac ‘j’ >> simp[]
QED

(* MAIN: the machine answers every complete request in D within 2K + 2
   rounds of round j0, given the four environment facts (see the header) *)
Theorem pmachine_live:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧
  j0 + 2 * LENGTH (proto_all P D) + 2 ≤ LENGTH g ∧
  Rj P resp fd g j0 ≼ D ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sj P resp fd g j = PA b ∧
         P.parse b = PIncomplete ∧ Readable fd ∉ (EL j g).ready ⇒
         D ≼ Rj P resp fd g j) ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sj P resp fd g j = PB b ⇒
         D ≼ Rj P resp fd g (SUC j)) ∧
  (∀j b. j0 ≤ j ∧ j ≤ LENGTH g ∧ Sj P resp fd g j = PD b ∧
         P.parse b = PIncomplete ⇒ D ≼ Rj P resp fd g j) ⇒
  ∃j. j ≤ j0 + 2 * LENGTH (proto_all P D) + 2 ∧
      proto_responses_to P resp D ≼ Wj P resp fd g j)
Proof
  DISCH_TAC >>
  strip_tac >> qabbrev_tac ‘NK = LENGTH (proto_all P D)’ >>
  drule_then (qspec_then ‘j0’ mp_tac) (ok pmachine_inv) >> simp[] >> strip_tac >>
  (* the requests completed by round j0 are among D's *)
  ‘rs ++ proto_all P (pbuf (Sj P resp fd g j0)) ≼ proto_all P D’
    by (‘proto_all P (Rj P resp fd g j0) ≼ proto_all P D’ by simp[pall_prefix] >>
        gvs[pall_print]) >>
  imp_res_tac IS_PREFIX_LENGTH >> gvs[] >>
  (* after a read at round j1 (state PB), drain_after finishes *)
  ‘∀j1 b1. j0 ≤ j1 ∧ j1 + 2 + NK ≤ LENGTH g ∧ Sj P resp fd g j1 = PB b1 ⇒
           ∃j. j ≤ j1 + 1 + NK ∧ proto_responses_to P resp D ≼ Wj P resp fd g j’
    by (rpt strip_tac >>
        ‘D ≼ Rj P resp fd g (SUC j1)’
          by (qpat_x_assum ‘∀j b. _ ∧ _ ∧ Sj _ _ _ _ _ = PB _ ⇒ _’
                (qspecl_then [‘j1’, ‘b1’] mp_tac) >> simp[]) >>
        ‘j1 + 2 + LENGTH (proto_all P D) ≤ LENGTH g’ by fs[Abbr ‘NK’] >>
        drule_all (ok after_read_live) >> strip_tac >>
        qexists_tac ‘j’ >> fs[Abbr ‘NK’]) >>
  Cases_on ‘Sj P resp fd g j0’ >> gvs[pbuf_def]
  (* waiting or answering, with buffer b *)
  >- (rename1 ‘prun P resp fd (PA "") (TAKE j0 g) = PA b’ >>
      drule_then (qspecl_then [‘LENGTH (proto_all P b)’, ‘j0’, ‘b’] mp_tac) (ok pdrain) >>
      simp[] >> strip_tac >>
      qabbrev_tac ‘j1 = j0 + LENGTH (proto_all P b)’ >>
      ‘proto_all P b' = []’
        by (qpat_x_assum ‘proto_all P b = _’ (fn th =>
              qpat_x_assum ‘LENGTH rq = _’ (mp_tac o REWRITE_RULE [th])) >>
            simp[]) >>
      (* LENGTH rq = LENGTH (proto_all P b) would make the simplifier loop *)
      qpat_x_assum ‘LENGTH rq = _’ kall_tac >>
      drule_then (qspec_then ‘j1’ mp_tac) (ok pmachine_inv) >>
      impl_tac >- fs[Abbr ‘j1’] >>
      qpat_x_assum ‘Sj _ _ _ _ j1 = _’ (fn th => simp[th, pbuf_def] >> assume_tac th) >>
      strip_tac >>
      ‘∀r rest. P.parse b' ≠ PComplete r rest’
        by (rpt strip_tac >> drule pall_complete >> simp[]) >>
      ‘FLAT (MAP P.print rs') ++ b' = FLAT (MAP P.print rs) ++ b’
        by metis_tac[] >>
      ‘rs' = rs ++ rq’
        by (qpat_x_assum ‘FLAT _ ++ b' = _’ (mp_tac o AP_TERM “proto_all P”) >>
            qpat_x_assum ‘EVERY _ rs'’ (fn th1 => qpat_x_assum ‘EVERY _ rs’ (fn th2 =>
              simp[th1, th2, pall_print] >> assume_tac th1 >> assume_tac th2)) >>
            qpat_x_assum ‘proto_all P b = _’ (fn th1 => qpat_x_assum ‘proto_all P b' = _’
              (fn th2 => simp[th1, th2]))) >>
      pop_assum SUBST_ALL_TAC >>
      qpat_x_assum ‘STRCAT (CONCAT (MAP _ (_ ++ _))) b' = _’ kall_tac >>
      Cases_on ‘P.parse b'’ >> gvs[]
      (* incomplete: either fd is not readable (all of D read), or a read *)
      >- (Cases_on ‘Readable fd ∈ (EL j1 g).ready’
          >- (‘Sj P resp fd g (SUC j1) = PB b'’ by simp[Sj_SUC, pstep_def, Abbr ‘j1’] >>
              Cases_on ‘LENGTH (proto_all P b) < NK’
              (* a read now, then drain_after *)
              >- (qpat_x_assum ‘∀j1 b1. _ ⇒ ∃j. _’ (qspecl_then [‘SUC j1’, ‘b'’] mp_tac) >>
                  impl_tac >- fs[Abbr ‘j1’] >> strip_tac >>
                  qexists_tac ‘j’ >> fs[Abbr ‘j1’])
              (* D's requests were all in hand at round j0: answered by j1 *)
              >> ‘rs ++ proto_all P b = proto_all P D’
                   by (irule (iffLR IS_PREFIX_LENGTH_ANTI) >> fs[Abbr ‘NK’]) >>
              qexists_tac ‘j1’ >> conj_tac >- fs[Abbr ‘j1’] >>
              qpat_x_assum ‘Wj _ _ _ _ j1 = _’ SUBST1_TAC >>
              qpat_x_assum ‘_ = proto_all P D’ (SUBST1_TAC o SYM) >> simp[])
          >> ‘D ≼ Rj P resp fd g j1’
               by (qpat_x_assum ‘∀j b. _ ∧ _ ∧ _ = PA _ ∧ _ ⇒ _’
                     (qspecl_then [‘j1’, ‘b'’] mp_tac) >>
                   impl_tac >- fs[Abbr ‘j1’] >> simp[]) >>
          qexists_tac ‘j1’ >> simp[Abbr ‘j1’] >>
          irule (ok responses_upto) >> fs[] >>
          qpat_x_assum ‘Rj _ _ _ _ (_ + _) = _’ (fn th =>
            qpat_x_assum ‘D ≼ _’ (mp_tac o REWRITE_RULE [th])) >>
          qpat_x_assum ‘b = _’ (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
          simp[])
      (* invalid: D's requests are exactly those already answered *)
      >> qexists_tac ‘j1’ >> conj_tac >- fs[Abbr ‘j1’] >>
      ‘proto_responses_to P resp D = MAP (resp) (rs ++ proto_all P b)’
        by (irule (ok responses_invalid) >> conj_tac >- fs[] >> qexists_tac ‘b'’ >> fs[]) >>
      qpat_x_assum ‘Wj _ _ _ _ j1 = _’ SUBST1_TAC >> pop_assum SUBST1_TAC >> simp[])
  (* reading this round *)
  >- (first_x_assum (qspecl_then [‘j0’, ‘s’] mp_tac) >> simp[] >>
      strip_tac >> qexists_tac ‘j’ >> simp[])
  (* stopped *)
  >> rename1 ‘prun P resp fd (PA "") (TAKE j0 g) = PD b’ >>
  Cases_on ‘P.parse b’ >> gvs[]
  >- (‘D ≼ Rj P resp fd g j0’ by (first_x_assum irule >> simp[]) >>
      qexists_tac ‘j0’ >> simp[] >>
      ‘proto_all P b = []’ by (irule proto_all_not_complete >> fs[]) >>
      ‘proto_responses_to P resp D ≼
         MAP (resp) rs ++ proto_responses_to P resp b ++
         ppend P resp (PD b)’ by (irule (ok responses_upto) >> simp[] >>
             qpat_x_assum ‘D ≼ _’ mp_tac >>
             qpat_x_assum ‘Rj _ _ _ _ _ = _’ (fn th => REWRITE_TAC [th])) >>
      gs[])
  >> qexists_tac ‘j0’ >> simp[] >>
  ‘proto_responses_to P resp D = MAP (resp) rs’
    by (irule (ok responses_invalid) >> fs[] >> metis_tac[]) >>
  simp[]
QED

(* What the handler has read only grows *)
Theorem Rj_SUC_prefix:
  prompt (pcomp P resp fd (PA "")) g ∧ j < LENGTH g ⇒
  Rj P resp fd g j ≼ Rj P resp fd g (SUC j)
Proof
  strip_tac >> drule_all pmachine_trans_SUC >> simp[] >> strip_tac >> simp[]
QED

(* If the handler has already read all of D by round j0, it answers D's
   requests within K + 1 rounds: it finishes a read in progress, then
   answers the buffered requests *)
Theorem pmachine_live_read:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧
  j0 + LENGTH (proto_all P D) + 2 ≤ LENGTH g ∧ D ≼ Rj P resp fd g j0 ⇒
  ∃j. j ≤ j0 + LENGTH (proto_all P D) + 1 ∧
      proto_responses_to P resp D ≼ Wj P resp fd g j)
Proof
  DISCH_TAC >>
  strip_tac >> Cases_on ‘∃b. Sj P resp fd g j0 = PB b’
  >- (fs[] >>
      ‘D ≼ Rj P resp fd g (SUC j0)’
        by (‘j0 < LENGTH g’ by fs[] >> drule_all Rj_SUC_prefix >>
            metis_tac[IS_PREFIX_TRANS]) >>
      mp_tac (Q.INST [‘j1’ |-> ‘j0’, ‘b1’ |-> ‘b’] (UNDISCH (SPEC_ALL after_read_live))) >>
      impl_tac >- fs[] >> strip_tac >> qexists_tac ‘j’ >> fs[])
  >> ‘∀b. Sj P resp fd g j0 ≠ PB b’ by metis_tac[] >>
  mp_tac (Q.INST [‘j2’ |-> ‘j0’] (UNDISCH (SPEC_ALL drain_after))) >>
  impl_tac >- fs[] >> strip_tac >> qexists_tac ‘j’ >> fs[]
QED

(* ------------------------------------------------------------------------
   Liveness with bounded reads
   ------------------------------------------------------------------------ *)

(* Stopped (or about to stop) on an invalid buffer: every complete request
   in D has been answered *)
Theorem stopped_invalid:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧ j ≤ LENGTH g ∧
  (Sj P resp fd g j = PA b ∨ Sj P resp fd g j = PD b) ∧
  P.parse b = PInvalid ∧ Rj P resp fd g j ≼ D ⇒
  proto_responses_to P resp D ≼ Wj P resp fd g j)
Proof
  DISCH_TAC >>
  strip_tac >> drule_then (qspec_then ‘j’ mp_tac) (ok pmachine_inv) >> simp[] >>
  strip_tac >> gvs[pbuf_def, ppend_def] >>
  ‘proto_responses_to P resp D = MAP (resp) rs’
    by (irule (ok responses_invalid) >> metis_tac[]) >>
  simp[]
QED

(* MAIN: machine-level liveness when a read may return only part of the
   unread data.  The environment facts:
   - what has been read and D are always comparable (both are prefixes of
     what has arrived);
   - waiting with an incomplete buffer while fd is not reported readable
     means everything (D in particular) has been read;
   - a read, unless D has been read already, reads all of D or reads
     something;
   - stopping at end-of-file means D has been read.
   Measure: m bounds how much of D is still unread at round j.  Each cycle
   (answer at most K buffered requests, wait one round, read) takes at most
   K + 3 rounds and either reads all of D or reads something. *)
Theorem pmachine_live_p:
  proto_ok P ⇒
  (prompt (pcomp P resp fd (PA "")) g ∧
  (∀j. j0 ≤ j ∧ j ≤ LENGTH g ⇒ Rj P resp fd g j ≼ D ∨ D ≼ Rj P resp fd g j) ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sj P resp fd g j = PA b ∧
         P.parse b = PIncomplete ∧ Readable fd ∉ (EL j g).ready ⇒
         D ≼ Rj P resp fd g j) ∧
  (∀j b. j0 ≤ j ∧ j < LENGTH g ∧ Sj P resp fd g j = PB b ∧
         ¬(D ≼ Rj P resp fd g j) ⇒
         D ≼ Rj P resp fd g (SUC j) ∨
         LENGTH (Rj P resp fd g j) < LENGTH (Rj P resp fd g (SUC j))) ∧
  (∀j b. j0 ≤ j ∧ j ≤ LENGTH g ∧ Sj P resp fd g j = PD b ∧
         P.parse b = PIncomplete ⇒ D ≼ Rj P resp fd g j) ⇒
  ∀m j. j0 ≤ j ∧ LENGTH D ≤ LENGTH (Rj P resp fd g j) + m ∧
        j + (m + 2) * (LENGTH (proto_all P D) + 3) ≤ LENGTH g ⇒
        ∃j'. j' ≤ LENGTH g ∧ proto_responses_to P resp D ≼ Wj P resp fd g j')
Proof
  DISCH_TAC >>
  strip_tac >> completeInduct_on ‘m’ >> rpt strip_tac >>
  qabbrev_tac ‘NK = LENGTH (proto_all P D)’ >>
  (* finishing: once all of D has been read, by round j1 *)
  ‘∀j1. j1 ≤ j + NK + 2 ∧ D ≼ Rj P resp fd g j1 ⇒
        ∃j'. j' ≤ LENGTH g ∧ proto_responses_to P resp D ≼ Wj P resp fd g j'’
    by (rpt strip_tac >>
        mp_tac (Q.INST [‘j0’ |-> ‘j1’] (UNDISCH (SPEC_ALL pmachine_live_read))) >>
        impl_tac >- (fs[Abbr ‘NK’] >> Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
        strip_tac >> qexists_tac ‘j'’ >> fs[Abbr ‘NK’] >>
        Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
  Cases_on ‘D ≼ Rj P resp fd g j’ >- (first_x_assum irule >> qexists_tac ‘j’ >> simp[]) >>
  ‘j ≤ LENGTH g’ by (Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
  ‘Rj P resp fd g j ≼ D’ by metis_tac[] >>
  ‘LENGTH (Rj P resp fd g j) < LENGTH D’
    by (CCONTR_TAC >> fs[NOT_LESS] >> metis_tac[IS_PREFIX_LENGTH_ANTI, IS_PREFIX_REFL,
                                                  IS_PREFIX_LENGTH, LESS_EQUAL_ANTISYM]) >>
  ‘0 < m’ by simp[] >>
  (* growing: a read at round j2 (state PB, j2 ≤ j + NK + 1) *)
  ‘∀j2 b2. j ≤ j2 ∧ j2 ≤ j + NK + 1 ∧ Sj P resp fd g j2 = PB b2 ∧
           Rj P resp fd g j2 = Rj P resp fd g j ⇒
           ∃j'. j' ≤ LENGTH g ∧ proto_responses_to P resp D ≼ Wj P resp fd g j'’
    by (rpt strip_tac >>
        ‘j2 < LENGTH g’ by (Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
        qpat_x_assum ‘∀j b. _ ∧ _ ∧ Sj _ _ _ _ _ = PB _ ∧ _ ⇒ _’
          (qspecl_then [‘j2’, ‘b2’] mp_tac) >>
        impl_tac >- simp[] >> strip_tac
        >- (qpat_x_assum ‘∀j1. _ ⇒ ∃j'. _’ irule >> qexists_tac ‘SUC j2’ >> simp[]) >>
        qpat_x_assum ‘∀m'. m' < m ⇒ _’ (qspec_then ‘m − 1’ mp_tac) >>
        impl_tac >- simp[] >>
        disch_then (qspec_then ‘SUC j2’ mp_tac) >> impl_tac
        >- (rpt conj_tac >- simp[] >- (qpat_x_assum ‘Rj _ _ _ _ j2 = _’ (fn th => fs[th])) >>
            Cases_on ‘m’ >> fs[MULT_CLAUSES, ADD1]) >>
        simp[]) >>
  Cases_on ‘Sj P resp fd g j’
  (* about to act on buffer b *)
  >- (rename1 ‘prun P resp fd (PA "") (TAKE j g) = PA b’ >>
      drule_then (qspec_then ‘j’ mp_tac) (ok pmachine_inv) >> simp[] >> strip_tac >>
      gvs[pbuf_def] >>
      ‘LENGTH (proto_all P b) ≤ NK’
        by (‘rs ++ proto_all P b ≼ proto_all P D’
              by (‘proto_all P (Rj P resp fd g j) ≼ proto_all P D’
                    by simp[pall_prefix] >> gvs[pall_print]) >>
            imp_res_tac IS_PREFIX_LENGTH >> fs[Abbr ‘NK’]) >>
      drule_then (qspecl_then [‘LENGTH (proto_all P b)’, ‘j’, ‘b’] mp_tac) (ok pdrain) >>
      impl_tac >- (simp[] >> Cases_on ‘m’ >> fs[MULT_CLAUSES]) >> strip_tac >>
      ‘proto_all P b' = []’
        by (qpat_x_assum ‘proto_all P b = _’ (fn th =>
              qpat_x_assum ‘LENGTH rq = _’ (mp_tac o REWRITE_RULE [th])) >>
            simp[]) >>
      qabbrev_tac ‘k = LENGTH (proto_all P b)’ >>
      (* these two would make the simplifier loop *)
      qpat_x_assum ‘LENGTH rq = _’ kall_tac >>
      qpat_x_assum ‘proto_all P b = _’ kall_tac >>
      ‘∀r rest. P.parse b' ≠ PComplete r rest’
        by (rpt strip_tac >> drule pall_complete >> simp[]) >>
      Cases_on ‘P.parse b'’ >> fs[]
      (* incomplete: wait for readiness, then read *)
      >- (‘j + k < LENGTH g’ by (Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
          Cases_on ‘Readable fd ∈ (EL (j + k) g).ready’
          >- (‘Sj P resp fd g (SUC (j + k)) = PB b'’
                by (drule_then (fn th => REWRITE_TAC[th]) Sj_SUC >>
                    simp[pstep_def]) >>
              ‘Rj P resp fd g (SUC (j + k)) = Rj P resp fd g j’
                by (drule_all Rj_Wj_SUC >> simp[]) >>
              first_x_assum irule >> qexists_tac ‘b'’ >> qexists_tac ‘SUC (j + k)’ >>
              simp[Abbr ‘k’]) >>
          qpat_x_assum ‘∀j b. _ ∧ _ ∧ _ = PA _ ∧ _ ⇒ _’
            (qspecl_then [‘j + k’, ‘b'’] mp_tac) >>
          simp[]) >>
      (* invalid: D's requests have been answered *)
      ‘j + k ≤ LENGTH g’ by (Cases_on ‘m’ >> fs[MULT_CLAUSES]) >>
      qexists_tac ‘j + k’ >> simp[] >>
      irule (ok stopped_invalid) >> metis_tac[])
  (* reading this round *)
  >- (rename1 ‘_ = PB b’ >>
      qpat_x_assum ‘∀j2 b2. _ ⇒ _’ (qspecl_then [‘j’, ‘b’] mp_tac) >> simp[])
  (* stopped: on end-of-file (then all of D was read), or on invalid input *)
  >> rename1 ‘_ = PD b’ >>
  drule_then (qspec_then ‘j’ mp_tac) (ok pmachine_inv) >> simp[] >> strip_tac >>
  Cases_on ‘P.parse b’
  >- metis_tac[]
  >- (qpat_x_assum ‘∀j b. _ ∧ _ ∧ _ = PD _ ∧ _ ⇒ _’ (qspecl_then [‘j’, ‘b’] mp_tac) >>
      simp[]) >>
  qexists_tac ‘j’ >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (ok stopped_invalid) >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Reading and end-of-file in the machine's transcript
   ------------------------------------------------------------------------ *)

(* In state PB the handler has a read of fd outstanding *)
Theorem pmachine_reading:
  prompt (pcomp P resp fd (PA "")) g ∧ j ≤ LENGTH g ∧ Sj P resp fd g j = PB b ⇒
  MEM (Read fd, NONE) (trans (pcomp P resp fd (PA "")) (TAKE j g))
Proof
  strip_tac >> drule_all pmachine_trans_TAKE >> disch_then SUBST1_TAC >>
  simp[MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> qexists_tac ‘j’ >>
  simp[pacts_def, zipr_def]
QED

(* The handler stops on a buffer that is not invalid only after reading
   end-of-file *)
Theorem pmachine_stopped_eof:
  ∀j b. j ≤ LENGTH g ∧ Sj P resp fd g j = PD b ∧ P.parse b ≠ PInvalid ⇒
        ∃i b'. i < j ∧ Sj P resp fd g i = PB b' ∧ oHD (EL i g).results = SOME Eof
Proof
  Induct >- simp[prun_def] >>
  rpt strip_tac >>
  ‘j < LENGTH g’ by simp[] >>
  qpat_x_assum ‘Sj _ _ _ _ (SUC j) = _’ mp_tac >>
  drule_then (fn th => REWRITE_TAC[th]) Sj_SUC >>
  Cases_on ‘Sj P resp fd g j’ >> simp[pstep_def]
  >- (every_case_tac >> simp[] >> strip_tac >> gvs[])
  >- (every_case_tac >> simp[] >> strip_tac >> gvs[] >>
      qexists_tac ‘j’ >> simp[])
  >> strip_tac >> gvs[] >>
  metis_tac[DECIDE “i < j ⇒ i < SUC j”]
QED

(* So its transcript has the read that returned end-of-file *)
Theorem pmachine_eof:
  prompt (pcomp P resp fd (PA "")) g ∧ j ≤ LENGTH g ∧
  Sj P resp fd g j = PD b ∧ P.parse b ≠ PInvalid ⇒
  MEM (Read fd, SOME Eof) (trans (pcomp P resp fd (PA "")) (TAKE j g))
Proof
  strip_tac >> drule_all pmachine_stopped_eof >> strip_tac >>
  drule_all pmachine_trans_TAKE >> disch_then SUBST1_TAC >>
  simp[MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >> qexists_tac ‘i’ >>
  simp[pacts_def, zipr_def]
QED

