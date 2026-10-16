(*
  The Level 2 CF library, completed (design/33 §2.1): map2 and both2 in
  CakeML, and a representation of the declared events that both2 can meet.

  asyncL2BlkProg represents the declared events as the canonical list
  SET_TO_LIST E (EVLIST), so that its generic blocking loop's select
  events are a function of the model.  both2 cannot produce that list:
  it declares the concatenation of its sides' lists, and SET_TO_LIST of a
  union is not computable from them.  So here the events are any list
  whose set is the model's interest (EVSET); a loop that needs a
  canonical select set sorts it (the socket loop does, on fds).

  STEPI / COMPI are asyncL2BlkProg's STEPA2 / COMP2 with EVSET in place
  of EVLIST; every STEPA2 value is a STEPI value (STEPA2_IMP_STEPI), so
  the constructors' specs carry over (asyncL2LibSpec).
*)
Theory asyncL2LibProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncCfActModel asyncCfDet
  asyncCfActProg asyncL2BlkModel asyncL2BlkProg asyncL2BlkSpec ml_translator
  ListProg
Libs
  preamble ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncL2BlkSpec"

(* ------------------------------------------------------------------------
   The CakeML implementation
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun map2 f c =
    case c of (acts, s) =>
      case s of
        Done2 x => (acts, Done2 (f x))
      | Pending2 es k => (acts, Pending2 es (fn w => map2 f (k w)));

  fun both2 c1 c2 =
    case c1 of (acts1, s1) =>
    case c2 of (acts2, s2) =>
      let val acts = acts1 @ acts2 in
        case (s1, s2) of
          (Done2 x, Done2 y) => (acts, Done2 (x, y))
        | _ =>
          (acts, Pending2 (interest c1 @ interest c2) (fn w =>
             case w of (rdy, t, res) =>
               let
                 val k = List.length acts1
                 val c1' = poll2 c1 (rdy, t, List.take res k)
                 val c2' = poll2 c2 (rdy, t, List.drop res k)
               in both2 c1' c2' end))
      end;
End

(* ------------------------------------------------------------------------
   The representation
   ------------------------------------------------------------------------ *)

(* v is a CakeML list of the events of E, in any order, maybe repeated *)
Definition EVSET_def:
  EVSET EV E v ⇔ ∃l. LIST_TO_SET l = E ∧ LIST_TYPE EV l v
End

Theorem EVLIST_IMP_EVSET:
  EVLIST EV E v ⇒ EVSET EV E v
Proof
  rw[EVLIST_def, EVSET_def] >> metis_tac[SET_TO_LIST_INV]
QED

Theorem EVSET_FINITE:
  EVSET EV E v ⇒ FINITE E
Proof
  rw[EVSET_def] >> simp[FINITE_LIST_TO_SET]
QED

(* STEPI p ACT RES EV WORLD c s: as STEPA2, with the declared events
   represented by EVSET *)
CoInductive STEPI:
  (∀c A x xv. c.run = finished A x ∧ RES x xv ⇒
     STEPI p ACT RES EV WORLD c (Done2V xv)) ∧
  (∀c iv kv. (c.run []).result = NONE ∧ EVSET EV (c.interest []) iv ∧
     (∀w wv. WORLD w wv ⇒
        returns p kv [wv]
          (POLL_RESULT2 ACT (STEPI p ACT RES EV WORLD) (suspended2 c [w]))) ⇒
     STEPI p ACT RES EV WORLD c (Pending2V iv kv))
End

Definition COMPI_def:
  COMPI p ACT RES EV WORLD c v ⇔
    POLL_RESULT2 ACT (STEPI p ACT RES EV WORLD) c v
End

Theorem COMPI_eta:
  COMPI p ACT RES EV WORLD c = POLL_RESULT2 ACT (STEPI p ACT RES EV WORLD) c
Proof
  simp[FUN_EQ_THM, COMPI_def]
QED

Theorem STEPI_Pending:
  STEPI p ACT RES EV WORLD c (Pending2V iv kv) ⇔
    (c.run []).result = NONE ∧ EVSET EV (c.interest []) iv ∧
    ∀w wv. WORLD w wv ⇒
      returns p kv [wv] (COMPI p ACT RES EV WORLD (suspended2 c [w]))
Proof
  simp[Once STEPI_cases, COMPI_eta]
QED

Theorem STEPI_Done:
  STEPI p ACT RES EV WORLD c (Done2V xv) ⇔
    ∃A x. c.run = finished A x ∧ RES x xv
Proof
  simp[Once STEPI_cases]
QED

(* MAIN: the canonical representation is one of the representations *)
Theorem STEPA2_IMP_STEPI:
  STEPA2 p ACT RES EV WORLD c v ⇒ STEPI p ACT RES EV WORLD c v
Proof
  strip_tac >> irule STEPI_coind >>
  qexists_tac ‘STEPA2 p ACT RES EV WORLD’ >> simp[] >>
  rpt gen_tac >> simp[Once STEPA2_cases] >> rw[]
  >- metis_tac[]
  >- (simp[EVLIST_IMP_EVSET] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> irule returns_mono >>
      first_x_assum (irule_at Any) >> rpt strip_tac >>
      irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >> simp[])
QED

Theorem COMP2_IMP_COMPI:
  COMP2 p ACT RES EV WORLD c v ⇒ COMPI p ACT RES EV WORLD c v
Proof
  rw[COMP2_def, COMPI_def] >> irule POLL_RESULT2_mono >>
  first_x_assum (irule_at Any) >> metis_tac[STEPA2_IMP_STEPI]
QED

(* ------------------------------------------------------------------------
   Finite approximations and the limit lemma (as for STEPA2)
   ------------------------------------------------------------------------ *)

Definition STEPIn_def:
  (STEPIn p ACT RES EV WORLD 0 c v ⇔ T) ∧
  (STEPIn p ACT RES EV WORLD (SUC n) c v ⇔
     (∃A x xv. c.run = finished A x ∧ RES x xv ∧ v = Done2V xv) ∨
     (∃iv kv. (c.run []).result = NONE ∧ EVSET EV (c.interest []) iv ∧
              v = Pending2V iv kv ∧
              ∀w wv. WORLD w wv ⇒
                returns p kv [wv]
                  (POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n)
                     (suspended2 c [w]))))
End

Theorem STEPIn_0[simp]:
  STEPIn p ACT RES EV WORLD 0 c v
Proof
  simp[STEPIn_def]
QED

Theorem STEPI_IMP_STEPIn:
  ∀n c v. STEPI p ACT RES EV WORLD c v ⇒ STEPIn p ACT RES EV WORLD n c v
Proof
  Induct >> simp[STEPIn_def] >>
  rpt gen_tac >> simp[Once STEPI_cases] >> rw[]
  >- metis_tac[]
  >- (rpt strip_tac >> irule returns_mono >>
      qexists_tac ‘POLL_RESULT2 ACT (STEPI p ACT RES EV WORLD) (suspended2 c [w])’ >>
      simp[] >> rpt strip_tac >> irule POLL_RESULT2_mono >>
      first_x_assum (irule_at Any) >> simp[])
QED

Theorem STEPIn_IMP_STEPI:
  (∀n. STEPIn p ACT RES EV WORLD n c v) ⇒ STEPI p ACT RES EV WORLD c v
Proof
  strip_tac >> irule STEPI_coind >>
  qexists_tac ‘λc v. ∀n. STEPIn p ACT RES EV WORLD n c v’ >> simp[] >>
  rpt strip_tac >>
  first_assum (qspec_then ‘SUC 0’ mp_tac) >>
  simp_tac std_ss [STEPIn_def] >> strip_tac >> gvs[]
  >- metis_tac[]
  >- (rpt strip_tac >>
      ‘∀n. returns p kv [wv]
             (POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) (suspended2 a0 [w]))’
        by (gen_tac >>
            qpat_x_assum ‘∀n. STEPIn _ _ _ _ _ n a0 _’ (qspec_then ‘SUC n’ mp_tac) >>
            simp[STEPIn_def] >> metis_tac[]) >>
      qspecl_then [‘p’, ‘kv’, ‘wv’,
                   ‘λn. POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) (suspended2 a0 [w])’]
        mp_tac returns_forall >> simp[] >> strip_tac >>
      irule returns_mono >> first_x_assum (irule_at Any) >>
      simp[POLL_RESULT2_forall])
QED

Theorem app_COMPI_of_approx:
  args ≠ [] ∧
  (∀n. app p f args H
         (POSTv v. &POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) c v)) ⇒
  app (p:'ffi ffi_proj) f args H (POSTv v. &COMPI p ACT RES EV WORLD c v)
Proof
  strip_tac >> irule app_weaken >>
  qexists_tac ‘POSTv v. &(∀n. POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) c v)’ >>
  conj_tac
  >- (rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def,
         POSTv_cond, COMPI_def, POLL_RESULT2_forall] >>
      irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >>
      metis_tac[STEPIn_IMP_STEPI])
  >- (qspecl_then [‘p’, ‘λn. POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) c’,
                   ‘args’, ‘f’, ‘H’] mp_tac app_forall >> gvs[])
QED

Theorem COMPI_IMP_approx:
  COMPI p ACT RES EV WORLD c v ⇒
  POLL_RESULT2 ACT (STEPIn p ACT RES EV WORLD n) c v
Proof
  rw[COMPI_def] >> irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >>
  metis_tac[STEPI_IMP_STEPIn]
QED

(* Actions emitted before the first round change neither the residual nor
   the interest *)
Theorem STEPI_prepend2:
  STEPI p ACT RES EV WORLD g sv ⇒ STEPI p ACT RES EV WORLD (prepend2 A g) sv
Proof
  simp[Once STEPI_cases] >> rw[]
  >- (simp[STEPI_Done, prepend2_def, prepend_finished] >> metis_tac[])
  >- gvs[STEPI_Pending, COMPI_eta, suspended2_prepend2, prepend2_def]
QED
