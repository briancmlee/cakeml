(*
  Option C: the Level 2 CF library, replayed into the socket program's
  translation chain (after cf-actions' asyncProtoProg), so that the Level 2
  protocol server can be one CakeML program with the socket loop.

  The code is asyncL2BlkProg's (step2, return2, poll2, interest, wait_on,
  never2, emit2, skip2, bind2) and cakeml/level2's map2 and both2; the
  representation is cakeml/level2's: the declared events are any list
  of the interest (EVSET), STEPI/COMPI.  See cakeml/level2/asyncL2LibProg
  for the rationale.
*)
Theory asyncOCProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 asyncCfActModel
  asyncCfActProg asyncCfDet asyncOCModel asyncProtoProg ml_translator ListProg
Libs
  preamble ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncProtoProg"

(* ------------------------------------------------------------------------
   The CakeML implementation
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  datatype ('act, 'e, 'w, 'a) step2 =
      Done2 'a
    | Pending2 ('e list) ('w -> 'act list * ('act, 'e, 'w, 'a) step2)
End

local
  val env = get_env (get_ml_prog_state ())
  fun stamp_of c =
    EVAL “nsLookup (^env).c (Short ^c)” |> concl |> rhs
    |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
in
  val done2_stamp = stamp_of “«Done2»”
  val pending2_stamp = stamp_of “«Pending2»”
end

Overload Done2V = “λxv. Conv (SOME ^done2_stamp) [xv]”
Overload Pending2V = “λiv kv. Conv (SOME ^pending2_stamp) [iv; kv]”

Quote add_cakeml:
  fun return2 x = ([], Done2 x);

  fun poll2 c w =
    case c of (acts, s) =>
      case s of Done2 x => ([], s) | Pending2 es k => k w;

  fun interest c =
    case c of (acts, s) =>
      case s of Done2 x => [] | Pending2 es k => es;

  fun wait_on e q =
    ([], Pending2 [e] (fn w => case q w of Some a => ([], Done2 a)
                                         | None => wait_on e q));

  fun never2 u = ([], Pending2 [] (fn w => never2 ()));

  fun emit2 a =
    ([a], Pending2 [] (fn w =>
       case w of (rdy, t, res) =>
         case res of [] => never2 () | r :: rs => ([], Done2 r)));

  fun skip2 k s =
    case s of
      Done2 x => s
    | Pending2 es g =>
        Pending2 es (fn w => case w of (rdy, t, res) => g (rdy, t, List.drop res k));

  fun bind2 c f =
    case c of (acts, s) =>
      case s of
        Done2 x =>
          (case f x of (acts2, s2) => (acts @ acts2, skip2 (List.length acts) s2))
      | Pending2 es k => (acts, Pending2 es (fn w => bind2 (k w) f));
End

(* ------------------------------------------------------------------------
   The representation predicates
   ------------------------------------------------------------------------ *)

(* v is a pair (acts, s): acts are c's first-round actions, RESID c s *)
Definition POLL_RESULT2_def:
  POLL_RESULT2 ACT RESID c v ⇔
    ∃av sv. v = Conv NONE [av; sv] ∧ LIST_TYPE ACT (c.run []).actions av ∧
            RESID c sv
End

Theorem POLL_RESULT2_mono[mono]:
  (∀c v. R1 c v ⇒ R2 c v) ⇒ POLL_RESULT2 ACT R1 c v ⇒ POLL_RESULT2 ACT R2 c v
Proof
  rw[POLL_RESULT2_def] >> metis_tac[]
QED



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

Theorem POLL_RESULT2_forall:
  (∀n. POLL_RESULT2 ACT (R n) c v) ⇔ POLL_RESULT2 ACT (λc v. ∀n. R n c v) c v
Proof
  simp[POLL_RESULT2_def] >> eq_tac >> rw[] >>
  ‘∃av sv. v = Conv NONE [av; sv]’ by metis_tac[] >> gvs[] >> metis_tac[]
QED


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
