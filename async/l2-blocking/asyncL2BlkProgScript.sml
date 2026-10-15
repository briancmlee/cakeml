(*
  Level 2 (declared interest) in the CF refinement layer.

  The CakeML representation of cf-actions (async/cf-actions), with the
  pending case also exposing what the computation is waiting for:

      datatype ('act, 'e, 'w, 'a) step2 =
          Done2 'a
        | Pending2 ('e list) ('w -> 'act list * ('act, 'e, 'w, 'a) step2)

  A computation value is a pair (acts, s), as at Level 1.  Pending2 es k
  declares the events es: the computation makes no progress, now or
  later, on a snapshot in which none of them is ready (and no response is
  due) -- the model's `quiet`.  An event loop can therefore block (e.g. in
  select) on the union of the declared events instead of polling every
  round (async/model/asyncSched2Script.sml, no_busy_waiting).

  STEPA2 relates these values to the model's Level 2 computations comp2
  (async/model/asyncLevel2Script.sml): the run part as STEPA does, and the
  declared events to the model's interest, at every round.
  See async/design/14-l2-blocking.md.
*)
Theory asyncL2BlkProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncCfActModel asyncCfDet
  asyncCfActProg asyncL2BlkModel ml_translator
Libs
  preamble ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncCfActProg"

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

(* EVLIST EV E v: v is a CakeML list whose elements represent exactly the
   events of the set E *)
Definition EVLIST_def:
  EVLIST EV E v ⇔ ∃l. LIST_TYPE EV l v ∧ LIST_TO_SET l = E
End

(* STEPA2 p ACT RES EV WORLD c s: the residual s implements the Level 2
   computation c.
   - Done2 xv: c has finished with some x that xv represents;
   - Pending2 iv kv: c has not finished, iv lists exactly the events c
     declares (c.interest []), and for every snapshot w, kv w returns the
     next round's actions with a residual implementing c with w delivered
     (suspended2 c [w], whose interest is c's on the longer history). *)
CoInductive STEPA2:
  (∀c A x xv. c.run = finished A x ∧ RES x xv ⇒
     STEPA2 p ACT RES EV WORLD c (Done2V xv)) ∧
  (∀c iv kv. (c.run []).result = NONE ∧ EVLIST EV (c.interest []) iv ∧
     (∀w wv. WORLD w wv ⇒
        returns p kv [wv]
          (POLL_RESULT2 ACT (STEPA2 p ACT RES EV WORLD) (suspended2 c [w]))) ⇒
     STEPA2 p ACT RES EV WORLD c (Pending2V iv kv))
End

Definition COMP2_def:
  COMP2 p ACT RES EV WORLD c v ⇔
    POLL_RESULT2 ACT (STEPA2 p ACT RES EV WORLD) c v
End

Theorem COMP2_eta:
  COMP2 p ACT RES EV WORLD c = POLL_RESULT2 ACT (STEPA2 p ACT RES EV WORLD) c
Proof
  simp[FUN_EQ_THM, COMP2_def]
QED

Theorem STEPA2_Pending:
  STEPA2 p ACT RES EV WORLD c (Pending2V iv kv) ⇔
    (c.run []).result = NONE ∧ EVLIST EV (c.interest []) iv ∧
    ∀w wv. WORLD w wv ⇒
      returns p kv [wv] (COMP2 p ACT RES EV WORLD (suspended2 c [w]))
Proof
  simp[Once STEPA2_cases, COMP2_eta]
QED

Theorem STEPA2_Done:
  STEPA2 p ACT RES EV WORLD c (Done2V xv) ⇔
    ∃A x. c.run = finished A x ∧ RES x xv
Proof
  simp[Once STEPA2_cases]
QED

(* ------------------------------------------------------------------------
   Finite approximations and the limit lemma (as for STEPA)
   ------------------------------------------------------------------------ *)

Definition STEPA2n_def:
  (STEPA2n p ACT RES EV WORLD 0 c v ⇔ T) ∧
  (STEPA2n p ACT RES EV WORLD (SUC n) c v ⇔
     (∃A x xv. c.run = finished A x ∧ RES x xv ∧ v = Done2V xv) ∨
     (∃iv kv. (c.run []).result = NONE ∧ EVLIST EV (c.interest []) iv ∧
              v = Pending2V iv kv ∧
              ∀w wv. WORLD w wv ⇒
                returns p kv [wv]
                  (POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n)
                     (suspended2 c [w]))))
End

Theorem STEPA2n_0[simp]:
  STEPA2n p ACT RES EV WORLD 0 c v
Proof
  simp[STEPA2n_def]
QED

Theorem POLL_RESULT2_forall:
  (∀n. POLL_RESULT2 ACT (R n) c v) ⇔ POLL_RESULT2 ACT (λc v. ∀n. R n c v) c v
Proof
  simp[POLL_RESULT2_def] >> eq_tac >> rw[] >>
  ‘∃av sv. v = Conv NONE [av; sv]’ by metis_tac[] >> gvs[] >> metis_tac[]
QED

Theorem STEPA2_IMP_STEPA2n:
  ∀n c v. STEPA2 p ACT RES EV WORLD c v ⇒ STEPA2n p ACT RES EV WORLD n c v
Proof
  Induct >> simp[STEPA2n_def] >>
  rpt gen_tac >> simp[Once STEPA2_cases] >> rw[]
  >- metis_tac[]
  >- (rpt strip_tac >> irule returns_mono >>
      qexists_tac ‘POLL_RESULT2 ACT (STEPA2 p ACT RES EV WORLD) (suspended2 c [w])’ >>
      simp[] >> rpt strip_tac >> irule POLL_RESULT2_mono >>
      first_x_assum (irule_at Any) >> simp[])
QED

Theorem STEPA2n_IMP_STEPA2:
  (∀n. STEPA2n p ACT RES EV WORLD n c v) ⇒ STEPA2 p ACT RES EV WORLD c v
Proof
  strip_tac >> irule STEPA2_coind >>
  qexists_tac ‘λc v. ∀n. STEPA2n p ACT RES EV WORLD n c v’ >> simp[] >>
  rpt strip_tac >>
  first_assum (qspec_then ‘SUC 0’ mp_tac) >>
  simp_tac std_ss [STEPA2n_def] >> strip_tac >> gvs[]
  >- metis_tac[]
  >- (rpt strip_tac >>
      ‘∀n. returns p kv [wv]
             (POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) (suspended2 a0 [w]))’
        by (gen_tac >>
            qpat_x_assum ‘∀n. STEPA2n _ _ _ _ _ n a0 _’ (qspec_then ‘SUC n’ mp_tac) >>
            simp[STEPA2n_def] >> metis_tac[]) >>
      qspecl_then [‘p’, ‘kv’, ‘wv’,
                   ‘λn. POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) (suspended2 a0 [w])’]
        mp_tac returns_forall >> simp[] >> strip_tac >>
      irule returns_mono >> first_x_assum (irule_at Any) >>
      simp[POLL_RESULT2_forall])
QED

Theorem app_COMP2_of_approx:
  args ≠ [] ∧
  (∀n. app p f args H
         (POSTv v. &POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) c v)) ⇒
  app (p:'ffi ffi_proj) f args H (POSTv v. &COMP2 p ACT RES EV WORLD c v)
Proof
  strip_tac >> irule app_weaken >>
  qexists_tac ‘POSTv v. &(∀n. POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) c v)’ >>
  conj_tac
  >- (rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def,
         POSTv_cond, COMP2_def, POLL_RESULT2_forall] >>
      irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >>
      metis_tac[STEPA2n_IMP_STEPA2])
  >- (qspecl_then [‘p’, ‘λn. POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) c’,
                   ‘args’, ‘f’, ‘H’] mp_tac app_forall >> gvs[])
QED

Theorem COMP2_IMP_approx:
  COMP2 p ACT RES EV WORLD c v ⇒
  POLL_RESULT2 ACT (STEPA2n p ACT RES EV WORLD n) c v
Proof
  rw[COMP2_def] >> irule POLL_RESULT2_mono >> first_x_assum (irule_at Any) >>
  metis_tac[STEPA2_IMP_STEPA2n]
QED

(* Actions emitted before the first round change neither the residual nor
   the interest *)
Theorem STEPA2_prepend2:
  STEPA2 p ACT RES EV WORLD g sv ⇒ STEPA2 p ACT RES EV WORLD (prepend2 A g) sv
Proof
  simp[Once STEPA2_cases] >> rw[]
  >- (simp[STEPA2_Done, prepend2_def, prepend_finished] >> metis_tac[])
  >- gvs[STEPA2_Pending, COMP2_eta, suspended2_prepend2, prepend2_def]
QED
