(*
  Actions and responses in the CF refinement layer.

  The CakeML representation of a polled computation:

      datatype ('act, 'w, 'a) step =
          Done 'a
        | Pending ('w -> 'act list * ('act, 'w, 'a) step)

  A computation value is a pair (acts, s): the actions it emits in its
  current round, and its residual s.  Polling a Pending k with the next
  snapshot w calls k w, which returns the next round's (acts, residual).
  return, wait, never, emit, bind and poll are plain CakeML functions, with
  no refs.

  A snapshot is a CakeML triple (ready, now, results), matching the model's
  snapshot record; results are the responses to the previous round's
  actions, in emission order (positional routing, as in the model).

  We relate these values to the HOL model of async/model (the real
  definitions: wait, emit, bind, suspended, finished) by a coinductive
  predicate STEPA, and prove CF specs for all six functions.
  See async/design/05-cf-actions.md.
*)
Theory libProg
Ancestors
  asyncCore asyncLevel1 asyncChoose libModel libDet
  ml_translator basisProg[qualified]
Libs
  preamble ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "basisProg"

(* ------------------------------------------------------------------------
   The CakeML implementation
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  datatype ('act, 'w, 'a) step =
      Done 'a
    | Pending ('w -> 'act list * ('act, 'w, 'a) step)
End

(* The constructor stamps of Done and Pending, read off the program state *)
local
  val env = get_env (get_ml_prog_state ())
  fun stamp_of c =
    EVAL “nsLookup (^env).c (Short ^c)” |> concl |> rhs
    |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
in
  val done_stamp = stamp_of “«Done»”
  val pending_stamp = stamp_of “«Pending»”
end

(* DoneV xv is the CakeML value Done xv; PendingV kv is Pending kv *)
Overload DoneV = “λxv. Conv (SOME ^done_stamp) [xv]”
Overload PendingV = “λkv. Conv (SOME ^pending_stamp) [kv]”

Quote add_cakeml:
  fun return x = ([], Done x);

  fun poll c w =
    case c of (acts, s) =>
      case s of Done x => ([], s) | Pending k => k w;

  fun wait p =
    ([], Pending (fn w => case p w of Some a => ([], Done a) | None => wait p));

  fun never u = wait (fn w => None);

  fun emit a =
    ([a], Pending (fn w =>
       case w of (rdy, t, res) =>
         case res of [] => never () | r :: rs => ([], Done r)));

  fun skip k s =
    case s of
      Done x => s
    | Pending g =>
        Pending (fn w => case w of (rdy, t, res) => g (rdy, t, List.drop res k));

  fun bind c f =
    case c of (acts, s) =>
      case s of
        Done x =>
          (case f x of (acts2, s2) => (acts @ acts2, skip (List.length acts) s2))
      | Pending k => (acts, Pending (fn w => bind (k w) f));
End

(* ------------------------------------------------------------------------
   The representation predicates
   ------------------------------------------------------------------------ *)

(* returns p f args R: calling closure f on args terminates normally with a
   value satisfying R, from the empty heap and keeping no heap (f is pure). *)
Definition returns_def:
  returns (p:'ffi ffi_proj) f args R ⇔ app p f args emp (POSTv v. &R v)
End

Theorem returns_mono[mono]:
  (∀v. R1 v ⇒ R2 v) ⇒ returns p f args R1 ⇒ returns p f args R2
Proof
  rw[returns_def] >> irule app_weaken >> first_x_assum (irule_at Any) >>
  rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def,
     POSTv_cond] >>
  metis_tac[]
QED

(* SNAPSHOT READY R s v: v is the CakeML triple (ready, now, results) for
   the model snapshot s.  The representation of the ready set is left to
   READY; the responses are a list of values related by R. *)
Definition SNAPSHOT_def:
  SNAPSHOT READY R (s : ('e,'r) snapshot) v ⇔
    ∃rv nv resv. v = Conv NONE [rv; nv; resv] ∧ READY s.ready rv ∧
                 NUM s.now nv ∧ LIST_TYPE R s.results resv
End

(* POLL_RESULT ACT RESID m v: v is a pair (acts, s) where acts are the
   actions m emits in its first round and the residual s satisfies RESID m. *)
Definition POLL_RESULT_def:
  POLL_RESULT ACT RESID m v ⇔
    ∃av sv. v = Conv NONE [av; sv] ∧ LIST_TYPE ACT (m []).actions av ∧
            RESID m sv
End

Theorem POLL_RESULT_mono[mono]:
  (∀m v. R1 m v ⇒ R2 m v) ⇒ POLL_RESULT ACT R1 m v ⇒ POLL_RESULT ACT R2 m v
Proof
  rw[POLL_RESULT_def] >> metis_tac[]
QED

(* STEPA p ACT RES WORLD m s: the residual s implements the model
   computation m (from its first round on, whose actions are carried
   separately, see COMP below).  ACT, RES and WORLD relate actions, results
   and snapshots to CakeML values.
   - Done xv implements m if m has finished with some x that xv represents
     (whatever actions it emitted in its first round);
   - Pending kv implements m if m has not finished in its first round, and
     for every snapshot w, kv w returns the next round's actions together
     with a residual implementing m with w delivered (suspended m [w]).
   Coinductive, because a computation may stay pending forever. *)
CoInductive STEPA:
  (∀m A x xv. m = finished A x ∧ RES x xv ⇒
     STEPA p ACT RES WORLD m (DoneV xv)) ∧
  (∀m kv. (m []).result = NONE ∧
     (∀w wv. WORLD w wv ⇒
        returns p kv [wv]
          (POLL_RESULT ACT (STEPA p ACT RES WORLD) (suspended m [w]))) ⇒
     STEPA p ACT RES WORLD m (PendingV kv))
End

(* COMP p ACT RES WORLD m v: the CakeML pair v = (acts, s) implements the
   model computation m: acts are the actions m emits in its first round
   ((m []).actions) and s implements the rest. *)
Definition COMP_def:
  COMP p ACT RES WORLD m v ⇔ POLL_RESULT ACT (STEPA p ACT RES WORLD) m v
End

Theorem COMP_eta:
  COMP p ACT RES WORLD m = POLL_RESULT ACT (STEPA p ACT RES WORLD) m
Proof
  simp[FUN_EQ_THM, COMP_def]
QED

(* The Pending case of STEPA, in terms of COMP *)
Theorem STEPA_Pending:
  STEPA p ACT RES WORLD m (PendingV kv) ⇔
    (m []).result = NONE ∧
    ∀w wv. WORLD w wv ⇒
      returns p kv [wv] (COMP p ACT RES WORLD (suspended m [w]))
Proof
  simp[Once STEPA_cases, COMP_eta]
QED

Theorem STEPA_Done:
  STEPA p ACT RES WORLD m (DoneV xv) ⇔ ∃A x. m = finished A x ∧ RES x xv
Proof
  simp[Once STEPA_cases]
QED

(* ------------------------------------------------------------------------
   Proof technique: finite approximations of STEPA (as for STEP in
   async/cf-spike), and the packaged limit lemma.
   ------------------------------------------------------------------------ *)

Definition STEPAn_def:
  (STEPAn p ACT RES WORLD 0 m v ⇔ T) ∧
  (STEPAn p ACT RES WORLD (SUC n) m v ⇔
     (∃A x xv. m = finished A x ∧ RES x xv ∧ v = DoneV xv) ∨
     (∃kv. (m []).result = NONE ∧ v = PendingV kv ∧
           ∀w wv. WORLD w wv ⇒
             returns p kv [wv]
               (POLL_RESULT ACT (STEPAn p ACT RES WORLD n) (suspended m [w]))))
End

Theorem STEPAn_0[simp]:
  STEPAn p ACT RES WORLD 0 m v
Proof
  simp[STEPAn_def]
QED

Theorem returns_forall:
  ∀p f x P.
    (∀i. returns p f [x] (P i)) ⇒ returns p f [x] (λv. ∀i. P i v)
Proof
  rw[returns_def, app_def] >> irule app_basic_forall >> simp[]
QED

(* The pair decomposition is unique, so POLL_RESULT commutes with ∀ *)
Theorem POLL_RESULT_forall:
  (∀n. POLL_RESULT ACT (R n) m v) ⇔ POLL_RESULT ACT (λm v. ∀n. R n m v) m v
Proof
  simp[POLL_RESULT_def] >> eq_tac >> rw[] >>
  ‘∃av sv. v = Conv NONE [av; sv]’ by metis_tac[] >> gvs[] >> metis_tac[]
QED

Theorem STEPA_IMP_STEPAn:
  ∀n m v. STEPA p ACT RES WORLD m v ⇒ STEPAn p ACT RES WORLD n m v
Proof
  Induct >> simp[STEPAn_def] >>
  rpt gen_tac >> simp[Once STEPA_cases] >> rw[]
  >- metis_tac[]
  >- (rpt strip_tac >> irule returns_mono >>
      qexists_tac ‘POLL_RESULT ACT (STEPA p ACT RES WORLD) (suspended m [w])’ >>
      simp[] >> rpt strip_tac >> irule POLL_RESULT_mono >>
      first_x_assum (irule_at Any) >> simp[])
QED

Theorem STEPAn_IMP_STEPA:
  (∀n. STEPAn p ACT RES WORLD n m v) ⇒ STEPA p ACT RES WORLD m v
Proof
  strip_tac >> irule STEPA_coind >>
  qexists_tac ‘λm v. ∀n. STEPAn p ACT RES WORLD n m v’ >> simp[] >>
  rpt strip_tac >>
  first_assum (qspec_then ‘SUC 0’ mp_tac) >>
  simp_tac std_ss [STEPAn_def] >> strip_tac >> gvs[]
  >- metis_tac[]
  >- (rpt strip_tac >>
      ‘∀n. returns p kv [wv]
             (POLL_RESULT ACT (STEPAn p ACT RES WORLD n) (suspended a0 [w]))’
        by (gen_tac >>
            qpat_x_assum ‘∀n. STEPAn _ _ _ _ n a0 _’ (qspec_then ‘SUC n’ mp_tac) >>
            simp[STEPAn_def] >> metis_tac[]) >>
      qspecl_then [‘p’, ‘kv’, ‘wv’,
                   ‘λn. POLL_RESULT ACT (STEPAn p ACT RES WORLD n) (suspended a0 [w])’]
        mp_tac returns_forall >> simp[] >> strip_tac >>
      irule returns_mono >> first_x_assum (irule_at Any) >>
      simp[POLL_RESULT_forall])
QED

(* The packaged limit argument: to prove a COMP spec, prove for every n
   that the call returns a pair whose residual satisfies the n-th
   approximation. *)
Theorem app_COMP_of_approx:
  args ≠ [] ∧
  (∀n. app p f args H (POSTv v. &POLL_RESULT ACT (STEPAn p ACT RES WORLD n) m v)) ⇒
  app (p:'ffi ffi_proj) f args H (POSTv v. &COMP p ACT RES WORLD m v)
Proof
  strip_tac >> irule app_weaken >>
  qexists_tac ‘POSTv v. &(∀n. POLL_RESULT ACT (STEPAn p ACT RES WORLD n) m v)’ >>
  conj_tac
  >- (rw[cfHeapsBaseTheory.SEP_IMPPOST_def, set_sepTheory.SEP_IMP_def,
         POSTv_cond, COMP_def, POLL_RESULT_forall] >>
      irule POLL_RESULT_mono >> first_x_assum (irule_at Any) >>
      metis_tac[STEPAn_IMP_STEPA])
  >- (qspecl_then [‘p’, ‘λn. POLL_RESULT ACT (STEPAn p ACT RES WORLD n) m’,
                   ‘args’, ‘f’, ‘H’] mp_tac app_forall >> gvs[])
QED

Theorem COMP_IMP_approx:
  COMP p ACT RES WORLD m v ⇒ POLL_RESULT ACT (STEPAn p ACT RES WORLD n) m v
Proof
  rw[COMP_def] >> irule POLL_RESULT_mono >> first_x_assum (irule_at Any) >>
  metis_tac[STEPA_IMP_STEPAn]
QED

(* ------------------------------------------------------------------------
   Pure facts about STEPA used by bind
   ------------------------------------------------------------------------ *)

(* Actions emitted before the first round don't change the residual *)
Theorem STEPA_prepend:
  STEPA p ACT RES WORLD g sv ⇒ STEPA p ACT RES WORLD (prepend A g) sv
Proof
  simp[Once STEPA_cases] >> rw[]
  >- (simp[STEPA_Done, prepend_finished] >> metis_tac[])
  >- gvs[STEPA_Pending, COMP_eta, suspended_prepend]
QED
