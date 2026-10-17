(*
  Route (d), the run (design/46): the input and output invariants over
  the guarded run prounds_t, and the server's transcript.

  The transcript the server has seen after the rounds h is asyncTranscript's
  trans m h: each executed round's actions with their answers, then the
  actions of the round not executed yet (no answers).  Per round:
   - the handles the server is handed (haccepted) are L1's next handles,
     in order, so they are distinct;
   - per episode j, the input invariant (pround_in) and the output
     invariant (pround_out) relate the spec's bytes to the server's reads
     and writes through handle j.
*)
Theory honestEchoL0Run
Ancestors
  alist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out
  asyncCore asyncLevel1 asyncTranscript
Libs
  preamble

(* One action's handed-out handle *)
Theorem pdo_acc:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  (ps'.b.nxt = ps.b.nxt ∧ haccepted [(a, SOME r)] = [] ∨
   ps'.b.nxt = ps.b.nxt + 1 ∧ haccepted [(a, SOME r)] = [l1hdl lfd ps.b.nxt])
Proof
  Cases_on ‘a’ >>
  simp[pdo_def, haccepted_def] >> rw[] >> gvs[AllCaseEqs()] >>
  gvs[l1do_def, l1_close_def, forget_def, set_outbox_def, after_send_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), forget_def, set_outbox_def, set_inb_def, after_send_def] >>
  TRY (Cases_on ‘l0_res_of out’) >> gvs[after_send_def, set_outbox_def] >> rw[]
QED

(* A round's actions hand out L1's next handles, in order *)
Theorem pacts_acc:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    ps.b.nxt ≤ ps'.b.nxt ∧
    haccepted (ZIP (acts, MAP SOME rs)) =
      GENLIST (λi. l1hdl lfd (ps.b.nxt + i)) (ps'.b.nxt − ps.b.nxt)
Proof
  Induct >- simp[pacts_def, haccepted_def] >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 ‘pdo lfd (w, ps) a = SOME (r, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  first_x_assum drule >> strip_tac >>
  drule pdo_acc >> strip_tac >>
  ‘haccepted ((a, SOME r) :: ZIP (acts, MAP SOME rs')) =
   haccepted [(a, SOME r)] ++ haccepted (ZIP (acts, MAP SOME rs'))’
    by (‘(a, SOME r) :: ZIP (acts, MAP SOME rs') = [(a, SOME r)] ++ ZIP (acts, MAP SOME rs')’
          by simp[] >>
        pop_assum SUBST1_TAC >> rewrite_tac[haccepted_APPEND]) >>
  gvs[] >>
  TRY (‘ps'.b.nxt − ps.b.nxt = SUC (ps'.b.nxt − (ps.b.nxt + 1))’ by simp[] >>
       pop_assum (fn th => REWRITE_TAC [th]) >>
       simp[GENLIST_CONS, o_DEF, ADD1] >> NO_TAC)
QED

(* The executed rounds' transcript: each round's actions with the answers
   of the next snapshot *)
Definition texec_def:
  texec m h =
    FLAT (GENLIST (λi. ZIP (new_actions (log_of m) (TAKE i h), MAP SOME (EL i h).results))
                  (LENGTH h))
End

Theorem zipr_ZIP[local]:
  ∀as rs. LENGTH rs = LENGTH as ⇒ zipr as rs = ZIP (as, MAP SOME rs)
Proof
  Induct >> simp[zipr_def] >> Cases_on ‘rs’ >> simp[zipr_def]
QED

Theorem zipr_NIL[local]:
  ∀as. zipr as [] = MAP (λa. (a, NONE)) as
Proof
  Induct >> simp[zipr_def]
QED

(* The server's transcript: the executed rounds, then the round not yet
   executed, unanswered *)
Theorem trans_texec:
  (∀i. i < LENGTH h ⇒ LENGTH (EL i h).results = LENGTH (new_actions (log_of m) (TAKE i h))) ⇒
  trans m h = texec m h ++ MAP (λa. (a, NONE)) (new_actions (log_of m) h)
Proof
  rw[trans_def, texec_def, GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  ‘GENLIST (round_trans m h) (LENGTH h) =
   GENLIST (λi. ZIP (new_actions (log_of m) (TAKE i h), MAP SOME (EL i h).results))
           (LENGTH h)’
    by (irule GENLIST_CONG >> rw[round_trans_def, responses_at_def] >>
        irule zipr_ZIP >> simp[]) >>
  simp[round_trans_def, responses_at_def, zipr_NIL]
QED

Theorem hread_NONE[simp]:
  hread hd (MAP (λa. (a, NONE)) as) = []
Proof
  Induct_on ‘as’ >> fs[hread_def] >> Cases >> simp[]
QED

Theorem haccepted_NONE[simp]:
  haccepted (MAP (λa. (a, NONE)) as) = []
Proof
  Induct_on ‘as’ >> fs[haccepted_def] >> Cases >> simp[]
QED
