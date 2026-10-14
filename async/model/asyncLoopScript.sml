(*
  The recursion rule: which recursive definitions of computations are
  well-defined.

  asyncCore defines fix body, the unique solution of r = body r, for any
  *contractive* body: one that, to compute r's behaviour on histories of
  length n, only needs r on histories shorter than n.  This theory shows how
  to establish contractiveness from the shape of the body:

   - every combinator (bind, map, both) is non-expansive: it never looks at
     its arguments on histories longer than its own;
   - bind m (λx. ... r ...) is *guarded* when m needs a snapshot before it
     can finish ((m []).result = NONE), e.g. m = wait p or m = emit a.  The
     continuation then only ever sees strictly shorter histories.

  So: a recursive call is allowed anywhere after a wait or an emit.  This is
  the rule "each iteration of a loop uses up at least one snapshot".
*)
Theory asyncLoop
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Agreement: bind, map and both only look at shorter histories
   ------------------------------------------------------------------------ *)

Theorem log_of_agree[local]:
  agree_below n m m' ∧ LENGTH h < n ⇒
  ∀p. LENGTH p ≤ LENGTH h ⇒ log_of m p = log_of m' p
Proof
  rw[agree_below_def, log_of_def]
QED

Theorem bind_agree:
  agree_below n m m' ∧ (∀x. agree_below n (f x) (f' x)) ⇒
  agree_below n (bind m f) (bind m' f')
Proof
  rw[agree_below_def] >> simp[bind_def]
  >> ‘first_prefix (λp. (m p).result ≠ NONE) h =
      first_prefix (λp. (m' p).result ≠ NONE) h’
       by (irule first_prefix_cong >> rw[] >> simp[LENGTH_TAKE_EQ] >> rw[])
  >> simp[] >> CASE_TAC >> simp[]
  >> rename1 ‘TAKE j h’
  >> ‘j ≤ LENGTH h’ by fs[first_prefix_SOME]
  >> ‘m (TAKE j h) = m' (TAKE j h)’ by simp[]
  >> ‘new_actions (log_of m) (TAKE j h) = new_actions (log_of m') (TAKE j h)’
       by (irule new_actions_cong >> rw[log_of_def])
  >> simp[]
QED

(* If m needs a snapshot to finish, the continuation of bind m f only ever
   sees histories strictly shorter than bind's own *)
Theorem bind_agree_guarded:
  (m []).result = NONE ∧ (∀x. agree_below n (f x) (f' x)) ⇒
  agree_below (n + 1) (bind m f) (bind m f')
Proof
  rw[agree_below_def] >> simp[bind_def]
  >> CASE_TAC >> simp[]
  >> rename1 ‘TAKE j h’
  >> ‘j ≠ 0’ by (strip_tac >> gvs[first_prefix_SOME])
  >> ‘j ≤ LENGTH h’ by fs[first_prefix_SOME]
  >> simp[]
QED

Theorem map_agree:
  agree_below n m m' ⇒ agree_below n (map f m) (map f m')
Proof
  rw[agree_below_def, map_def]
QED

Theorem both_agree:
  agree_below n m1 m1' ∧ agree_below n m2 m2' ⇒
  agree_below n (both m1 m2) (both m1' m2')
Proof
  rw[agree_below_def] >> simp[both_def, par_log_def, left_view_def, right_view_def]
  >> ‘par_views (log_of m1) (log_of m2) h = par_views (log_of m1') (log_of m2') h’
       by (irule par_views_cong >> rw[log_of_def])
  >> ‘par_actions (log_of m1) (log_of m2) h = par_actions (log_of m1') (log_of m2') h’
       by (irule par_actions_cong >> rw[log_of_def])
  >> simp[]
  >> ‘LENGTH (FST (par_views (log_of m1') (log_of m2') h)) = LENGTH h ∧
      LENGTH (SND (par_views (log_of m1') (log_of m2') h)) = LENGTH h’
       by simp[LENGTH_par_views]
  >> simp[]
QED

(* ------------------------------------------------------------------------
   Non-expansive and guarded bodies
   ------------------------------------------------------------------------ *)

Theorem nonexpansive_bind:
  nonexpansive (λr. M r) ∧ (∀x. nonexpansive (λr. G x r)) ⇒
  nonexpansive (λr. bind (M r) (λx. G x r))
Proof
  rw[nonexpansive_def] >> irule bind_agree >> simp[]
QED

Theorem nonexpansive_map:
  nonexpansive (λr. M r) ⇒ nonexpansive (λr. map f (M r))
Proof
  rw[nonexpansive_def] >> irule map_agree >> simp[]
QED

Theorem nonexpansive_both:
  nonexpansive (λr. M1 r) ∧ nonexpansive (λr. M2 r) ⇒
  nonexpansive (λr. both (M1 r) (M2 r))
Proof
  rw[nonexpansive_def] >> irule both_agree >> simp[]
QED

(* MAIN: the recursion rule.  A recursive call may appear anywhere in the
   continuation of a computation that needs a snapshot to finish (a wait or
   an emit, for example). *)
Theorem guarded_bind:
  (m []).result = NONE ∧ (∀x. nonexpansive (λr. G x r)) ⇒
  guarded (λr. bind m (λx. G x r))
Proof
  rw[guarded_def, nonexpansive_def] >> irule bind_agree_guarded >> simp[]
QED

(* Once guarded, always guarded: guardedness passes through the
   continuation of any bind *)
Theorem guarded_bind_continuation:
  (∀x. guarded (λr. G x r)) ⇒ guarded (λr. bind m (λx. G x r))
Proof
  rw[guarded_def] >> irule bind_agree >> simp[]
QED

(* MAIN: settledness of guarded recursive definitions *)
Theorem settled_fix:
  contractive body ∧ (∀r. (∀p. settled (r p)) ⇒ ∀p. settled (body r p)) ⇒
  ∀p. settled (fix body p)
Proof
  strip_tac >> irule fix_preserves >> simp[settled_closed]
  >> qexists_tac ‘never’ >> simp[settled_never]
QED
