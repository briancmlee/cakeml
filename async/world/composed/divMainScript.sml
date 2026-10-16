(*
  Calling a diverging main: the POSTd analogue of cfMain's call_main_thm2.

  If main satisfies a CF spec with a divergence postcondition POSTd Q,
  then the whole program (the declarations prog followed by a call to
  main) diverges, and its infinite I/O trace satisfies Q.  Nothing here
  depends on a particular FFI world.
*)
Theory divMain
Ancestors
  semanticPrimitives evaluate evaluateProps evaluate_dec ml_prog
  set_sep cfHeapsBase cfStore cfApp cf cfMain lprefix_lub llist
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* Facts about evaluate_dec_list and the clock *)

(* More clock never loses I/O events (evaluate_decs has this as
   evaluate_decs_add_to_clock_io_events_mono). *)
Theorem evaluate_dec_list_add_to_clock_io_events_mono:
  ∀s env ds extra.
    io_events_mono (FST (evaluate_dec_list s env ds)).ffi
      (FST (evaluate_dec_list (s with clock := s.clock + extra) env ds)).ffi
Proof
  ho_match_mp_tac evaluate_dec_list_ind \\ rpt strip_tac
  >- simp [evaluate_dec_list_def]
  (* d1::d2::ds: split on the first declaration *)
  >- (simp [evaluate_dec_list_def]
      \\ Cases_on ‘evaluate_dec_list s env [d1]’ \\ rename1 ‘(s1,r1)’
      \\ Cases_on ‘r1 = Rerr (Rabort Rtimeout_error)’
      >- ((* the small clock stops in d1; the large one carries on *)
          gvs []
          \\ first_x_assum (qspec_then ‘extra’ mp_tac) \\ simp []
          \\ Cases_on ‘evaluate_dec_list (s with clock := extra + s.clock) env [d1]’
          \\ rename1 ‘(s1',r1')’ \\ simp [] \\ strip_tac
          \\ Cases_on ‘r1'’ \\ simp []
          \\ Cases_on ‘evaluate_dec_list s1' (a +++ env) (d2::ds)’ \\ simp []
          \\ irule io_events_mono_trans \\ first_x_assum (irule_at Any)
          \\ irule call_FFI_rel_io_events_mono
          \\ drule evaluate_dec_list_call_FFI_rel_imp \\ simp [])
      \\ drule_all evaluate_dec_list_add_to_clock
      \\ disch_then (qspec_then ‘extra’ assume_tac) \\ simp []
      \\ Cases_on ‘r1’ \\ gvs []
      \\ qpat_x_assum ‘∀x. io_events_mono (FST (evaluate_dec_list s1 _ _)).ffi _’
           (qspec_then ‘extra’ mp_tac)
      \\ rpt (CASE_TAC \\ simp []))
  >~ [‘Dlet’]
  >- (rw [evaluate_dec_list_def]
      \\ qspecl_then [‘s’, ‘env’, ‘[e]’, ‘extra’] mp_tac
           (CONJUNCT1 evaluate_add_to_clock_io_events_mono)
      \\ simp [] \\ rpt (CASE_TAC \\ simp []))
  >~ [‘Dmod’]
  >- (simp [evaluate_dec_list_def]
      \\ first_x_assum (qspec_then ‘extra’ mp_tac)
      \\ rpt (CASE_TAC \\ simp []))
  >~ [‘Dlocal’]
  >- (rename1 ‘Dlocal lds bds’
      \\ simp [evaluate_dec_list_def]
      \\ Cases_on ‘evaluate_dec_list s env lds’ \\ rename1 ‘(s1,r1)’
      \\ Cases_on ‘r1 = Rerr (Rabort Rtimeout_error)’
      >- (gvs []
          \\ first_x_assum (qspec_then ‘extra’ mp_tac) \\ simp []
          \\ Cases_on ‘evaluate_dec_list (s with clock := extra + s.clock) env lds’
          \\ rename1 ‘(s1',r1')’ \\ simp [] \\ strip_tac
          \\ Cases_on ‘r1'’ \\ simp []
          \\ Cases_on ‘evaluate_dec_list s1' (a +++ env) bds’ \\ simp []
          \\ irule io_events_mono_trans \\ first_x_assum (irule_at Any)
          \\ irule call_FFI_rel_io_events_mono
          \\ drule evaluate_dec_list_call_FFI_rel_imp \\ simp [])
      \\ drule_all evaluate_dec_list_add_to_clock
      \\ disch_then (qspec_then ‘extra’ assume_tac) \\ simp []
      \\ Cases_on ‘r1’ \\ gvs []
      \\ first_x_assum (qspec_then ‘extra’ mp_tac) \\ simp [])
  \\ rw [evaluate_dec_list_def] \\ rpt (CASE_TAC \\ simp [])
QED

(* Two runs that both finish (no timeout) agree, up to the clock. *)
Theorem evaluate_dec_list_clock_unique:
  evaluate_dec_list (s with clock := k1) env ds = (s1,r1) ∧
  r1 ≠ Rerr (Rabort Rtimeout_error) ∧
  evaluate_dec_list (s with clock := k2) env ds = (s2,r2) ∧
  r2 ≠ Rerr (Rabort Rtimeout_error) ⇒
  r2 = r1 ∧ s2 = s1 with clock := s2.clock
Proof
  ‘∀k1 k2 s1 r1 s2 r2.
     k1 ≤ k2 ∧
     evaluate_dec_list (s with clock := k1) env ds = (s1,r1) ∧
     r1 ≠ Rerr (Rabort Rtimeout_error) ∧
     evaluate_dec_list (s with clock := k2) env ds = (s2,r2) ⇒
     r2 = r1 ∧ s2 = s1 with clock := s2.clock’
    suffices_by (
      ntac 2 strip_tac
      \\ Cases_on ‘k1 ≤ k2’
      >- (first_x_assum (qspecl_then [‘k1’, ‘k2’, ‘s1’, ‘r1’, ‘s2’, ‘r2’] mp_tac)
          \\ simp [])
      \\ first_x_assum (qspecl_then [‘k2’, ‘k1’, ‘s2’, ‘r2’, ‘s1’, ‘r1’] mp_tac)
      \\ impl_tac >- simp []
      \\ rw [] \\ pop_assum (fn th => once_rewrite_tac [th])
      \\ simp [state_component_equality])
  \\ rpt gen_tac \\ strip_tac
  \\ drule_all evaluate_dec_list_add_to_clock
  \\ disch_then (qspec_then ‘k2 - k1’ mp_tac) \\ simp []
QED

(*---------------------------------------------------------------------------*)
(* The call of main *)

(* The declaration that calls main, as appended by cfMain and basis_ffiLib. *)
Definition main_call_def:
  main_call fname =
    Dlet NoLocs (Pcon NONE []) (App Opapp [Var (Short fname); Con NONE []])
End

(* If the body of main times out for every clock, so does its call, and the
   call's I/O is the body's (or nothing new, on clock 0). *)
Theorem main_call_timeout:
  nsLookup env.v (Short fname) = SOME fv ∧
  do_opapp [fv; Conv NONE []] = SOME (env', exp') ∧
  (∀ck. ∃s'. evaluate_ck ck s env' [exp'] = (s', Rerr (Rabort Rtimeout_error)))
  ⇒
  ∀c. ∃s'. evaluate_dec_list (s with clock := c) env [main_call fname] =
             (s', Rerr (Rabort Rtimeout_error)) ∧
           (c = 0 ∧ s'.ffi = s.ffi ∨
            0 < c ∧ s'.ffi = (FST (evaluate_ck (c - 1) s env' [exp'])).ffi)
Proof
  rpt strip_tac
  \\ simp [main_call_def, evaluate_dec_list_def, astTheory.pat_bindings_def]
  \\ simp [evaluate_def, do_con_check_def, build_conv_def]
  \\ Cases_on ‘c = 0’ \\ simp []
  \\ first_x_assum (qspec_then ‘c - 1’ strip_assume_tac)
  \\ gvs [evaluate_ck_def, dec_clock_def]
QED

(*---------------------------------------------------------------------------*)
(* The whole program *)

(* For each clock, the whole program times out: either inside prog, with
   I/O that is a prefix of prog's, or inside main, with main's I/O for some
   clock. *)
Theorem prog_main_call_timeout:
  evaluate_dec_list (st1 with clock := ck1) env1 prog =
    (st2 with clock := ck2, Rval env2) ∧
  nsLookup env2.v (Short fname) = SOME fv ∧
  do_opapp [fv; Conv NONE []] = SOME (env', exp') ∧
  (∀ck. ∃s'. evaluate_ck ck st2 env' [exp'] = (s', Rerr (Rabort Rtimeout_error)))
  ⇒
  ∀k. ∃s'.
    evaluate_dec_list (st1 with clock := k) env1 (prog ++ [main_call fname]) =
      (s', Rerr (Rabort Rtimeout_error)) ∧
    (s'.ffi.io_events ≼ st2.ffi.io_events ∨
     ∃c. s'.ffi = (FST (evaluate_ck c st2 env' [exp'])).ffi)
Proof
  rpt strip_tac
  \\ simp [evaluate_dec_list_append]
  \\ Cases_on ‘evaluate_dec_list (st1 with clock := k) env1 prog’
  \\ rename1 ‘(s1,r1)’
  \\ Cases_on ‘r1 = Rerr (Rabort Rtimeout_error)’
  >- ((* prog itself runs out of clock: its I/O is a prefix of the full run's *)
      gvs []
      \\ qspecl_then [‘st1 with clock := k’, ‘env1’, ‘prog’, ‘ck1’]
           mp_tac evaluate_dec_list_add_to_clock_io_events_mono
      \\ simp []
      \\ qspecl_then [‘st1 with clock := ck1’, ‘env1’, ‘prog’,
                      ‘st2 with clock := ck2’, ‘Rval env2’, ‘k’]
           mp_tac evaluate_dec_list_add_to_clock
      \\ simp [] \\ disch_then kall_tac
      \\ (‘k + ck1 = ck1 + k’ by decide_tac) \\ pop_assum SUBST1_TAC
      \\ simp [io_events_mono_def] \\ metis_tac [])
  (* prog finishes as in the Decls run; then main is called *)
  \\ qpat_assum ‘evaluate_dec_list (st1 with clock := ck1) _ _ = _’
       (mp_then Any mp_tac evaluate_dec_list_clock_unique)
  \\ simp [] \\ disch_then drule_all \\ strip_tac
  \\ qabbrev_tac ‘c = s1.clock’ \\ gvs []
  \\ ‘nsLookup (env2 +++ env1).v (Short fname) = SOME fv’
       by (simp [extend_dec_env_def, namespacePropsTheory.nsLookup_nsAppend_some])
  \\ drule_all main_call_timeout
  \\ disch_then (qspec_then ‘c’ strip_assume_tac)
  \\ gvs [combine_dec_result_def]
  \\ metis_tac [IS_PREFIX_REFL]
QED

(* How evaluate_dec_list_with_clock projects a result. *)
Theorem FST_ffi_of_result[local]:
  FST ((λ(st',r). (st'.ffi,r)) x) = (FST x).ffi
Proof
  Cases_on ‘x’ \\ simp []
QED

(* MAIN: calling a main whose spec has a divergence postcondition POSTd Q
   makes the whole program diverge, with an I/O trace satisfying Q. *)
Theorem call_main_thm_div:
  Decls env1 st1 prog env2 st2 ⇒
  lookup_var fname env2 = SOME fv ⇒
  app (proj1, proj2) fv [Conv NONE []] P ($POSTd Q) ⇒
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) ∧ P h1 ⇒
  ∃io. semantics_dec_list st1 env1 (SNOC (main_call fname) prog) (Diverge io) ∧
       Q io
Proof
  rpt strip_tac
  \\ gvs [Decls_def, lookup_var_def]
  (* run main's spec from the state after prog *)
  \\ gvs [app_def, app_basic_def]
  \\ first_x_assum drule_all \\ strip_tac
  \\ Cases_on ‘r’ \\ gvs [POSTd_def, POST_def, cond_def]
  \\ rename1 ‘Q io’ \\ qexists_tac ‘io’ \\ simp []
  \\ rename1 ‘do_opapp _ = SOME (env',exp')’
  \\ gvs [evaluate_to_heap_def]
  \\ drule_all prog_main_call_timeout \\ strip_tac
  \\ simp [semantics_dec_list_def, evaluate_dec_list_with_clock_def, SNOC_APPEND]
  \\ conj_tac
  >- (gen_tac \\ first_x_assum (qspec_then ‘k’ strip_assume_tac) \\ simp [])
  \\ gvs [lprefix_lub_def, PULL_EXISTS]
  \\ conj_tac
  >- ((* every finite run's I/O is below io: below prog's I/O, which is
         below main's, or main's itself *)
      gen_tac \\ first_x_assum (qspec_then ‘k’ strip_assume_tac) \\ simp []
      >- (‘st2.ffi.io_events ≼
             (FST (evaluate_ck 0 st2 env' [exp'])).ffi.io_events’
            by (qspecl_then [‘st2 with clock := 0’, ‘env'’, ‘[exp']’]
                  mp_tac (CONJUNCT1 evaluate_io_events_mono)
                \\ simp [io_events_mono_def, evaluate_ck_def])
          \\ irule LPREFIX_TRANS
          \\ qexists_tac ‘fromList (FST (evaluate_ck 0 st2 env' [exp'])).ffi.io_events’
          \\ simp [LPREFIX_fromList_fromList]
          \\ metis_tac [IS_PREFIX_TRANS])
      \\ gvs [])
  (* io is below every upper bound: main's run on clock ck is below main's
     run on clock ck2 + ck, which is the whole program's on ck1 + ck + 1 *)
  \\ rpt strip_tac
  \\ first_x_assum irule \\ gen_tac
  \\ ‘(FST (evaluate_dec_list (st1 with clock := ck1 + ck + 1) env1
              (prog ++ [main_call fname]))).ffi.io_events =
        (FST (evaluate_ck (ck2 + ck) st2 env' [exp'])).ffi.io_events’
    by (qspecl_then [‘st1 with clock := ck1’, ‘env1’, ‘prog’,
                     ‘st2 with clock := ck2’, ‘Rval env2’, ‘ck + 1’]
          mp_tac evaluate_dec_list_add_to_clock
        \\ simp [evaluate_dec_list_append] \\ strip_tac
        \\ ‘nsLookup (env2 +++ env1).v (Short fname) = SOME fv’
          by (simp [extend_dec_env_def,
                    namespacePropsTheory.nsLookup_nsAppend_some])
        \\ drule_all main_call_timeout
        \\ disch_then (qspec_then ‘ck + (ck2 + 1)’ strip_assume_tac)
        \\ gvs [combine_dec_result_def])
  \\ ‘(FST (evaluate_ck ck st2 env' [exp'])).ffi.io_events ≼
        (FST (evaluate_ck (ck2 + ck) st2 env' [exp'])).ffi.io_events’
    by (qspecl_then [‘st2 with clock := ck’, ‘env'’, ‘[exp']’, ‘ck2’]
          mp_tac (CONJUNCT1 evaluate_add_to_clock_io_events_mono)
        \\ simp [io_events_mono_def, evaluate_ck_def])
  \\ irule LPREFIX_TRANS
  \\ qexists_tac ‘fromList (FST (evaluate_ck (ck2 + ck) st2 env' [exp'])).ffi.io_events’
  \\ simp [LPREFIX_fromList_fromList]
  \\ first_x_assum (qspec_then ‘ck1 + ck + 1’ mp_tac)
  \\ gvs [FST_ffi_of_result]
QED
