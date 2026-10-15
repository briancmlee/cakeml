(*
  cfDiv's FFI-part loop rule, generalised to worlds with several FFI parts.

  cfDiv's repeat_POSTd_one_FFI_part / IMP_app_POSTd_one_FFI_part require
  limited_parts ns p: the world has exactly one FFI part, so that the
  part's events ARE the program's whole I/O trace.  With several parts, a
  part's events are only the trace filtered to its names
  (FFI_part_IN_st2heap_IMP).  The rules here drop limited_parts and
  conclude about the filtered trace instead:

     ... ∧ lprefix_lub (IMAGE (fromList o events) UNIV) io ∧
     (∀io'. LFILTER (ffi_has_index_in ns) io' = io ⇒ Q io')
     ⇒ app p ... ($POSTd Q)

  The body may use other parts too (they live in the frame Hs i).  The
  proofs are cfDiv's, with the one use of limited_parts replaced, the
  whole trace taken as the limit of the run's I/O events, and a lazy-list
  lemma (LFILTER commutes with limits of chains, lprefix_lub_LFILTER).
*)
Theory ffiSpikeDivMulti
Ancestors
  cfDiv cfApp cfStore cfHeapsBase set_sep evaluate
  evaluateProps semanticPrimitives lprefix_lub llist
Libs
  preamble cfLib

val repeat_clos =
  some_repeat_clos_def |> SPEC_ALL |> concl |> rhs |> rator |> rand;

val let_a = repeat_clos |> rator |> rand |> rand |> rand |> rand

fun rename_conv s tm =
  let
    val (v,body) = dest_abs tm
  in ALPHA_CONV (mk_var(s,type_of v)) tm end;

(*---------------------------------------------------------------------------*)
(* LFILTER commutes with the limit of a chain of finite lists *)

Theorem prefix_mono_le[local]:
  (∀n. w n ≼ w (SUC n)) ⇒ ∀m n. m ≤ n ⇒ w m ≼ w n
Proof
  strip_tac \\ Induct_on ‘n’ \\ rw []
  \\ Cases_on ‘m = SUC n’ \\ gvs []
  \\ ‘m ≤ n’ by decide_tac
  \\ metis_tac [IS_PREFIX_TRANS]
QED

Theorem LPREFIX_fromList_LFILTER[local]:
  LPREFIX (fromList l) ll ⇒ LPREFIX (fromList (FILTER P l)) (LFILTER P ll)
Proof
  rw [LPREFIX_APPEND]
  \\ simp [LFILTER_APPEND, LFINITE_fromList, LFILTER_fromList]
  \\ metis_tac []
QED

(* An element of a filtered lazy list comes from a finite prefix. *)
Theorem LNTH_LFILTER_prefix[local]:
  ∀k io x. LNTH k (LFILTER P io) = SOME x ⇒
           ∃l r. io = LAPPEND (fromList l) r ∧
                 LNTH k (fromList (FILTER P l)) = SOME x
Proof
  Induct \\ rw []
  \\ Cases_on ‘LFILTER P io’ \\ gvs []
  \\ drule LFILTER_EQ_CONS \\ strip_tac \\ gvs []
  >- (qexistsl [‘l ++ [h]’, ‘ll'’]
      \\ ‘FILTER P l = []’ by gvs [FILTER_EQ_NIL, EVERY_MEM]
      \\ simp [GSYM LAPPEND_fromList, LAPPEND_ASSOC, FILTER_APPEND])
  \\ first_x_assum drule \\ strip_tac \\ gvs []
  \\ qexistsl [‘l ++ [h] ++ l'’, ‘r’]
  \\ simp [GSYM LAPPEND_fromList, LAPPEND_ASSOC, FILTER_APPEND]
  \\ ‘FILTER P l = []’ by gvs [FILTER_EQ_NIL, EVERY_MEM]
  \\ gvs [LNTH_fromList]
QED

(* Every finite prefix of the limit of a chain is a prefix of some
   element of the chain. *)
Theorem prefix_reached[local]:
  (∀n. w n ≼ w (SUC n)) ∧ lprefix_lub (IMAGE (fromList o w) UNIV) io ⇒
  ∀l r. io = LAPPEND (fromList l) r ⇒ ∃n. l ≼ w n
Proof
  strip_tac \\ ho_match_mp_tac SNOC_INDUCT \\ conj_tac >- simp []
  \\ rpt strip_tac
  \\ first_x_assum (qspec_then ‘x ::: r’ mp_tac)
  \\ impl_tac >- simp [GSYM LAPPEND_fromList, LAPPEND_ASSOC, SNOC_APPEND]
  \\ strip_tac
  \\ rename1 ‘l ≼ w n1’
  \\ ‘LNTH (LENGTH l) io = SOME x’
    by simp [LNTH_LAPPEND, SNOC_APPEND, LNTH_fromList, EL_APPEND2,
             LLENGTH_fromList]
  \\ ‘lprefix_chain (IMAGE (fromList o w) UNIV)’
    by metis_tac [lprefix_lub_is_chain]
  \\ ‘LNTH (LENGTH l) io =
      lprefix_chain_nth (LENGTH l) (IMAGE (fromList o w) UNIV)’
    by metis_tac [lprefix_lub_nth]
  \\ ‘∃n2. LNTH (LENGTH l) (fromList (w n2)) = SOME x’
    by (gvs [lprefix_chain_nth_def, some_def] \\ metis_tac [])
  \\ qabbrev_tac ‘n = MAX n1 n2’
  \\ ‘w n1 ≼ w n ∧ w n2 ≼ w n’
    by (drule prefix_mono_le \\ simp [Abbr ‘n’])
  \\ ‘LPREFIX (fromList (w n)) io’
    by (fs [lprefix_lub_def, PULL_EXISTS] \\ metis_tac [])
  \\ qexists_tac ‘n’
  \\ ‘l ≼ w n’ by metis_tac [IS_PREFIX_TRANS]
  \\ ‘LENGTH l < LENGTH (w n2)’
    by (qpat_x_assum ‘LNTH _ (fromList (w n2)) = _’ mp_tac
        \\ rw [LNTH_fromList])
  \\ ‘LENGTH l < LENGTH (w n)’
    by metis_tac [IS_PREFIX_LENGTH, LESS_LESS_EQ_TRANS]
  \\ ‘LNTH (LENGTH l) (fromList (w n)) = LNTH (LENGTH l) io’
    by (qpat_x_assum ‘LPREFIX (fromList (w n)) _’ mp_tac
        \\ rw [LPREFIX_NTH, LLENGTH_fromList, less_opt_def])
  \\ ‘EL (LENGTH l) (w n) = x’
    by (qpat_x_assum ‘LNTH (LENGTH l) io = SOME x’ mp_tac
        \\ pop_assum (SUBST1_TAC o SYM) \\ simp [LNTH_fromList])
  \\ qpat_x_assum ‘l ≼ w n’ mp_tac
  \\ rw [IS_PREFIX_APPEND, SNOC_APPEND]
  \\ Cases_on ‘l'’ \\ gvs [EL_APPEND2]
QED

(* MAIN (lazy lists): filtering the limit of a chain of finite lists gives
   the limit of the filtered chain. *)
Theorem lprefix_lub_LFILTER:
  (∀n. w n ≼ w (SUC n)) ∧ lprefix_lub (IMAGE (fromList o w) UNIV) io ⇒
  lprefix_lub (IMAGE (fromList o FILTER P o w) UNIV) (LFILTER P io)
Proof
  strip_tac \\ simp [lprefix_lub_def, PULL_EXISTS] \\ conj_tac
  >- (rw [] \\ irule LPREFIX_fromList_LFILTER
      \\ gvs [lprefix_lub_def, PULL_EXISTS])
  \\ rw [LPREFIX_NTH, less_opt_LLENGTH_LNTH_SOME, IS_SOME_EXISTS]
  \\ drule LNTH_LFILTER_prefix \\ strip_tac
  \\ ‘∃m. l ≼ w m’ by metis_tac [prefix_reached]
  \\ ‘FILTER P l ≼ FILTER P (w m)’ by metis_tac [IS_PREFIX_FILTER]
  \\ first_x_assum (qspec_then ‘m’ mp_tac)
  \\ rw [LPREFIX_NTH, LLENGTH_fromList, less_opt_def]
  \\ gvs [LNTH_fromList] \\ every_case_tac \\ gvs []
  \\ ‘n < LENGTH (FILTER P (w m))’
    by metis_tac [IS_PREFIX_LENGTH, LESS_LESS_EQ_TRANS]
  \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ simp [LNTH_fromList]
  \\ gvs [IS_PREFIX_APPEND, EL_APPEND1]
QED

Theorem repeat_POSTd_FFI_part_filter:
    !p env fv xv H Q ns.
      (?Hs events vs ss u io.
         vs 0 xv /\ H ==>> Hs 0 /\
         (!i. ?P. Hs i = P * one (FFI_part (ss i) u ns (events i))) /\
         (!i xv. vs i xv ==>
            (app p fv [xv] (Hs i)
                             (POSTv v'. &(vs (SUC i) v') * Hs (SUC i)))) /\
         lprefix_lub (IMAGE (fromList o events) UNIV) io /\
         (!io'. LFILTER (ffi_has_index_in ns) io' = io ==> Q io'))
      ==>
      app p (some_repeat_clos env) [fv; xv] H ($POSTd Q)
Proof
  rpt strip_tac
  \\ rw [app_def, app_basic_def]
  \\ fs [some_repeat_clos_def,do_opapp_def,Once find_recfun_def]
  \\ fs [POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM,cond_STAR]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once evaluate_to_heap_def]
  \\ fs [evaluate_ck_def,evaluate_def,PULL_EXISTS,
         cfStoreTheory.st2heap_clock]
  \\ `SPLIT3 (st2heap p st) (h_i,h_k,EMPTY)` by fs [SPLIT3_def,SPLIT_def]
  \\ asm_exists_tac \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rpt strip_tac
  \\ rename [`SPLIT (st2heap p st1) (h_j,h_l)`]
  \\ qmatch_goalsub_abbrev_tac `evaluate_to_heap st1 ENVE BODYE`
  \\ qexists_tac `Div (build_lprefix_lub (IMAGE (\ck. fromList
        (FST (evaluate_ck ck st1 ENVE [BODYE])).ffi.io_events) UNIV))`
  \\ qunabbrev_tac `ENVE` \\ qunabbrev_tac `BODYE`
  \\ fs [POSTd_eq] \\ fs [emp_def]
  \\ qexists_tac `UNIV DIFF h_l`
  \\ qexists_tac `UNIV`
  \\ conj_tac THEN1 fs [SPLIT3_def,IN_DISJOINT,EXTENSION]
  \\ fs [evaluate_to_heap_def]
  \\ fs [app_def,app_basic_def,POSTv_eq,PULL_EXISTS]
  \\ fs [evaluate_to_heap_def,PULL_EXISTS,cond_STAR]
  \\ qabbrev_tac `assert_Hs = \i st.
                    ?h_i h_k. SPLIT (st2heap p st) (h_i,h_k) /\ Hs i h_i`
  \\ `!i xv st0.
        assert_Hs i st0 /\ vs i xv ==>
        ?env exp ck st1 xv'.
          assert_Hs (i+1) st1 /\
          do_opapp [fv; xv] = SOME (env,exp) /\
          evaluate_ck ck st0 env [exp] = (st1,Rval [xv']) /\
          vs (i+1) xv' /\
          st1.clock = 0` by
   (fs [Abbr`assert_Hs`,PULL_EXISTS] \\ rpt strip_tac
    \\ first_assum drule \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac \\ fs [ADD1]
    \\ drule SPLIT_of_SPLIT3_2u3
    \\ strip_tac
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `st'' with clock := 0`
    \\ simp[st2heap_clock]
    \\ asm_exists_tac \\ simp[]
    \\ PURE_ONCE_REWRITE_TAC[CONJ_SYM]
    \\ asm_exists_tac \\ simp[]
    \\ fs[evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_set_clock
    \\ disch_then (qspec_then `0` mp_tac) \\ strip_tac \\ fs []
    \\ qexists_tac `ck1` \\ fs [cfStoreTheory.st2heap_clock])
  \\ `!x. ?ck st1 xv'. let (i,st0,xv) = x in
            assert_Hs i st0 /\ vs i xv ==>
            ?env exp.
              assert_Hs (i+1) st1 /\
              do_opapp [fv; xv] = SOME (env,exp) /\
              evaluate_ck ck st0 env [exp] = (st1,Rval [xv']) /\
              vs (i+1) xv' /\
              st1.clock = 0` by (fs [FORALL_PROD] \\ metis_tac [])
  \\ pop_assum mp_tac
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [SKOLEM_THM]))
  \\ simp []
  \\ fs [FORALL_PROD]
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rr") (rename_conv "clocks"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrar") (rename_conv "states"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarar") (rename_conv "values"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrararar") (rename_conv "i"))
  \\ CONV_TAC ((RATOR_CONV o PATH_CONV "rrarararar") (rename_conv "st0"))
  \\ strip_tac
  \\ qabbrev_tac `svpairs = (\x. states x, values x)`
  \\ qabbrev_tac `get_i = get_index (st1,xv) svpairs`
  \\ qabbrev_tac `cks = clocks o get_i`
  \\ qabbrev_tac `sts = \i.
                    if i = 0 then st1 else states (get_index (st1,xv) svpairs (i-1))`
  \\ qabbrev_tac `vls = \i.
                    if i = 0 then xv else values (get_index (st1,xv) svpairs (i-1))`
  \\ `∀i.
        ∃env exp.
            do_opapp [fv; vls i] = SOME (env,exp) ∧
            evaluate_ck (cks i) (sts i) env [exp] =
            (sts (i+1),Rval [vls (i + 1)]) ∧
            (sts (i+1)).clock = 0 ∧
            assert_Hs i (sts i) ∧ assert_Hs (i+1) (sts (i+1)) /\
            vs (i+1) (vls (i+1))` by
    (Induct THEN1
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`, Abbr`svpairs`,Abbr`vls`]
       \\ `assert_Hs 0 st1` by
         (fs [Abbr`assert_Hs`] \\ asm_exists_tac \\ fs [SEP_IMP_def])
       \\ `vs 0 xv` by simp[]
       \\ fs [] \\ once_rewrite_tac [get_index_def] \\ fs []
       \\ first_x_assum drule \\ disch_then drule \\ strip_tac \\ fs []
      )
     \\ fs [ADD1]
     \\ first_x_assum drule \\ disch_then drule
     \\ strip_tac \\ fs []
     \\ `(states (i + 1,sts (i + 1),vls(i+1))) = sts (i+2)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`,Abbr`vls`,Abbr`svpairs`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ `(values (i + 1,sts (i + 1),vls(i+1))) = vls (i+2)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`,Abbr`vls`,Abbr`svpairs`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ `clocks (i + 1,sts (i + 1),vls(i+1)) = cks (i+1)` by
      (fs [Abbr`sts`,Abbr`cks`,Abbr`get_i`,Abbr`vls`,Abbr`svpairs`]
       \\ once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once get_index_def])
     \\ fs [])
  \\ qabbrev_tac `cks_sum = \i. SUM (GENLIST cks i) + 3 * i`
  \\ qabbrev_tac `nth_env = \i. (env with
               v :=
                 nsBind «x» (vls i)
                   (nsBind «f» fv
                      (build_rec_env ^repeat_clos env env.v)))`
  \\ `(env with v :=
                 nsBind «x» (vls 0)
                   (nsBind «f» fv
                      (build_rec_env ^repeat_clos env env.v))) = nth_env 0`
        by fs [Abbr `nth_env`] \\ fs [] \\ pop_assum kall_tac
  \\ qabbrev_tac `body = ^let_a`
  \\ `(∀i n.
         i <= n ==>
         ∃st'.
            evaluate_ck (cks_sum n - cks_sum i) (sts i) (nth_env i) [body] =
              (st',Rerr (Rabort Rtimeout_error)) /\
            FILTER (ffi_has_index_in ns) st'.ffi.io_events = events n)` by
   (completeInduct_on `n-i:num` \\ rw []
    \\ fs [PULL_FORALL] \\ Cases_on `n = i` \\ fs [] \\ rveq
    THEN1
     (simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
      \\ simp [Once evaluate_def,Abbr `nth_env`]
      \\ ntac 4 (simp [Once evaluate_def])
      \\ first_x_assum (qspec_then `i` mp_tac) \\ rw [] \\ fs []
      \\ qunabbrev_tac `assert_Hs` \\ fs []
      \\ last_x_assum (qspec_then `i` mp_tac)
      \\ rw [] \\ fs [] \\ fs [STAR_def,one_def,SPLIT_def,EXTENSION]
      \\ irule FFI_part_IN_st2heap_IMP
      \\ MAP_EVERY qexists_tac [`p`, `ss i`, `u`]
      \\ metis_tac [])
    \\ simp [Once evaluate_def,Abbr `body`,evaluate_ck_def]
    \\ simp [Once evaluate_def,Abbr `nth_env`]
    \\ ntac 3 (simp [Once evaluate_def])
    \\ qpat_x_assum `!i. ?x. _`(qspec_then `i` mp_tac) \\ rw [] \\ fs []
    \\ `cks_sum i + 3 + cks i <= cks_sum n` by
     (fs [Abbr`cks_sum`]
      \\ `SUC i <= n` by fs []
      \\ pop_assum mp_tac
      \\ simp [Once LESS_EQ_EXISTS] \\ rw [ADD1,LEFT_ADD_DISTRIB] \\ fs []
      \\ qsuff_tac `SUM (GENLIST cks i) + cks i <= SUM (GENLIST cks (i + (p' + 1)))`
      THEN1 fs [] \\ fs [GSYM SUM_GENLIST_SUC]
      \\ match_mp_tac SUM_GENLIST_LESS_EQ \\ fs [])
    \\ simp [evaluateTheory.dec_clock_def,namespaceTheory.nsOptBind_def]
    \\ fs [evaluate_ck_def]
    \\ drule evaluatePropsTheory.evaluate_add_to_clock \\ fs []
    \\ disch_then (qspec_then `(cks_sum n − (cks_sum i + 1)) - cks i` mp_tac)
    \\ `cks_sum n − (cks_sum i + 1) − cks i + cks i =
        cks_sum n − (cks_sum i + 1)` by fs [] \\ fs []
    \\ disch_then kall_tac
    \\ ntac 3 (simp [Once evaluate_def])
    \\ fs [astTheory.pat_bindings_def]
    \\ fs [semanticPrimitivesTheory.pmatch_def,same_ctor_def,same_type_def]
    \\ fs [build_rec_env_def]
    \\ ntac 3 (simp [Once evaluate_def])
    \\ ntac 3 (simp [Once evaluate_def])
    \\ simp [Once evaluate_def]
    \\ simp [do_opapp_def,Once find_recfun_def]
    \\ simp [Once evaluate_def]
    \\ fs [evaluateTheory.dec_clock_def]
    \\ `(cks i + (cks_sum i + 3)) = cks_sum (i+1)` by
     (fs [Abbr`cks_sum`,GSYM ADD1] \\ fs [GENLIST]
      \\ fs [SNOC_APPEND,SUM_APPEND])
    \\ fs [AND_IMP_INTRO,build_rec_env_def])
  \\ pop_assum (qspec_then `0` mp_tac)
  \\ fs [Abbr `sts`] \\ strip_tac
  \\ `cks_sum 0 = 0` by fs [Abbr `cks_sum`] \\ fs []
  (* the whole trace: the limit E of the run's I/O events over all clocks *)
  \\ ‘env with v := nsBind «x» xv (nsBind «f» fv
         (build_rec_env [(«repeat»,«f»,Fun «x» body)] env env.v)) = nth_env 0’
    by simp [Abbr ‘nth_env’, Abbr ‘vls’]
  \\ pop_assum SUBST_ALL_TAC
  \\ qabbrev_tac ‘E = λck. (FST (evaluate_ck ck st1 (nth_env 0) [body])).ffi.io_events’
  \\ ‘(λck. fromList (FST (evaluate_ck ck st1 (nth_env 0) [body])).ffi.io_events) =
      fromList o E’ by simp [Abbr ‘E’, FUN_EQ_THM]
  \\ pop_assum SUBST_ALL_TAC
  \\ ‘∀ck. E ck ≼ E (SUC ck)’
    by (rw [Abbr ‘E’] \\ fs [evaluate_ck_def]
        \\ qspecl_then [‘st1 with clock := ck’,‘nth_env 0’,‘[body]’,‘1’] mp_tac
             (evaluatePropsTheory.evaluate_add_to_clock_io_events_mono
              |> CONJUNCT1 |> INST_TYPE [``:'ffi``|->``:'a``])
        \\ fs [evaluatePropsTheory.io_events_mono_def, ADD1])
  \\ ‘∀i. cks_sum i < cks_sum (i + 1)’
    by (simp [Abbr ‘cks_sum’] \\ rw []
        \\ qsuff_tac ‘SUM (GENLIST cks i) <= SUM (GENLIST cks (i + 1))’
        >- simp [] \\ match_mp_tac SUM_GENLIST_LESS_EQ \\ fs [])
  (* the run's events, sampled at the loop iterations *)
  \\ qabbrev_tac ‘smp = λn. E (cks_sum n)’
  \\ ‘∀n. FILTER (ffi_has_index_in ns) (smp n) = events n’
    by (rw [Abbr ‘smp’, Abbr ‘E’]
        \\ qpat_x_assum ‘∀n. ∃st'. evaluate_ck _ _ _ _ = _ ∧ _’
             (qspec_then ‘n’ strip_assume_tac) \\ simp [])
  \\ ‘∀n. smp n ≼ smp (SUC n)’
    by (rw [Abbr ‘smp’]
        \\ irule (prefix_mono_le |> UNDISCH |> SPEC_ALL |> DISCH_ALL)
        \\ simp []
        \\ qpat_x_assum ‘∀i. cks_sum i < _’ (qspec_then ‘n’ mp_tac)
        \\ simp [ADD1])
  \\ ‘∃ioW. lprefix_lub (IMAGE (fromList o smp) UNIV) ioW’
    by (irule_at Any build_lprefix_lub_thm
        \\ rw [lprefix_chain_def] \\ simp [LPREFIX_fromList, from_toList]
        \\ qpat_x_assum ‘∀n. smp n ≼ _’ assume_tac
        \\ drule prefix_mono_le \\ strip_tac
        \\ metis_tac [LESS_EQ_CASES])
  \\ ‘lprefix_lub (IMAGE (fromList o E) UNIV) ioW’
    by (simp [combinTheory.o_DEF]
        \\ ho_match_mp_tac (GEN_ALL lprefix_lub_skip)
        \\ qexists_tac ‘cks_sum’ \\ rpt conj_tac
        >- (rw [LPREFIX_fromList, from_toList] \\ metis_tac [ADD1])
        >- simp []
        \\ qpat_x_assum ‘lprefix_lub (IMAGE (fromList o smp) _) _’ mp_tac
        \\ simp [Abbr ‘smp’, combinTheory.o_DEF])
  \\ ‘build_lprefix_lub (IMAGE (fromList o E) UNIV) = ioW’
    by (irule unique_lprefix_lub
        \\ qexists_tac ‘IMAGE (fromList o E) UNIV’ \\ simp []
        \\ irule build_lprefix_lub_thm
        \\ irule lprefix_lub_is_chain \\ qexists_tac ‘ioW’ \\ simp [])
  \\ ‘(λck. fromList (E ck)) = fromList o E’ by simp [FUN_EQ_THM]
  \\ pop_assum (fn th => REWRITE_TAC [th])
  \\ simp []
  (* the filtered whole trace is the part's trace *)
  \\ conj_tac
  >- (qpat_x_assum ‘∀io'. _ ⇒ Q io'’ irule
      \\ ‘lprefix_lub (IMAGE (fromList o FILTER (ffi_has_index_in ns) o smp) UNIV)
            (LFILTER (ffi_has_index_in ns) ioW)’
        by (irule lprefix_lub_LFILTER \\ simp [])
      \\ ‘fromList o FILTER (ffi_has_index_in ns) o smp = fromList o events’
        by simp [FUN_EQ_THM]
      \\ irule unique_lprefix_lub
      \\ qexists_tac ‘IMAGE (fromList o events) UNIV’ \\ simp []
      \\ ‘LUB (IMAGE (λck. fromList (E ck)) UNIV) = ioW’
        by (qpat_x_assum ‘LUB _ = ioW’ (SUBST1_TAC o SYM)
            \\ simp [combinTheory.o_DEF])
      \\ pop_assum SUBST1_TAC
      \\ qpat_x_assum ‘lprefix_lub _ (LFILTER _ _)’ mp_tac
      \\ qpat_x_assum ‘∀n. FILTER _ (smp n) = events n’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp [combinTheory.o_DEF])
  \\ reverse conj_tac
  >- fs [combinTheory.o_DEF]
  \\ rw []
  \\ qpat_x_assum ‘∀n. ∃st'. evaluate_ck _ _ _ _ = _ ∧ _’
       (qspec_then ‘ck’ strip_assume_tac)
  \\ imp_res_tac evaluate_ck_timeout_error_IMP
  \\ ‘ck <= cks_sum ck’ by simp [Abbr ‘cks_sum’]
  \\ first_x_assum drule \\ simp []
QED

(* MAIN: cfDiv's IMP_app_POSTd_one_FFI_part without limited_parts.  A
   never-ending tail-recursive function whose body keeps track of one FFI
   part ns (other parts may be in the frame Hs i and used freely) diverges,
   and its trace, filtered to ns, is the limit io of the part's events. *)
Theorem IMP_app_POSTd_FFI_part_filter:
    make_stepfun_closure env fname farg fbody = SOME stepv /\
    fname ≠ farg ∧
    (∃Hs events vs ss u io.
         vs 0 xv ∧ H ==>> Hs 0 * one (FFI_part (ss 0) u ns (events 0)) ∧
         (∀i xv'.
              vs i xv' ==>
              app p stepv [xv'] (Hs i * one (FFI_part (ss i) u ns (events i)))
                (POSTv v'. &(vs (SUC i) v') *
                           Hs (SUC i) * one (FFI_part (ss (SUC i)) u ns (events (SUC i))))) ∧
         lprefix_lub (IMAGE (fromList ∘ events) univ(:num)) io ∧
         (∀io'. LFILTER (ffi_has_index_in ns) io' = io ⇒ Q io')) ⇒
    app p (Recclosure env [(fname,farg,fbody)] fname) [xv] H ($POSTd Q)
Proof
  strip_tac
  \\ match_mp_tac make_repeat_closure_sound \\ fs []
  \\ fs [make_repeat_closure_def]
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ match_mp_tac app_opapp_intro
  \\ fs [evaluate_def,build_rec_env_def]
  \\ fs [GSYM some_repeat_clos_def]
  \\ match_mp_tac (GEN_ALL repeat_POSTd_FFI_part_filter) \\ fs []
  \\ qexists_tac `ns` \\ fs []
  \\ qexists_tac `\i. Hs i * one (FFI_part (ss i) u ns (events i))`
  \\ MAP_EVERY qexists_tac [`events`, `vs`, `ss`, `u`, `io`]
  \\ fs [] \\ conj_tac
  THEN1 (rw [] \\ qexists_tac `Hs i` \\ fs [])
  \\ rw [] \\ fs [STAR_ASSOC]
QED
