(*
  xcf_div_filter: cfDivLib.xcf_div_rule for the rule
  IMP_app_POSTd_FFI_part_filter, which has no limited_parts assumption:
  the caller names the tracked part's FFI names ns instead.
  (naryFun_repack_conv/naryClosure_repack_conv are copied from cfDivLib,
  where they are local.)
*)
structure ffiSpikeDivMultiLib =
struct

open preamble cfTacticsLib cfNormaliseTheory cfDivTheory ffiSpikeDivMultiTheory;

local
  fun naryFun_repack_conv tm =
    let
      val (base_case, rec_case) = CONJ_PAIR (GSYM naryFun_def)
      val Fun_pat = ``Fun _ _``
      val conv =
          if can (match_term Fun_pat) tm then
            (RAND_CONV naryFun_repack_conv) THENC
            (REWR_CONV rec_case)
          else
            REWR_CONV base_case
    in conv tm
    end
  val naryClosure_repack_conv =
    (RAND_CONV naryFun_repack_conv) THENC (REWR_CONV (GSYM naryClosure_def))
in
  fun xcf_div_filter ns name st =
    let
      val f_def = fetch_def name st
    in
      rpt strip_tac
      \\ simp[f_def]
      \\ match_mp_tac(GEN_ALL IMP_app_POSTd_FFI_part_filter)
      \\ qmatch_goalsub_abbrev_tac `make_stepfun_closure highly_improbable_name`
      \\ CONV_TAC(STRIP_QUANT_CONV(PATH_CONV "l" EVAL))
      \\ qunabbrev_tac `highly_improbable_name`
      \\ qmatch_goalsub_abbrev_tac `highly_improbable_name = _`
      \\ qexists_tac `highly_improbable_name`
      \\ qexists_tac ns
      \\ conj_tac >- MATCH_ACCEPT_TAC(Q.REFL `highly_improbable_name`)
      \\ conj_tac >- EVAL_TAC
      \\ qunabbrev_tac `highly_improbable_name`
      \\ CONV_TAC(STRIP_QUANT_CONV(PATH_CONV "rrl" (DEPTH_CONV naryClosure_repack_conv)))
      \\ CONSEQ_CONV_TAC(
            DEPTH_CONSEQ_CONV(
              ONCE_CONSEQ_REWRITE_CONV
                ([],[GEN_ALL(REWRITE_RULE [AND_IMP_INTRO] app_of_cf)],[])))
      \\ CONV_TAC(
            STRIP_QUANT_CONV(
              PATH_CONV "rrlr" (
                QUANT_CONV(
                  RATOR_CONV(SIMP_CONV list_ss [])
                            THENC PURE_REWRITE_CONV [AND_CLAUSES]
                            THENC SIMP_CONV (srw_ss()) [cf_def,is_bound_Fun_def,astTheory.op_case_def,
                                                        dest_opapp_def]))))
      \\ CONV_TAC(DEPTH_CONV BETA_CONV)
    end
end

end
