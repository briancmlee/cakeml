open preamble
     stackSemTheory
     stack_to_labTheory
     labSemTheory

val _ = new_theory"stack_to_labProof";

(* TODO: move *)

val word_sh_word_shift = Q.store_thm("word_sh_word_shift",
  `word_sh a b c = SOME z ⇒ z = word_shift a b c`,
  EVAL_TAC >> rw[] >> every_case_tac >> fs[] >>
  EVAL_TAC >> rw[]);

val assert_T = Q.store_thm("assert_T[simp]",
  `assert T s = s`,
  rw[assert_def,state_component_equality]);

val good_syntax_def = Define `
  (good_syntax ((Seq p1 p2):'a stackLang$prog) ptr len ret <=>
     good_syntax p1 ptr len ret /\
     good_syntax p2 ptr len ret) /\
  (good_syntax ((If c r ri p1 p2):'a stackLang$prog) ptr len ret <=>
     good_syntax p1 ptr len ret /\
     good_syntax p2 ptr len ret) /\
  (good_syntax (Halt n) ptr len ret <=> (n = len)) /\
  (good_syntax (FFI n1 n2 n3) ptr len ret <=>
     n1 = ptr /\ n2 = len /\ n3 = ret) /\
  (good_syntax (Call x1 _ x2) ptr len ret <=>
     (case x1 of SOME (y,_,_,_) => good_syntax y ptr len ret | NONE => T) /\
     (case x2 of SOME (y,_,_) => good_syntax y ptr len ret | NONE => T)) /\
  (good_syntax _ ptr len ret <=> T)`

(* -- *)

val state_rel_def = Define`
  state_rel (s:('a,'b)stackSem$state) (t:('a,'b)labSem$state) ⇔
    t.regs = FAPPLY s.regs ∧
    t.mem = s.memory ∧
    t.mem_domain = s.mdomain ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    (∀n prog. lookup n s.code = SOME prog ⇒
      good_syntax prog t.len_reg t.ptr_reg t.link_reg ∧
      MEM (prog_to_section (n,prog)) t.code) ∧
    ¬t.failed ∧
    is_word (read_reg t.ptr_reg t) ∧
    (∀x. x ∈ s.mdomain ⇒ w2n x MOD (dimindex (:'a) DIV 8) = 0) ∧
    ¬s.use_stack ∧
    ¬s.use_store ∧
    ¬s.use_alloc`;

val code_installed_def = Define`
  (code_installed n [] code = T) ∧
  (code_installed n (x::xs) code ⇔
   asm_fetch_aux n code = SOME x ∧
   code_installed (n+1) xs code)`;

val set_var_upd_reg = Q.store_thm("set_var_upd_reg",
  `state_rel s t ∧ is_word b ⇒
   state_rel (set_var a b s) (upd_reg a b t)`,
  rw[state_rel_def,upd_reg_def,set_var_def,FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM] >>
  rw[]>>fs[]>>rfs[] \\ metis_tac [])

val set_var_Word_upd_reg = Q.store_thm("set_var_Word_upd_reg[simp]",
  `state_rel s t ⇒
   state_rel (set_var a (Word b) s) (upd_reg a (Word b) t)`,
   METIS_TAC[set_var_upd_reg,wordSemTheory.is_word_def])

val mem_store_upd_mem = Q.store_thm("mem_store_upd_mem",
  `state_rel s t ∧ mem_store x y s = SOME s1 ⇒
   state_rel s1 (upd_mem x y t)`,
  rw[state_rel_def,upd_mem_def,stackSemTheory.mem_store_def,FUN_EQ_THM,APPLY_UPDATE_THM] >>
  rw[APPLY_UPDATE_THM] >> rfs[] >> metis_tac []);

val state_rel_read_reg_FLOOKUP_regs = Q.store_thm("state_rel_read_reg_FLOOKUP_regs",
  `state_rel s t ∧
   FLOOKUP s.regs x = SOME y ⇒
   y = read_reg x t`,
  rw[state_rel_def]>>fs[FLOOKUP_DEF]);

val inst_correct = Q.store_thm("inst_correct",
  `inst i s1 = SOME s2 ∧
   state_rel s1 t1 ⇒
   state_rel s2 (asm_inst i t1)`,
  simp[inst_def] >>
  every_case_tac >> fs[] >>
  rw[assign_def,word_exp_def] >> rw[] >>
  fs[LET_THM] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac state_rel_read_reg_FLOOKUP_regs >> fs[] >> rfs[] >>
  imp_res_tac word_sh_word_shift >>
  fs[wordSemTheory.num_exp_def,wordSemTheory.word_op_def] >> rw[] >>
  TRY ( Cases_on`b`>>fs[binop_upd_def] >> NO_TAC) >>
  TRY (
    fs[stackSemTheory.mem_load_def,labSemTheory.mem_load_def,labSemTheory.addr_def] >>
    qpat_assum`Word _ = _`(assume_tac o SYM) >> fs[] >>
    `t1.mem_domain = s1.mdomain ∧ t1.mem = s1.memory` by ( fs[state_rel_def] ) >> fs[] >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    simp[] ) >>
  fs[stackSemTheory.word_exp_def,LET_THM,IS_SOME_EXISTS] >>
  every_case_tac >> fs[] >> rpt var_eq_tac >>
  fs[wordSemTheory.word_op_def,stackSemTheory.get_var_def] >> rpt var_eq_tac >>
  res_tac >>
  qpat_assum`Word _ = _`(assume_tac o SYM) >> fs[] >>
  `t1.mem_domain = s1.mdomain ∧ t1.mem = s1.memory` by ( fs[state_rel_def] ) >> fs[] >>
  fs[labSemTheory.mem_store_def,labSemTheory.addr_def] >>
  qmatch_assum_abbrev_tac`mem_store cc _ _ = _` >>
  `cc ∈ s1.mdomain` by fs[stackSemTheory.mem_store_def] >>
  first_assum(fn th => first_assum(
    tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
  simp[] >>
  imp_res_tac mem_store_upd_mem);

val flatten_correct = Q.store_thm("flatten_correct",
  `∀prog s1 r s2 n l t1.
     evaluate (prog,s1) = (r,s2) ∧ r ≠ SOME Error ∧
     state_rel s1 t1 ∧
     max_lab prog ≤ l ∧
     good_syntax prog t1.len_reg t1.ptr_reg t1.link_reg ∧
     code_installed t1.pc (FST (flatten prog n l)) t1.code
     ⇒
     ∃ck t2.
     case r of SOME (Halt w) =>
         evaluate (t1 with clock := t1.clock + ck) =
           ((case w of
             | Word 0w => Halt Success
             | Word _ => Halt Resource_limit_hit
             | _ => Error),
            t2) ∧
         s2.ffi = t2.ffi
     | _ =>
       evaluate (t1 with clock := t1.clock + ck) =
       evaluate t2 ∧
       state_rel s2 t2 ∧
       case r of
       | NONE => t2.pc = t1.pc + LENGTH (FST(flatten prog n l))
       | SOME (Result (Loc n1 n2) w2) =>
           loc_to_pc n1 n2 t2.code = SOME t2.pc ∧
           read_reg 2 t2 = w2
       | SOME (Exception (Loc n1 n2) w2) =>
           loc_to_pc n1 n2 t2.code = SOME t2.pc ∧
           read_reg 2 t2 = w2
       | SOME TimeOut => t2.clock = 0
       | _ => F`,
  recInduct stackSemTheory.evaluate_ind >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    qexists_tac`0`>>simp[] >> METIS_TAC[] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var v s`>>fs[] >> rpt var_eq_tac >>
    simp[] >>
    qexists_tac`1`>>
    fs[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    fs[get_var_def,FLOOKUP_DEF] >> var_eq_tac >>
    qexists_tac `t1 with clock := t1.clock + 1` >>
    fs [good_syntax_def,state_rel_def] >> rfs [] >>
    every_case_tac >> fs []) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`inst i s`>>fs[]>>rpt var_eq_tac>>simp[]>>
    imp_res_tac inst_correct >>
    qexists_tac`1`>>
    fs[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    IF_CASES_TAC >- fs[state_rel_def] >>
    simp[dec_clock_def,asm_inst_consts] >>
    `asm_inst i t1 with clock := t1.clock = asm_inst i t1`
    by METIS_TAC[asm_inst_consts,labPropsTheory.with_same_clock] >>
    pop_assum SUBST1_TAC >>
    qexists_tac`inc_pc (asm_inst i t1)`>>simp[inc_pc_def,asm_inst_consts] >>
    fs[state_rel_def,asm_inst_consts] >> METIS_TAC[] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    fs[state_rel_def] ) >>
  cheat)

val _ = export_theory();
