(*Generated by Lem from compiler.lem.*)
open bossLib Theory Parse res_quanTheory
open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory
open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();



open ToBytecodeTheory ToIntLangTheory IntLangTheory CompilerPrimitivesTheory BytecodeTheory CompilerLibTheory SemanticPrimitivesTheory AstTheory LibTheory

val _ = new_theory "Compiler"

(*open Ast*)
(*open CompilerLib*)
(*open IntLang*)
(*open ToIntLang*)
(*open ToBytecode*)
(*open Bytecode*)

val _ = type_abbrev( "contab" , ``: (( conN id), num)fmap # (num, ( conN id))fmap # num``);
(*val cmap : contab -> Pmap.map (id conN) num*)
 val cmap_def = Define `
 (cmap (m,_,_) = m)`;


val _ = Hol_datatype `
 compiler_state =
  <| contab : contab
   ; rbvars : string list
   ; renv : num list
   ; rsz  : num
   ; rnext_label : num
   |>`;


(*val cpam : compiler_state -> Pmap.map num (id conN)*)
 val cpam_def = Define `
 (cpam s = ((case s.contab of (_,w,_) => w )))`;


(*val etC : compiler_state -> exp_to_Cexp_state*)
val _ = Define `
 (etC rs = (<| bvars := rs.rbvars; cnmap := ( cmap rs.contab) |>))`;


val _ = Define `
 init_compiler_state =  
(<| contab := ( FEMPTY, FEMPTY, 0)
   ; rbvars := []
   ; renv := []
   ; rsz  := 0
   ; rnext_label := 0
   |>)`;


val _ = Define `
 (compile_Cexp rs Ce =  
(let (Ce,n) = ( label_closures ( LENGTH rs.rbvars) rs.rnext_label Ce) in
  let cs = (<| out := []; next_label := n |>) in
  let cs = ( compile_code_env cs Ce) in
  compile ( MAP CTLet rs.renv) TCNonTail rs.rsz cs Ce))`;


 val number_constructors_defn = Hol_defn "number_constructors" `

(number_constructors [] ct = ct)
/\
(number_constructors ((c,_)::cs) (m,w,n) =  
(number_constructors cs ( FUPDATE  m ( (Short c), n), FUPDATE  w ( n, (Short c)), (n +1))))`;

val _ = Defn.save_defn number_constructors_defn;

val _ = Define `
 (compile_decl rs cs vs = 
  ((case FOLDL
           (\ (s,z,i,env,bvs) bv .
            (case find_index bv bvs 1 of
                  NONE =>
            (emit s ( MAP Stack [Load 0; Load 0; El i; Store 1]) ,(z + 1)
            ,(i + 1) ,((rs.rsz + z + 1) :: env) ,(bv :: bvs) )
              | SOME j =>
            (emit s ( MAP Stack [Load 0; El i; Store j]) ,z ,(i + 1) ,env
            ,bvs )
            )) (cs,0,0,rs.renv,rs.rbvars) vs of
       (cs,z,_,env,bvs) =>
   let cs = ( emit cs [Stack Pop]) in
   (( rs with<| rsz := rs.rsz + z ; renv := env ; rbvars := bvs
   ; rnext_label := cs.next_label |>) , REVERSE cs.out)
   )))`;


 val compile_dec_def = Define `

(compile_dec rs (Dtype ts) =
  (( rs with<| contab := FOLDL
        (\ct p . (case (ct ,p ) of ( ct , (_,_,cs) ) => number_constructors cs ct ))
        rs.contab ts |>)
  ,[]))
/\
(compile_dec rs (Dletrec defs) =  
(let m = ( etC rs) in
  let fns = ( MAP (\p . 
  (case (p ) of ( (n,_,_) ) => n )) defs) in
  let m = (( m with<| bvars := fns ++ m.bvars |>)) in
  let Cdefs = ( defs_to_Cdefs m defs) in
  let cs = ( compile_Cexp rs (CLetrec Cdefs (CCon 0 ( GENLIST CVar ( LENGTH fns))))) in
  compile_decl rs cs fns))
/\
(compile_dec rs (Dlet p e) =  
(let m = ( etC rs) in
  let Ce = ( exp_to_Cexp m e) in
  let (m,Cp) = ( pat_to_Cpat ( m with<| bvars := [] |>) p) in
  let vs = (m.bvars) in
  let Cpes = ([(Cp,CCon 0 ( GENLIST CVar ( LENGTH vs)))]) in
  let cs = ( compile_Cexp rs (CLet Ce (remove_mat_var 0 Cpes))) in
  compile_decl rs cs vs))`;

val _ = export_theory()

