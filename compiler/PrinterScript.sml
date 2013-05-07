(*Generated by Lem from printer.lem.*)
open bossLib Theory Parse res_quanTheory
open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory
open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();



open CompilerTheory ToBytecodeTheory ToIntLangTheory IntLangTheory CompilerPrimitivesTheory BytecodeTheory CompilerLibTheory SemanticPrimitivesTheory AstTheory LibTheory

val _ = new_theory "Printer"

(* observable values *)

(*open Ast*)
(*open SemanticPrimitives*)
(*open CompilerLib*)
(*open IntLang*)
(*open Bytecode*)

val _ = Hol_datatype `
 ov =
    OLit of lit
  | OConv of conN id => ov list
  | OFn
  | OLoc of num (* machine, not semantic, address *)
  | OError`;
 (* internal machine value (pointer) that should not appear *)

 val v_to_ov_defn = Hol_defn "v_to_ov" `

(v_to_ov _ (Litv l) = (OLit l))
/\
(v_to_ov s (Conv cn vs) = (OConv cn ( MAP (v_to_ov s) vs)))
/\
(v_to_ov _ (Closure _ _ _) = OFn)
/\
(v_to_ov _ (Recclosure _ _ _) = OFn)
/\
(v_to_ov s (Loc n) = (OLoc ( EL  n  s)))`;

val _ = Defn.save_defn v_to_ov_defn;

 val Cv_to_ov_defn = Hol_defn "Cv_to_ov" `

(Cv_to_ov _ _ (CLitv l) = (OLit l))
/\
(Cv_to_ov m s (CConv cn vs) = (OConv ( FAPPLY  m  cn) ( MAP (Cv_to_ov m s) vs)))
/\
(Cv_to_ov _ _ (CRecClos _ _ _) = OFn)
/\
(Cv_to_ov _ s (CLoc n) = (OLoc ( EL  n  s)))`;

val _ = Defn.save_defn Cv_to_ov_defn;

 val bv_to_ov_defn = Hol_defn "bv_to_ov" `

(bv_to_ov _ (Number i) = (OLit (IntLit i)))
/\
(bv_to_ov m (Block n vs) =  
(if n = (bool_to_tag F) then OLit (Bool F) else
  if n = (bool_to_tag T) then OLit (Bool T) else
  if n = unit_tag then OLit Unit else
  if n = closure_tag then OFn else
  OConv ( FAPPLY  m  (n - block_tag)) ( MAP (bv_to_ov m) vs)))
/\
(bv_to_ov _ (RefPtr n) = (OLoc n))
/\
(bv_to_ov _ _ = OError)`;

val _ = Defn.save_defn bv_to_ov_defn;

 val id_to_string_def = Define `

(id_to_string (Short s) = s)
/\
(id_to_string (Long x y) = ( STRCAT  x ( STRCAT  "." y)))`;


 val ov_to_string_defn = Hol_defn "ov_to_string" `

(ov_to_string (OLit (IntLit (i:int))) =  
(if int_lt i i0 then STRCAT  "-" ( num_to_dec_string ( Num ( int_neg i)))
  else num_to_dec_string ( Num i)))
/\
(ov_to_string (OLit (Bool T)) = "true")
/\
(ov_to_string (OLit (Bool F)) = "false")
/\
(ov_to_string (OLit Unit) = "()")
/\
(ov_to_string (OConv cn vs) = ( STRCAT 
  (id_to_string cn) ( STRCAT  " " 
  (case intersperse ", " ( MAP ov_to_string vs) of
    [s] => s
  | ls => STRCAT  "(" ( STRCAT(FLAT ls) ")")
  ))))
/\
(ov_to_string (OLoc _) = "<ref>")
/\
(ov_to_string OFn = "<fn>")
/\
(ov_to_string OError = "<error>")`;

val _ = Defn.save_defn ov_to_string_defn;

(*open Compiler*)

 val lookup_cc_def = Define `

(lookup_cc sz st rs (CCArg n) = ( el_check (sz + n) st))
/\
(lookup_cc sz st rs (CCEnv n) =  
(
  OPTION_BIND (el_check sz st)
  (\ v . (case v of Block 0 vs => el_check n vs | _ => NONE ))))
/\
(lookup_cc sz st rs (CCRef n) =  
(
  OPTION_BIND (el_check sz st)
  (\ v . (case v of Block 0 vs =>
     OPTION_BIND (el_check n vs)
     (\ v . (case v of RefPtr p => FLOOKUP rs p | _ => NONE ))
   | _ => NONE ))))`;


 val lookup_ct_def = Define `

(lookup_ct sz st rs (CTLet n) = (if sz < n then NONE else el_check (sz - n) st))
/\
(lookup_ct sz st rs (CTEnv cc) = ( lookup_cc sz st rs cc))`;


 val lookup_bv_def = Define `
 (lookup_bv cs bs v =  
(
  OPTION_BIND (find_index v cs.rbvars 0)
  (\ n . lookup_ct cs.rsz bs.stack bs.refs (CTLet ( EL  n  cs.renv)))))`;


 val print_dec_def = Define `

(print_dec _ _ (Dtype ls) = ( MAP (\p . 
  (case (p ) of ( (_,s,_) ) => STRCAT "type " s )) ls))
/\
(print_dec cs bs (Dlet p _) = ( MAP
    (\ p . STRCAT  "val " ( STRCAT  p ( STRCAT  " = " 
      (ov_to_string (bv_to_ov (Compiler$cpam cs) (THE (lookup_bv cs bs p)))))))
    (pat_bindings p [])))
/\
(print_dec _ _ (Dletrec defs) = ( MAP (\p . 
  (case (p ) of ( (f,_,_) ) => STRCAT "val " ( STRCAT f " = <fn>") )) defs))`;

val _ = export_theory()

