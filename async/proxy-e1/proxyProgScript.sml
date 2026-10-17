(*
  The proxy's fold step, translated (ordinary HOL translator) on top of
  the E1 driver's types (e1TypesProg), for the generic E1 driver: the
  initial state, the step on a list of ready handles (pstepl, which is
  pstep on ssnap: proxyStepL), the round's actions, the interest and
  finished (never).
*)
Theory proxyProg
Ancestors
  ml_translator mllist e1TypesProg honestL1PFProg proxyStepL moonshotProxy proxyHLStmts
  moonshotClientSpec
Libs
  preamble ml_translatorLib ml_progLib

val _ = translation_extends "e1TypesProg";

(* As honestL1PFProg: TAKE / DROP as the basis's mllist take / drop, MEM
   as lmem *)
fun tr th = translate (th |> REWRITE_RULE [GSYM mllistTheory.take_def,
                                          GSYM mllistTheory.drop_def,
                                          GSYM honestL1PFProgTheory.lmem_MEM]);

val _ = register_type “:pconn”;
val _ = register_type “:pst”;

val r = tr pread_def;
val r = tr cbound_def;
val r = tr pnew_def;
val r = tr popen_def;
val r = tr palll_def;
val r = tr pall_palll;
val r = tr plevels_def;
val r = tr pconnects_def;
val r = tr pwrites_def;
val r = tr wreq_def;
val r = tr pgate_def;
val r = tr preadsl_def;
val r = tr ponel_def;
val r = tr pactsl_def;
val r = tr pres_def;
val r = tr upd_at_def;
val r = tr pupdl_def;
val r = tr pupd_pupdl;
val r = tr pinitl_def;
val r = tr pstepl_def;

(* The round's actions, the interest, and finished *)
Definition pacts_of_def:
  pacts_of (st : pst) = MAP SND st.last
End

Definition pifds_of_def:
  pifds_of (lfd : word64) st = lfd :: FLAT (MAP popen st.pc)
End

Definition pfin_def:
  pfin (st : pst) = F
End

val r = tr pacts_of_def;
val r = tr pifds_of_def;
val r = tr pfin_def;
