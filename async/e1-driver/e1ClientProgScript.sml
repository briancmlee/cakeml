(*
  The moonshot client (moonshotClient's cprog) as a fold program for the
  E1 driver: its state cst, and its fold's parts (init, step, acts, ifds,
  fin) translated.

  moonshotClient states the client on sets of ready handles and on
  rqs : num -> request list; the translated versions take the ready
  handles as a list and the request bytes as a function rq : num ->
  word8 list.  Each comes with its equation to the original:
  cinit_eq, cstep_eq (with rq = λi. brequests (rqs i)).

  mk_client a n bss lfd builds the fold's values for e1_start: the
  request bytes of connection i are EL i bss (rqf bss; [] past the end).

  client_main c a n s: the client's whole run, e1_start c on mk_client,
  with the request bytes decoded from the string s (e1Lits: the program's
  main passes lits_enc bss as a string literal).
*)
Theory e1ClientProg
Ancestors
  ml_translator asyncCore asyncM3World endpointHLModel moonshotClientSpec moonshotClient
  honestL1PFModel honestL1PFProg e1TypesProg e1DriverProg e1Lits
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "e1DriverProg";

fun tr th = translate (th |> REWRITE_RULE [GSYM honestL1PFProgTheory.lmem_MEM]);

val _ = register_type “:cconn”;
val _ = register_type “:cst”;

(* ------------------------------------------------------------------------
   The client's fold, on lists
   ------------------------------------------------------------------------ *)

Theorem cbound_num:
  cbound = 9223372036854775808
Proof
  simp[cbound_def]
QED

(* cact1 with the ready handles as a list *)
Definition cact1l_def:
  cact1l a nh c (rdy : word64 list) =
    case c of
    | CIdle => if nh < cbound then [EConnect a] else []
    | CPend hd => if MEM hd rdy then [ERead hd cread] else []
    | CUp hd rest =>
        (if rest ≠ [] then [EWrite hd rest] else []) ++
        (if MEM hd rdy then [ERead hd cread] else [])
    | CDone => []
End

(* cacts, by recursion over the connections (connection i first) *)
Definition cactsi_def:
  cactsi a nh rdy (i : num) [] = [] ∧
  cactsi a nh rdy i (c :: cs) = MAP (λx. (i, x)) (cact1l a nh c rdy) ++ cactsi a nh rdy (i + 1) cs
End

Definition cactsl_def:
  cactsl a st (rdy : word64 list) = cactsi a st.nh rdy 0 st.cs
End

(* LUPDATE (f (EL i cs)) i cs, by recursion *)
Definition lmod_def:
  lmod f (i : num) [] = [] ∧
  lmod f i (c :: cs) = if i = 0 then f c :: cs else c :: lmod f (i - 1) cs
End

(* REPLICATE N CIdle, by recursion *)
Definition cidles_def:
  cidles (n : num) = if n = 0 then [] else CIdle :: cidles (n - 1)
End

(* cupd with the request bytes as a function *)
Definition cupdf_def:
  cupdf (rq : num -> word8 list) st [] rs = st ∧
  cupdf rq st _ [] = st ∧
  cupdf rq st ((i, x) :: xs) (r :: rs) =
    cupdf rq (st with <| cs := lmod (λc. cres (rq i) c x r) i st.cs;
                         nh := st.nh + (if new_hd r = NONE then 0 else 1);
                         hlc := (case new_hd r of SOME hd => [(hd, i)] | NONE => []) ++ st.hlc |>)
          xs rs
End

Definition cinitl_def:
  cinitl a N =
    let st = <| cs := cidles N; last := []; nh := 0; hlc := [] |> in
      st with last := cactsl a st []
End

Definition cstepl_def:
  cstepl a rq st (rdy : word64 list) rs =
    let st1 = cupdf rq st st.last rs in st1 with last := cactsl a st1 rdy
End

(* The fold's actions and interest *)
Definition clast_def:
  clast st = MAP SND st.last
End

Definition chds_def:
  chds [] = [] ∧
  chds (c :: cs) = chd c ++ chds cs
End

Definition cifdsl_def:
  cifdsl st = chds st.cs
End

(* Connection i's request bytes, from the list bss *)
Definition rqf_def:
  rqf ([] : word8 list list) (i : num) = [] ∧
  rqf (bs :: bss) i = if i = 0 then bs else rqf bss (i - 1)
End

Theorem cact1_eq:
  cact1 a nh c (set rdy) = cact1l a nh c rdy
Proof
  Cases_on ‘c’ >> simp[cact1_def, cact1l_def]
QED

Theorem cactsi_eq[local]:
  ∀cs i. cactsi a nh rdy i cs =
         FLAT (GENLIST (λj. MAP (λx. (i + j, x)) (cact1l a nh (EL j cs) rdy)) (LENGTH cs))
Proof
  Induct >> simp[cactsi_def] >> rw[] >>
  REWRITE_TAC [GSYM ADD1, GENLIST_CONS] >> simp[combinTheory.o_DEF, ADD1]
QED

Theorem cacts_eq:
  cacts a st (set rdy) = cactsl a st rdy
Proof
  simp[cacts_def, cactsl_def, cact1_eq, cactsi_eq]
QED

Theorem lmod_eq:
  ∀f i cs. lmod f i cs = LUPDATE (f (EL i cs)) i cs
Proof
  Induct_on ‘cs’ >> rpt gen_tac >> Cases_on ‘i’ >> simp[lmod_def, LUPDATE_def]
QED

Theorem cidles_eq:
  ∀n. cidles n = REPLICATE n CIdle
Proof
  Induct >> simp[Once cidles_def]
QED

Theorem chds_eq:
  ∀cs. chds cs = FLAT (MAP chd cs)
Proof
  Induct >> simp[chds_def]
QED

Theorem rqf_eq:
  ∀bss i. rqf bss i = if i < LENGTH bss then EL i bss else []
Proof
  Induct >> rpt gen_tac >> Cases_on ‘i’ >> simp[rqf_def] >> rw[] >> gvs[]
QED

Theorem cupd_eq:
  ∀rqs st xs rs. cupd rqs st xs rs = cupdf (λi. brequests (rqs i)) st xs rs
Proof
  ho_match_mp_tac cupd_ind >> rw[cupd_def, cupdf_def, lmod_eq]
QED

Theorem cinit_eq:
  cinit a N = cinitl a N
Proof
  simp[cinit_def, cinitl_def, cidles_eq] >>
  ‘(∅ : word64 set) = set []’ by simp[] >> pop_assum SUBST1_TAC >> simp[cacts_eq]
QED

Theorem cstep_eq:
  cstep a rqs st (ssnap rdy rs) = cstepl a (λi. brequests (rqs i)) st rdy rs
Proof
  simp[cstep_def, cstepl_def, ssnap_def, cupd_eq, cacts_eq]
QED

Theorem cifds_eq:
  cifds a N rqs h = cifdsl (cstate a N rqs h)
Proof
  simp[cifds_def, cifdsl_def, chds_eq]
QED

(* ------------------------------------------------------------------------
   Translation
   ------------------------------------------------------------------------ *)

val r = translate cbound_num;
val r = translate cread_def;
val r = tr cact1l_def;
val r = tr cactsi_def;
val r = tr cactsl_def;
val r = translate lmod_def;
val r = translate cidles_def;
val r = translate (cres_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);
val r = translate new_hd_def;
val r = translate cupdf_def;
val r = translate cinitl_def;
val r = translate cstepl_def;
val r = translate clast_def;
val r = translate chd_def;
val r = translate chds_def;
val r = translate cifdsl_def;
val r = translate call_done_def;
val r = translate rqf_def;

Quote add_cakeml:
  fun mk_client a n bss lfd =
    (pol_never, cifdsl, clast, cstepl a (rqf bss), call_done, cinitl a n);
End

val r = translate unvnum_def;
val r = translate lits_dec_def;

Quote add_cakeml:
  fun client_main c a n s =
    let
      val bss = lits_dec (str_to_bytes s)
      fun mk lfd = mk_client a n bss lfd
    in e1_start c mk end;
End
