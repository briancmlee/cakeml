(*
  asyncTranslateLib: a prototype translator for the async monad
  (design/43-async-translator.md).

  Input: the model's unfolding equation of a recursive computation,
      |- ∀x1 .. xk. f x1 .. xk = BODY
  where BODY is written with the library's combinators (bind, emit,
  readable, return, map, both), HOL case expressions over registered
  datatypes, calls to primitives and to previously translated functions,
  and recursive calls to f itself.

  Output:
   - CakeML code for f (appended to the current program), a call to the
     verified library for every combinator, written by gen below;
   - |- ∀n x1 v1 .. . INV1 x1 v1 ∧ .. ⇒
          app p f_v [v1; ..] emp (POSTv v. &COMPd p ACT B SNAP n (f x1 ..) v)
     proved by complete induction on the depth n, with a tactic (prove_tac)
     that walks the same model term and applies the library's specs;
   - |- ... (POSTv v. &COMP p ACT B SNAP (f x1 ..) v), by the approximation
     lemma app_COMP_of_approxd.

  The recursion is checked to be guarded first (check_guarded): every
  recursive call must sit in the continuation of a bind whose first part
  is a guarded primitive (one that cannot finish before a poll).  That is
  what makes the depth go down from the call site to the recursive call.
*)
structure asyncTranslateLib =
struct

open HolKernel boolLib bossLib
open cfTacticsLib ml_translatorLib basisFunctionsLib ml_progLib
open asyncCoreTheory asyncLoopTheory asyncLevel1Theory asyncCfActProgTheory asyncCfActSpecTheory
     asyncCfActBothTheory asyncM4ApproxTheory asyncM4ServerProgTheory
     asyncTranslateTheory

val ERR = mk_HOL_ERR "asyncTranslateLib"

(* ------------------------------------------------------------------------
   Primitives and context
   ------------------------------------------------------------------------ *)

(* A primitive (or a previously translated function): its model constant,
   its CakeML name, its spec |- H ⇒ app p c_v [args] emp (POSTv v. &COMP ..),
   whether it is guarded (|- (c args []).result = NONE), and |- wf (c args). *)
type prim = { const : term, name : string, spec : thm,
              guard : thm option, wf : thm }

type ctx = { self : term, self_v : term, prims : prim list,
             wfs : thm list, defs : thm list }

val v_ty = “:semanticPrimitives$v”
val bind_tm = prim_mk_const {Thy = "asyncLevel1", Name = "bind"}
val map_tm = prim_mk_const {Thy = "asyncLevel1", Name = "map"}
val both_tm = prim_mk_const {Thy = "asyncLevel1", Name = "both"}
val returns_tm = prim_mk_const {Thy = "asyncCfActProg", Name = "returns"}
val (COMP_tm, COMPd_tm) =
  let val (a, c) = dest_imp (concl (SPEC_ALL COMP_IMP_COMPd))
  in (fst (strip_comb a), fst (strip_comb c)) end

fun is_app_of c n tm =
  let val (f, args) = strip_comb tm
  in same_const f c andalso length args = n end handle HOL_ERR _ => false

val is_bind = is_app_of bind_tm 2
val is_map = is_app_of map_tm 2
val is_both = is_app_of both_tm 2

(* the value constant c_v of a spec |- .. ⇒ app p c_v args H Q *)
fun spec_fun th =
  let val c = concl (SPEC_ALL th)
      val c = if is_imp c then snd (dest_imp c) else c
  in el 2 (snd (strip_comb c)) end

val bind_v_tm = spec_fun bind_spec_d
val map_v_tm = spec_fun map_spec_d
val both_v_tm = spec_fun both_spec_d

fun lookup_prim (ctx : ctx) tm =
  let val (f, _) = strip_comb tm
  in List.find (fn (pr : prim) => same_const (#const pr) f) (#prims ctx) end

fun is_self (ctx : ctx) tm = same_const (fst (strip_comb tm)) (#self ctx)

(* the result type 'x of a computation of type history -> ('act, 'x option) outcome *)
fun res_ty m =
  let val (_, out) = dom_rng (type_of m)
      val (_, args) = dest_type out
      val opt = valOf (List.find (fn ty => can (match_type “:'a option”) ty) args)
  in hd (snd (dest_type opt)) end

(* the definitions of the refinement invariants occurring in a term *)
fun inv_defs tm =
  let val cs = find_terms (fn t => is_const t andalso
                 String.isSuffix "_TYPE" (fst (dest_const t))) tm
      fun def c = let val {Thy, Name, ...} = dest_thy_const c
                  in [DB.fetch Thy (Name ^ "_def")] end handle HOL_ERR _ => []
  in List.concat (map def cs) end

val counter = ref 0
fun fresh s = (counter := !counter + 1; s ^ Int.toString (!counter))

(* ------------------------------------------------------------------------
   Guardedness: recursive calls only under a guarded bind
   ------------------------------------------------------------------------ *)

fun check_guarded (ctx : ctx) tm =
  let
    fun calls_self t = can (find_term (same_const (#self ctx))) t
    fun go guarded t =
      if is_bind t then
        let val (m, k) = (rand (rator t), rand t)
            val g = case lookup_prim ctx m of
                        SOME {guard = SOME _, ...} => true | _ => false
        in go guarded m; go (guarded orelse g) k end
      else if is_abs t then go guarded (snd (dest_abs t))
      else if TypeBase.is_case t then
        let val (_, x, rows) = TypeBase.dest_case t
        in app (fn (_, r) => go guarded r) rows end
      else if is_self ctx t then
        (if guarded then () else
           raise ERR "check_guarded"
             ("unguarded recursive call: " ^ term_to_string t))
      else if is_comb t then (go guarded (rator t); go guarded (rand t))
      else ()
  in go false tm end

(* ------------------------------------------------------------------------
   Code generation: model term -> CakeML concrete syntax
   ------------------------------------------------------------------------ *)

val reserved = ["fn", "fun", "val", "let", "in", "end", "case", "of", "if",
                "then", "else", "and", "op", "datatype", "type", "raise",
                "handle", "andalso", "orelse", "structure", "exception"]

fun ident v =
  let val s = String.translate (fn #"'" => "_" | c => String.str c)
                (fst (dest_var v))
  in if mem s reserved then s ^ "_" else s end

(* The CakeML name the translator gave a constructor (register_type may
   change it, e.g. NoConn becomes Noconn): read it off the TypeStamp in the
   type invariant's definition. *)
fun cake_con c =
  let val inv = get_type_inv (snd (strip_fun (type_of c)))
      val defs = List.concat (map (CONJUNCTS o SPEC_ALL) (inv_defs inv))
      fun mine th = let val l = lhs (snd (strip_forall (concl (SPEC_ALL th))))
                    in same_const (fst (strip_comb (rand (rator l)))) c end
                    handle HOL_ERR _ => false
      val th = valOf (List.find mine defs)
      val ts = find_term (fn t => is_comb t andalso
                 is_const (fst (strip_comb t)) andalso
                 fst (dest_const (fst (strip_comb t))) = "TypeStamp") (concl th)
      val nm = rand (rator ts)
      val nm = if is_comb nm then rand nm else nm   (* strlit "..." *)
  in stringSyntax.fromHOLstring nm end
  handle _ => fst (dest_const c)

(* a pure term: a variable, (), or a constructor applied to variables *)
fun pure_exp tm =
  if is_var tm then ident tm
  else if tm ~~ “()” then "()"
  else let val (c, args) = strip_comb tm
           val _ = TypeBase.is_constructor c orelse
                   raise ERR "pure_exp" ("not supported: " ^ term_to_string tm)
           val _ = all is_var args orelse
                   raise ERR "pure_exp" ("nested: " ^ term_to_string tm)
       in "(" ^ String.concatWith " " (cake_con c :: map ident args)
          ^ ")" end

(* a call c a1 .. ak: non-variable arguments are let-bound first, left to
   right (the proof mirrors this order) *)
fun gen_call name args =
  let val bs = map (fn a => if is_var a then (ident a, NONE)
                            else let val n = fresh "a" in (n, SOME (pure_exp a)) end)
                   args
      val lets = List.mapPartial
                   (fn (n, SOME e) => SOME ("val " ^ n ^ " = " ^ e) | _ => NONE) bs
      val call = String.concatWith " " (name :: map fst bs)
  in if null lets then "(" ^ call ^ ")"
     else "(let " ^ String.concatWith " " lets ^ " in " ^ call ^ " end)" end

fun gen (ctx : ctx) selfname tm =
  if is_bind tm then
    let val (m, k) = (rand (rator tm), rand tm)
        val (x, b) = dest_abs k
        val kn = fresh "k" and mn = fresh "m"
    in "(let val " ^ kn ^ " = (fn " ^ ident x ^ " => " ^ gen ctx selfname b ^
       ")\n val " ^ mn ^ " = " ^ gen ctx selfname m ^
       "\n in bind " ^ mn ^ " " ^ kn ^ " end)" end
  else if is_map tm then
    let val (f, m) = (rand (rator tm), rand tm)
        val (x, b) = dest_abs f
        val fn_ = fresh "f" and mn = fresh "m"
    in "(let val " ^ fn_ ^ " = (fn " ^ ident x ^ " => " ^ pure_exp b ^
       ")\n val " ^ mn ^ " = " ^ gen ctx selfname m ^
       "\n in map " ^ fn_ ^ " " ^ mn ^ " end)" end
  else if is_both tm then
    let val (m1, m2) = (rand (rator tm), rand tm)
        val an = fresh "c" and bn = fresh "c"
    in "(let val " ^ bn ^ " = " ^ gen ctx selfname m2 ^
       "\n val " ^ an ^ " = " ^ gen ctx selfname m1 ^
       "\n in both " ^ an ^ " " ^ bn ^ " end)" end
  else if TypeBase.is_case tm then
    let val (_, x, rows) = TypeBase.dest_case tm
        fun row (pat, rhs) = pure_exp pat ^ " => " ^ gen ctx selfname rhs
    in "(case " ^ ident x ^ " of\n   " ^
       String.concatWith "\n | " (map row rows) ^ ")" end
  else if is_self ctx tm then gen_call selfname (snd (strip_comb tm))
  else case lookup_prim ctx tm of
         SOME pr => gen_call (#name pr) (snd (strip_comb tm))
       | NONE => raise ERR "gen" ("not supported: " ^ term_to_string tm)

(* ------------------------------------------------------------------------
   Proof generation: walk the model term in the goal's postcondition
   ------------------------------------------------------------------------ *)

fun is_post t = is_app_of COMPd_tm 7 t orelse is_app_of COMP_tm 6 t

(* the post-condition's parts: p, ACT, B, SNAP, depth (if COMPd), M *)
fun goal_post (_, w) =
  let val t = find_term is_post w
      val (c, args) = strip_comb t
  in if same_const c COMPd_tm
     then (el 1 args, el 2 args, el 3 args, el 4 args, SOME (el 5 args), el 6 args)
     else (el 1 args, el 2 args, el 3 args, el 4 args, NONE, el 5 args) end

fun mk_COMP (p, act, b, snap, m, v) = list_mk_icomb (COMP_tm, [p, act, b, snap, m, v])
fun mk_COMPd (p, act, b, snap, d, m, v) =
  list_mk_icomb (COMPd_tm, [p, act, b, snap, d, m, v])
fun mk_returns (p, f, args, q) =
  list_mk_icomb (returns_tm, [p, f, listSyntax.mk_list (args, v_ty), q])

val (postv_tm, cond_tm) =
  let val t = “POSTv v. &T”
  in (rator t, rator (snd (dest_abs (rand t)))) end

fun mk_postv v body = mk_comb (postv_tm, mk_abs (v, mk_comb (cond_tm, body)))

fun mk_app (p, f, args, post) =
  let val t = “app (p:'ffi ffi_proj) f args emp post”
  in subst [“p:'ffi ffi_proj” |-> p, “f:v” |-> f,
            “args:v list” |-> listSyntax.mk_list (args, v_ty),
            “post:res -> hprop” |-> post]
       (inst [alpha |-> alpha] t) end

(* instantiate a lemma's free relation variable A *)
fun instA lemma a =
  let val l = SPEC_ALL lemma
      val av = valOf (List.find (fn v => fst (dest_var v) = "A")
                        (free_vars (concl l)))
      val theta = match_type (type_of av) (type_of a)
  in INST [inst theta av |-> a] (INST_TYPE theta l) end

fun asm_pat k = [QUOTE "curried _ _ ", ANTIQUOTE k, QUOTE " ∧ _"]

(* the value of a variable argument: the v with INV x v among the assumptions *)
fun arg_value (asl, _) x =
  let fun ok t = (rand (rator t) ~~ x andalso type_of (rand t) = v_ty
                  andalso is_var (rand t)) handle HOL_ERR _ => false
  in rand (valOf (List.find ok asl)) end
  handle Option => raise ERR "arg_value" ("no value for " ^ term_to_string x)

(* report the first failing step with its goal *)
fun tr name (tac : tactic) g =
  tac g handle e =>
    (print ("\nasyncTranslateLib: step " ^ name ^ " failed (" ^
            exnMessage e ^ ") on\n" ^
            term_to_string (snd g) ^ "\n");
     raise e)

fun side_tac (ctx : ctx) =
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         simp (#wfs ctx @ List.mapPartial #guard (#prims ctx)) >> NO_TAC,
         metis_tac [COMP_IMP_COMPd]]

(* the goal: a characteristic formula with post POSTv v. &COMP(d) .. M v *)
fun prove_tac (ctx : ctx) g = tr "dispatch" (prove_tac0 ctx) g
and prove_tac0 (ctx : ctx) g =
  let val (_, _, _, _, _, m) = goal_post g
  in (if is_bind m then bind_tac ctx
      else if is_map m then map_tac ctx
      else if is_both m then both_tac ctx
      else if TypeBase.is_case m then case_tac ctx
      else call_tac ctx) g end

and bind_tac ctx (g as (asl, w)) =
  let
    val (p, act, b, snap, d, m) = goal_post g
    val d = valOf d
    val (m1, k) = (rand (rator m), rand m)
    val a = get_type_inv (res_ty m1)
    val guarded = case lookup_prim ctx m1 of
                      SOME {guard = SOME _, ...} => true | _ => false
    val fvs = free_varsl (w :: asl)
    val kn = fresh "k" and mn = fresh "m"
    val kv = mk_var (kn, v_ty) and mv = mk_var (mn, v_ty)
    val (x0, _) = dest_abs k
    val x = variant fvs x0
    val xv = variant fvs (mk_var (fst (dest_var x) ^ "v", v_ty))
    val d' = if guarded then numSyntax.mk_minus (d, numSyntax.term_of_int 1) else d
    val cont = list_mk_forall ([x, xv],
                 mk_imp (list_mk_comb (a, [x, xv]),
                   mk_returns (p, kv, [xv],
                     mk_COMPd (p, act, b, snap, d', mk_comb (k, x), xv)
                     |> rator)))
    val cont = if guarded
               then mk_imp (numSyntax.mk_less (numSyntax.zero_tm, d), cont)
               else cont
    val m1post = if guarded then mk_COMP (p, act, a, snap, m1, mv)
                 else mk_COMPd (p, act, a, snap, d, m1, mv)
    val lemma = instA (if guarded then bind_guarded_any else bind_spec_d) a
    val vv = mk_var ("v", v_ty)
    val app_tm = mk_app (p, bind_v_tm, [mv, kv],
                   mk_postv vv (mk_COMPd (p, act, b, snap, d, m, vv)))
  in
    (tr "bind/xfun" (xfun [QUOTE kn]) >>
     tr "bind/xlet" (xlet [ANTIQUOTE (mk_postv mv m1post)]) >- prove_tac ctx >>
     SUBGOAL_THEN cont ASSUME_TAC
     >- ((if guarded then DISCH_TAC else ALL_TAC) >> rpt gen_tac >> DISCH_TAC >>
         PURE_REWRITE_TAC [returns_def] >>
         tr "bind/cont" (qpat_x_assum (asm_pat kv) (irule o CONJUNCT2)) >>
         BETA_TAC >> prove_tac ctx) >>
     SUBGOAL_THEN app_tm (fn th => tr "bind/xapp" (xapp_spec th >> xsimpl))
     >- tr "bind/lemma" (MATCH_MP_TAC lemma >> side_tac ctx)) g
  end

and map_tac ctx (g as (asl, w)) =
  let
    val (p, act, b, snap, d, m) = goal_post g
    val d = valOf d
    val (f, m0) = (rand (rator m), rand m)
    val a = get_type_inv (res_ty m0)
    val fvs = free_varsl (w :: asl)
    val fname = fresh "f" and mn = fresh "m"
    val fv = mk_var (fname, v_ty) and mv = mk_var (mn, v_ty)
    val x = variant fvs (fst (dest_abs f))
    val xv = variant fvs (mk_var (fst (dest_var x) ^ "v", v_ty))
    val cont = list_mk_forall ([x, xv],
                 mk_imp (list_mk_comb (a, [x, xv]),
                   mk_returns (p, fv, [xv], mk_comb (b, mk_comb (f, x)))))
    val vv = mk_var ("v", v_ty)
    val app_tm = mk_app (p, map_v_tm, [fv, mv],
                   mk_postv vv (mk_COMPd (p, act, b, snap, d, m, vv)))
  in
    (xfun [QUOTE fname] >>
     xlet [ANTIQUOTE (mk_postv mv (mk_COMPd (p, act, a, snap, d, m0, mv)))]
     >- prove_tac ctx >>
     SUBGOAL_THEN cont ASSUME_TAC
     >- (rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [returns_def] >>
         qpat_x_assum (asm_pat fv) (irule o CONJUNCT2) >> BETA_TAC >>
         pure_tac ctx) >>
     SUBGOAL_THEN app_tm (fn th => xapp_spec th >> xsimpl)
     >- tr "map/lemma" (MATCH_MP_TAC (instA map_spec_d a) >> side_tac ctx)) g
  end

and both_tac ctx (g as (asl, w)) =
  let
    val (p, act, b, snap, d, m) = goal_post g
    val d = valOf d
    val (m1, m2) = (rand (rator m), rand m)
    val a1 = get_type_inv (res_ty m1) and a2 = get_type_inv (res_ty m2)
    val av = mk_var (fresh "c", v_ty) and bv = mk_var (fresh "c", v_ty)
    val vv = mk_var ("v", v_ty)
    val app_tm = mk_app (p, both_v_tm, [av, bv],
                   mk_postv vv (mk_COMPd (p, act, b, snap, d, m, vv)))
  in
    (xlet [ANTIQUOTE (mk_postv bv (mk_COMPd (p, act, a2, snap, d, m2, bv)))]
     >- prove_tac ctx >>
     xlet [ANTIQUOTE (mk_postv av (mk_COMPd (p, act, a1, snap, d, m1, av)))]
     >- prove_tac ctx >>
     SUBGOAL_THEN app_tm (fn th => xapp_spec th >> xsimpl)
     >- tr "both/lemma" (MATCH_MP_TAC (SPEC_ALL both_spec_d) >> side_tac ctx)) g
  end

and case_tac ctx g =
  let val (_, _, _, _, _, m) = goal_post g
      val (_, x, _) = TypeBase.dest_case m
      val defs = inv_defs (get_type_inv (type_of x))
  in (tr "case" (Cases_on [ANTIQUOTE x] >> gvs defs >> xmatch) >> prove_tac ctx) g end

(* a final pure value (the body of map's function) *)
and pure_tac ctx g =
  (FIRST [xcon >> xsimpl >> simp (#defs ctx @ inv_defs (snd g)) >> NO_TAC,
          xvar >> xsimpl >> NO_TAC]) g

(* a call of a primitive, of a translated function, or of f itself *)
and call_tac ctx (g as (asl, w)) =
  let
    val (p, act, b, snap, d, m) = goal_post g
    val (c, args) = strip_comb m
    (* let-bind the non-variable arguments, in order *)
    val lets = List.filter (not o is_var) args
    val names = map (fn _ => mk_var (fresh "a", v_ty)) lets
    fun xlet_arg (a, av) =
      xlet [ANTIQUOTE (mk_postv av (list_mk_comb (get_type_inv (type_of a), [a, av])))]
      >- tr "arg" (xcon >> xsimpl >> simp (#defs ctx @ inv_defs (get_type_inv (type_of a))))
    fun finish (g as (asl, w)) =
      let
        fun value a = case List.find (fn (t, _) => t ~~ a) (zip lets names) of
                          SOME (_, av) => av | NONE => arg_value g a
        val vals = map value args
        val vv = mk_var ("v", v_ty)
      in
        if is_self ctx m then
          let val app_tm = mk_app (p, #self_v ctx, vals,
                             mk_postv vv (mk_COMPd (p, act, b, snap, valOf d, m, vv)))
              fun is_ih th = is_forall (concl th) andalso
                             can (find_term (same_const (#self_v ctx))) (concl th)
          in (SUBGOAL_THEN app_tm (fn th => tr "self/xapp" (xapp_spec th >> xsimpl))
              >- tr "self/ih" (first_assum (irule o assert is_ih) >> simp [])) g end
        else
          let val pr = valOf (lookup_prim ctx m)
              val app_tm = mk_app (p, spec_fun (#spec pr), vals,
                             mk_postv vv (mk_COMP (p, act, b, snap, m, vv)))
          in (SUBGOAL_THEN app_tm
                (fn th => tr "call/xapp" (xapp_spec th >> xsimpl >> simp [COMP_IMP_COMPd]))
              >- tr "call/spec" (irule (#spec pr) >> simp [])) g end
      end
  in (EVERY (map xlet_arg (zip lets names)) >> finish) g end

(* ------------------------------------------------------------------------
   The front end: a recursive model definition, written once
   ------------------------------------------------------------------------ *)

(* contractiveness and well-formedness, by the shape of the body *)
fun case_split_tac (g as (_, w)) =
  let val c = find_term (fn t => TypeBase.is_case t andalso
                           is_var (#2 (TypeBase.dest_case t))) w
  in Cases_on [ANTIQUOTE (#2 (TypeBase.dest_case c))] g end

fun contr_step guards =
  FIRST [ho_match_mp_tac guarded_bind >> conj_tac >- (simp guards >> NO_TAC),
         ho_match_mp_tac nonexpansive_bind >> conj_tac,
         ho_match_mp_tac nonexpansive_map,
         ho_match_mp_tac nonexpansive_both >> conj_tac,
         simp [nonexpansive_const, nonexpansive_call] >> NO_TAC,
         gen_tac >> TRY BETA_TAC, case_split_tac >> simp []]

fun wf_step wfs =
  FIRST [first_assum ACCEPT_TAC, simp wfs >> NO_TAC,
         irule wf_bind >> conj_tac, irule wf_map, irule wf_both >> conj_tac,
         gen_tac >> TRY BETA_TAC, case_split_tac >> simp []]

(* define_async name ‘f x = BODY’ guards wfs: BODY may call f under a
   guarded bind.  Defines name_body (f abstracted) and name = fix name_body;
   proves contractive, the unfolding equation and wf (f x). *)
fun define_async name q guards wfs =
  let
    val tm = Term q
    val (l, body) = dest_eq tm
    val (fvar, xs) = strip_comb l
    val x = case xs of [x] => x
                     | _ => raise ERR "define_async" "one parameter only"
    val r = variant (free_vars tm) (mk_var ("r", type_of fvar))
    val bvar = mk_var (name ^ "_body", type_of r --> type_of fvar)
    val body_def = new_definition (name ^ "_body_def",
                     mk_eq (list_mk_comb (bvar, [r, x]), subst [fvar |-> r] body))
    val bconst = fst (strip_comb (lhs (concl (SPEC_ALL body_def))))
    val contr = store_thm (name ^ "_body_contractive",
      mk_icomb (prim_mk_const {Thy = "asyncCore", Name = "contractive"}, bconst),
      rw [contractive_def, body_def] >> REPEAT (contr_step guards))
    val fix_c = prim_mk_const {Thy = "asyncCore", Name = "fix"}
    val def = new_definition (name ^ "_def",
                mk_eq (mk_var (name, type_of fvar), mk_icomb (fix_c, bconst)))
    val fconst = lhs (concl def)
    val unfold = store_thm (name ^ "_unfold",
      mk_forall (x, subst [fvar |-> fconst] tm),
      simp [def, Once (MATCH_MP fix_unfold contr)] >> simp [body_def])
    val wf = store_thm ("wf_" ^ name,
      mk_forall (x, mk_icomb (prim_mk_const {Thy = "asyncLevel1", Name = "wf"},
                              mk_comb (fconst, x))),
      simp [def] >> irule wf_fix >> simp [contr] >> rw [body_def] >>
      REPEAT (wf_step wfs))
  in {def = def, unfold = unfold, wf = wf, contractive = contr} end

(* ------------------------------------------------------------------------
   The driver
   ------------------------------------------------------------------------ *)

(* translate_async {name, unfold, prims, wfs, act, snap}:
   name   the CakeML name of the new function;
   unfold |- ∀xs. f xs = BODY (BODY may call f);
   prims  the primitives and previously translated functions;
   wfs    well-formedness theorems for the model terms (wf_both, ...);
   act, snap  the refinement relations of actions and of snapshots.
   Returns the new function as a prim, with its COMP spec, for later calls. *)
fun translate_async {name, unfold, prims, wfs, act, snap, guard} =
  let
    val th = SPEC_ALL unfold
    val (lhs_t, body) = dest_eq (concl th)
    val (f, xs) = strip_comb lhs_t
    val ctx0 = {self = f, self_v = T, prims = prims, wfs = wfs, defs = []}
    val _ = check_guarded ctx0 body
    val code = "fun " ^ name ^ " " ^ String.concatWith " " (map ident xs) ^
               " =\n" ^ gen ctx0 name body ^ ";"
    val _ = print ("asyncTranslateLib: generated\n" ^ code ^ "\n")
    val _ = append_prog (process_topdecs [QUOTE code])
    val f_v = lhs (concl (DB.fetch "-" (name ^ "_v_def")))
    val ctx = {self = f, self_v = f_v, prims = prims, wfs = wfs, defs = []}
    val p = mk_var ("p", “:'ffi ffi_proj”)
    val n = mk_var ("n", numSyntax.num)
    val vals = map (fn x => mk_var (ident x ^ "v", v_ty)) xs
    val hyps = list_mk_conj (map2 (fn x => fn xv =>
                 list_mk_comb (get_type_inv (type_of x), [x, xv])) xs vals)
    val b = get_type_inv (res_ty lhs_t)
    val vv = mk_var ("v", v_ty)
    fun goal post = list_mk_forall (xs @ vals,
                      mk_imp (hyps, mk_app (p, f_v, vals, mk_postv vv post)))
    val goal_d = mk_forall (n, goal (mk_COMPd (p, act, b, snap, n, lhs_t, vv)))
    val goal_c = goal (mk_COMP (p, act, b, snap, lhs_t, vv))
    val spec_d = store_thm (name ^ "_spec_d", goal_d,
      tr "induct" (completeInduct_on ‘n’ >> rpt strip_tac) >>
      tr "xcf" (xcf name (get_ml_prog_state ())) >>
      tr "unfold" (ONCE_REWRITE_TAC [th]) >> prove_tac ctx)
    val spec = store_thm (name ^ "_spec", goal_c,
      rpt strip_tac >> irule app_COMP_of_approxd >> simp [spec_d])
  in {const = f, name = name, spec = spec, guard = guard,
      wf = TRUTH} : prim end

end
