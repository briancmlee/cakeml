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

(* The library's combinators in CakeML: their names, and the specs the
   proof applies (a guarded bind, a bind at depth n, map, both). *)
type vocab = { bind : string, map : string, both : string,
               bind_guarded : thm, bind_d : thm, map_d : thm, both_d : thm }

type ctx = { self : term, self_v : term, prims : prim list,
             wfs : thm list, defs : thm list, vocab : vocab }

val v_ty = “:semanticPrimitives$v”

(* The refinement invariant of a type, as the standard translator's
   get_type_inv, extended to type variables: a type variable 'a gets a
   relation variable Ra (the protocol's R in PROTO_IMPL), a function type
   the translator's Arrow, and a type operator over type variables its
   invariant constant applied to theirs. *)
fun type_inv ty =
  if is_vartype ty then
    mk_var ("R" ^ String.translate (fn #"'" => "" | c => String.str c)
                    (dest_vartype ty), ty --> v_ty --> bool)
  else if null (type_vars ty) then get_type_inv ty
  else if can dom_rng ty andalso fst (dest_type ty) = "fun" then
    let val (d, r) = dom_rng ty
    in list_mk_icomb (prim_mk_const {Thy = "ml_translator", Name = "Arrow"},
                      [type_inv d, type_inv r]) end
  else
    let val (_, args) = dest_type ty
        val inst0 = get_type_inv (type_subst (map (fn a => a |-> oneSyntax.one_ty)
                                   (filter is_vartype args)) ty)
        val (c, cargs) = strip_comb inst0
        val {Thy, Name, ...} = dest_thy_const c
        val args' = map2 (fn a => fn ca => if is_vartype a then type_inv a else ca)
                         args cargs
    in list_mk_icomb (prim_mk_const {Thy = Thy, Name = Name}, args') end
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

(* the abstract echo library of asyncM4ServerProg *)
val echo_vocab : vocab =
  {bind = "bind", map = "map", both = "both",
   bind_guarded = bind_guarded_any, bind_d = bind_spec_d,
   map_d = map_spec_d, both_d = both_spec_d}

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
      val bool_def = if can (find_term (same_const “BOOL”)) tm
                     then [ml_translatorTheory.BOOL_def] else []
  in bool_def @ List.concat (map def cs) end

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
  if c ~~ T then "True" else if c ~~ F then "False" else
  let val inv = type_inv (snd (strip_fun (type_of c)))
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

(* a simple pure term: a variable, (), or a constructor applied to variables *)
fun is_simple tm =
  is_var tm orelse tm ~~ “()” orelse
  (let val (c, args) = strip_comb tm
   in TypeBase.is_constructor c andalso all is_var args end
   handle HOL_ERR _ => false)

(* Any other pure term t goes to the standard translator: it is lifted to
   aux ys = t (ys its free variables; a unit argument if there are none),
   translated, and called.  The proof finds the aux again by matching. *)
val aux_table : thm list ref = ref []

fun aux_inst t =
  let fun try def =
        let val d = SPEC_ALL def
            val (l, r) = dest_eq (concl d)
            val (tmS, tyS) = match_term r t
            val d' = INST tmS (INST_TYPE tyS d)
            val (_, args) = strip_comb (lhs (concl d'))
        in case args of
               [u] => if type_of u = oneSyntax.one_ty andalso is_var u
                      then (INST [u |-> oneSyntax.one_tm] d', true)
                      else (d', false)
             | _ => (d', false)
        end
  in valOf (valOf (List.find isSome
                    (map (fn d => SOME (try d) handle HOL_ERR _ => NONE)
                         (!aux_table)))) end
  handle Option => raise ERR "aux_inst" ("no aux for " ^ term_to_string t)

fun lift_pure t =
  (aux_inst t; ()) handle HOL_ERR _ =>
  let val ys = free_vars t
      val ys = if null ys then [mk_var (fresh "u", oneSyntax.one_ty)] else ys
      val name = fresh "aux"
      val f = mk_var (name, foldr (fn (y, ty) => type_of y --> ty) (type_of t) ys)
      val def = new_definition (name ^ "_def", mk_eq (list_mk_comb (f, ys), t))
      val _ = translate def
  in aux_table := def :: !aux_table end

(* a call of a functional parameter (a variable) on simple arguments: the
   CakeML value is passed in, and the proof uses its Arrow certificate *)
fun is_param_call tm =
  let val (f, args) = strip_comb tm
  in is_var f andalso not (null args) andalso all is_simple args end

fun pure_exp tm =
  if is_param_call tm then
    let val (f, args) = strip_comb tm
    in "(" ^ String.concatWith " " (map ident (f :: args)) ^ ")" end
  else if is_simple tm then
    if is_var tm then ident tm
    else if tm ~~ “()” then "()"
    else let val (c, args) = strip_comb tm
         in "(" ^ String.concatWith " " (cake_con c :: map ident args) ^ ")" end
  else
    let val _ = lift_pure tm
        val (d, unit_arg) = aux_inst tm
        val (c, args) = strip_comb (lhs (concl d))
        val name = fst (dest_const c)
    in if unit_arg then
         let val u = fresh "u" in
           "(let val " ^ u ^ " = () in " ^ name ^ " " ^ u ^ " end)" end
       else "(" ^ String.concatWith " " (name :: map ident args) ^ ")" end

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
       "\n in " ^ #bind (#vocab ctx) ^ " " ^ mn ^ " " ^ kn ^ " end)" end
  else if is_map tm then
    let val (f, m) = (rand (rator tm), rand tm)
        val (x, b) = dest_abs f
        val fn_ = fresh "f" and mn = fresh "m"
    in "(let val " ^ fn_ ^ " = (fn " ^ ident x ^ " => " ^ pure_exp b ^
       ")\n val " ^ mn ^ " = " ^ gen ctx selfname m ^
       "\n in " ^ #map (#vocab ctx) ^ " " ^ fn_ ^ " " ^ mn ^ " end)" end
  else if is_both tm then
    let val (m1, m2) = (rand (rator tm), rand tm)
        val an = fresh "c" and bn = fresh "c"
    in "(let val " ^ bn ^ " = " ^ gen ctx selfname m2 ^
       "\n val " ^ an ^ " = " ^ gen ctx selfname m1 ^
       "\n in " ^ #both (#vocab ctx) ^ " " ^ an ^ " " ^ bn ^ " end)" end
  else if is_cond tm then
    let val (b, m1, m2) = dest_cond tm
        val bn = fresh "b"
    in "(let val " ^ bn ^ " = " ^ pure_exp b ^ " in if " ^ bn ^ " then " ^
       gen ctx selfname m1 ^ "\n else " ^ gen ctx selfname m2 ^ " end)" end
  else if TypeBase.is_case tm then
    let val (_, x, rows) = TypeBase.dest_case tm
        fun row (pat, rhs) = pure_exp pat ^ " => " ^ gen ctx selfname rhs
        val sn = if is_var x then ident x else fresh "s"
        val cs = "(case " ^ sn ^ " of\n   " ^
                 String.concatWith "\n | " (map row rows) ^ ")"
    in if is_var x then cs
       else "(let val " ^ sn ^ " = " ^ pure_exp x ^ " in " ^ cs ^ " end)" end
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
      else if is_cond m then cond_tac ctx
      else if TypeBase.is_case m then case_tac ctx
      else call_tac ctx) g end

and bind_tac ctx (g as (asl, w)) =
  let
    val (p, act, b, snap, d, m) = goal_post g
    val d = valOf d
    val (m1, k) = (rand (rator m), rand m)
    val a = type_inv (res_ty m1)
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
    val lemma = instA (if guarded then #bind_guarded (#vocab ctx)
                       else #bind_d (#vocab ctx)) a
    val vv = mk_var ("v", v_ty)
    val app_tm = mk_app (p, spec_fun (#bind_d (#vocab ctx)), [mv, kv],
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
    val a = type_inv (res_ty m0)
    val fvs = free_varsl (w :: asl)
    val fname = fresh "f" and mn = fresh "m"
    val fv = mk_var (fname, v_ty) and mv = mk_var (mn, v_ty)
    val x = variant fvs (fst (dest_abs f))
    val xv = variant fvs (mk_var (fst (dest_var x) ^ "v", v_ty))
    val cont = list_mk_forall ([x, xv],
                 mk_imp (list_mk_comb (a, [x, xv]),
                   mk_returns (p, fv, [xv], mk_comb (b, mk_comb (f, x)))))
    val vv = mk_var ("v", v_ty)
    val app_tm = mk_app (p, spec_fun (#map_d (#vocab ctx)), [fv, mv],
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
     >- tr "map/lemma" (MATCH_MP_TAC (instA (#map_d (#vocab ctx)) a) >> side_tac ctx)) g
  end

and both_tac ctx (g as (asl, w)) =
  let
    val (p, act, b, snap, d, m) = goal_post g
    val d = valOf d
    val (m1, m2) = (rand (rator m), rand m)
    val a1 = type_inv (res_ty m1) and a2 = type_inv (res_ty m2)
    val av = mk_var (fresh "c", v_ty) and bv = mk_var (fresh "c", v_ty)
    val vv = mk_var ("v", v_ty)
    val app_tm = mk_app (p, spec_fun (#both_d (#vocab ctx)), [av, bv],
                   mk_postv vv (mk_COMPd (p, act, b, snap, d, m, vv)))
  in
    (xlet [ANTIQUOTE (mk_postv bv (mk_COMPd (p, act, a2, snap, d, m2, bv)))]
     >- prove_tac ctx >>
     xlet [ANTIQUOTE (mk_postv av (mk_COMPd (p, act, a1, snap, d, m1, av)))]
     >- prove_tac ctx >>
     SUBGOAL_THEN app_tm (fn th => xapp_spec th >> xsimpl)
     >- tr "both/lemma" (MATCH_MP_TAC (SPEC_ALL (#both_d (#vocab ctx))) >> side_tac ctx)) g
  end

and case_tac ctx g =
  let val (_, _, _, _, _, m) = goal_post g
      val (_, x, _) = TypeBase.dest_case m
      val inv = type_inv (type_of x)
      val defs = #defs ctx @ inv_defs inv
      val sv = mk_var (fresh "s", v_ty)
  in ((if is_var x then ALL_TAC
       else xlet [ANTIQUOTE (mk_postv sv (list_mk_comb (inv, [x, sv])))]
            >- pure_val_tac ctx x) >>
      tr "case" (Cases_on [ANTIQUOTE x] >> gvs defs >> xmatch) >> prove_tac ctx) g end

(* a final pure value (the body of map's function) *)
and pure_tac ctx g =
  let fun is_postv t = is_comb t andalso is_const (rator t) andalso
                       fst (dest_const (rator t)) = "POSTv"
      (* POSTv (λv. &(INV t v)) *)
      val t = (rand o rator o rand o snd o dest_abs o rand)
                (find_term is_postv (snd g))
              handle HOL_ERR _ => T
  in if is_param_call t then param_tac t g
     else if is_simple t orelse t ~~ T then
       (FIRST [xcon >> xsimpl >> simp (#defs ctx @ inv_defs (snd g)) >> NO_TAC,
               xvar >> xsimpl >> NO_TAC]) g
     else aux_tac t g end

(* the goal: the CF of an aux call, with post POSTv v. &INV t v *)
and aux_tac t g =
  let val (d, unit_arg) = aux_inst t
      val (_, args) = strip_comb (lhs (concl d))
  in (tr "aux/fold" (PURE_ONCE_REWRITE_TAC [GSYM d]) >>
      (if unit_arg
       then xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl)
       else ALL_TAC) >>
      tr "aux/xapp" (xapp >> xsimpl >>
        TRY (MAP_EVERY (fn y => qexists_tac [ANTIQUOTE y])
               (if unit_arg then [] else args)) >>
        simp [])) g
  end

(* the value of a pure argument a, as an xlet with post INV a av *)
and param_tac t (g as (asl, _)) =
  let val f = fst (strip_comb t)
      fun is_cert th = let val c = concl th
                           val (h, _) = strip_comb c
                       in is_const h andalso fst (dest_const h) = "Arrow" andalso
                          rand (rator c) ~~ f end handle HOL_ERR _ => false
  in tr "param" (first_assum (fn th => if is_cert th then xapp_spec th
                                       else NO_TAC) >>
                 TRY xsimpl >> simp [] >> TRY (metis_tac [])) g end

and pure_val_tac ctx a =
  if is_param_call a then param_tac a
  else if is_simple a then
    tr "arg" (xcon >> xsimpl >> simp (#defs ctx @ inv_defs (type_inv (type_of a))))
  else aux_tac a

and cond_tac ctx (g as (asl, w)) =
  let val (_, _, _, _, _, m) = goal_post g
      val (b, _, _) = dest_cond m
      val bv = mk_var (fresh "b", v_ty)
  in (xlet [ANTIQUOTE (mk_postv bv (list_mk_comb (type_inv bool, [b, bv])))]
      >- (if is_var b then (xvar >> xsimpl) else pure_val_tac ctx b) >>
      tr "if" xif >> TRY (asm_rewrite_tac []) >> prove_tac ctx) g
  end

(* a call of a primitive, of a translated function, or of f itself *)
and call_tac ctx (g as (asl, w)) =
  let
    val (p, act, b, snap, d, m) = goal_post g
    val (c, args) = strip_comb m
    (* let-bind the non-variable arguments, in order *)
    val lets = List.filter (not o is_var) args
    val names = map (fn _ => mk_var (fresh "a", v_ty)) lets
    fun xlet_arg (a, av) =
      xlet [ANTIQUOTE (mk_postv av (list_mk_comb (type_inv (type_of a), [a, av])))]
      >- pure_val_tac ctx a
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
  let val fvs = free_vars w
      fun scrut t = if is_cond t then #1 (dest_cond t)
                    else #2 (TypeBase.dest_case t)
      fun ok t = (is_cond t orelse TypeBase.is_case t) andalso
                 all (fn v => tmem v fvs) (free_vars (scrut t))
      val c = find_term ok w
  in Cases_on [ANTIQUOTE (scrut c)] g end

fun contr_step guards =
  FIRST [ho_match_mp_tac guarded_bind >> conj_tac >- (simp guards >> NO_TAC),
         ho_match_mp_tac nonexpansive_bind >> conj_tac,
         ho_match_mp_tac nonexpansive_map,
         ho_match_mp_tac nonexpansive_both >> conj_tac,
         simp [nonexpansive_const, nonexpansive_call, guarded_const] >> NO_TAC,
         gen_tac >> TRY BETA_TAC, case_split_tac >> simp [],
         IF_CASES_TAC]

fun wf_step wfs =
  FIRST [first_assum ACCEPT_TAC, simp wfs >> NO_TAC,
         irule wf_bind >> conj_tac, irule wf_map, irule wf_both >> conj_tac,
         gen_tac >> TRY BETA_TAC, case_split_tac >> simp [],
         IF_CASES_TAC]

(* define_async name nfixed ‘f a1 .. aj x1 .. xk = BODY’ guards wfs:
   a1 .. aj (j = nfixed) are fixed parameters (every recursive call passes
   them unchanged), x1 .. xk (k ≤ 2) vary; BODY calls f only under a
   guarded bind.  Defines name_body (the recursive call abstracted, over the
   tuple of x1 .. xk) and f a1 .. aj x1 .. xk = fix (name_body a1 .. aj)
   (x1, .., xk); proves contractiveness, the unfolding equation and wf. *)
fun define_async name nfixed q guards wfs =
  let
    val tm = Term q
    val (l, body) = dest_eq tm
    val (fvar, args) = strip_comb l
    val (fixed, xs) = (List.take (args, nfixed), List.drop (args, nfixed))
    val _ = length xs = 1 orelse length xs = 2 orelse
            raise ERR "define_async" "one or two varying parameters"
    val avoid = free_vars tm
    val ptm = if length xs = 1 then hd xs
              else variant avoid (mk_var ("p", type_of (pairSyntax.list_mk_pair xs)))
    val mty = type_of l
    val r = variant avoid (mk_var ("r", type_of ptm --> mty))
    (* the recursive calls f a1 .. aj y1 .. yk become r (y1, .., yk) *)
    val partial = list_mk_comb (fvar, fixed)
    val ys = map (fn x => variant avoid (mk_var (fst (dest_var x) ^ "'", type_of x))) xs
    val body1 = subst [partial |-> list_mk_abs (ys, mk_comb (r, pairSyntax.list_mk_pair ys))] body
    val body1 = rhs (concl (QCONV (DEPTH_CONV BETA_CONV) body1))
    val body1 = if length xs = 1 then body1
                else subst [hd xs |-> pairSyntax.mk_fst ptm,
                            el 2 xs |-> pairSyntax.mk_snd ptm] body1
    val bvar = mk_var (name ^ "_body",
                 foldr (fn (a, ty) => type_of a --> ty) (type_of r --> type_of ptm --> mty) fixed)
    val body_def = new_definition (name ^ "_body_def",
                     mk_eq (list_mk_comb (bvar, fixed @ [r, ptm]), body1))
    val bconst = fst (strip_comb (lhs (concl (SPEC_ALL body_def))))
    val bapp = list_mk_comb (bconst, fixed)
    val contr = store_thm (name ^ "_body_contractive",
      mk_icomb (prim_mk_const {Thy = "asyncCore", Name = "contractive"}, bapp),
      rw [contractive_def, body_def] >> REPEAT (contr_step guards))
    val fix_c = prim_mk_const {Thy = "asyncCore", Name = "fix"}
    val fixb = mk_icomb (fix_c, bapp)
    val def = new_definition (name ^ "_def",
                mk_eq (list_mk_comb (mk_var (name, type_of fvar), args),
                       mk_comb (fixb, pairSyntax.list_mk_pair xs)))
    val fconst = fst (strip_comb (lhs (concl (SPEC_ALL def))))
    val fix_eq = MATCH_MP fix_unfold contr
    val unfold = store_thm (name ^ "_unfold",
      list_mk_forall (args, subst [fvar |-> fconst] tm),
      rpt gen_tac >> PURE_ONCE_REWRITE_TAC [def] >>
      CONV_TAC (LAND_CONV (RATOR_CONV (REWR_CONV fix_eq))) >>
      simp [body_def, def])
    val wf = store_thm ("wf_" ^ name,
      list_mk_forall (args,
        mk_icomb (prim_mk_const {Thy = "asyncLevel1", Name = "wf"},
                  list_mk_comb (fconst, args))),
      rpt gen_tac >> PURE_ONCE_REWRITE_TAC [def] >>
      irule wf_fix >> simp [contr] >> rw [body_def] >>
      REPEAT (wf_step wfs))
  in {def = def, unfold = unfold, wf = wf, contractive = contr,
      body_def = body_def} end

(* ------------------------------------------------------------------------
   The driver
   ------------------------------------------------------------------------ *)

(* translate_async {name, unfold, prims, wfs, act, snap}:
   name   the CakeML name of the new function;
   unfold |- ∀xs. f xs = BODY (BODY may call f);
   prims  the primitives and previously translated functions;
   wfs    well-formedness theorems for the model terms (wf_both, ...);
   act, snap  the refinement relations of actions and of snapshots;
   vocab  the library's combinators (echo_vocab, or the socket library's);
   pre    extra preconditions on the parameters (e.g. fd < dimword(:64));
   defs   extra definitions for the proof's simp calls (e.g. SRESP_def).
   Returns the new function as a prim, with its COMP spec, for later calls. *)
fun translate_async {name, unfold, prims, wfs, act, snap, guard, vocab, pre,
                     defs} =
  let
    val th = SPEC_ALL unfold
    (* keep the model's type variables apart from the library's ('r, ...) *)
    val th = INST_TYPE (map (fn ty => ty |-> mk_vartype (dest_vartype ty ^ "m"))
                            (type_vars_in_term (concl th))) th
    (* instantiate the computation's event, response and action types to
       those of the vocabulary (act, snap) *)
    val (lhs0, _) = dest_eq (concl th)
    val snap_args = snd (dest_type (fst (dom_rng (type_of snap))))
    val act_ty = fst (dom_rng (type_of act))
    val (hist_ty, out_ty) = dom_rng (type_of lhs0)
    val snap_ty = hd (snd (dest_type hist_ty))
    val th = INST_TYPE
               (match_type snap_ty (mk_thy_type {Thy = "asyncCore", Tyop = "snapshot",
                                                  Args = snap_args}) @
                match_type (hd (snd (dest_type out_ty))) act_ty) th
    val (lhs_t, body) = dest_eq (concl th)
    val (f, xs) = strip_comb lhs_t
    val ctx0 = {self = f, self_v = T, prims = prims, wfs = wfs, defs = defs,
                vocab = vocab}
    val _ = check_guarded ctx0 body
    val code = "fun " ^ name ^ " " ^ String.concatWith " " (map ident xs) ^
               " =\n" ^ gen ctx0 name body ^ ";"
    val _ = print ("asyncTranslateLib: generated\n" ^ code ^ "\n")
    val _ = append_prog (process_topdecs [QUOTE code])
    val f_v = lhs (concl (DB.fetch "-" (name ^ "_v_def")))
    val ctx = {self = f, self_v = f_v, prims = prims, wfs = wfs, defs = defs,
               vocab = vocab}
    val p = mk_var ("p", “:'ffi ffi_proj”)
    val n = mk_var ("n", numSyntax.num)
    val vals = map (fn x => mk_var (ident x ^ "v", v_ty)) xs
    val hyps = list_mk_conj (map2 (fn x => fn xv =>
                 list_mk_comb (type_inv (type_of x), [x, xv])) xs vals
                 @ pre)
    val b = type_inv (res_ty lhs_t)
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
      rpt strip_tac >> irule app_COMP_of_approxd >> simp [] >> gen_tac >>
      metis_tac [spec_d])
  in {const = f, name = name, spec = spec, guard = guard,
      wf = TRUTH} : prim end

end
