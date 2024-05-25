(*
 An example showing how to use the monadic translator to translate polymorphic
 monadic array quicksort, including exceptions.
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "promise"

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
(* TODO still some problems with type variables - if 'a not used below,
   some translations fail *)

Datatype:
  snapshot = Snapshot (int list)
End
val _ = register_type “:snapshot”;

Type Promise = “:snapshot -> α option”

Datatype:
  state_refs = <| arr : α option; arr2 : α option; phantom: (α # α) option |>
End

val state_type = ``:α state_refs``;

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

Type M = “:α state_refs -> ('c,state_exn) exc # α state_refs”

val config =  local_state_config |>
              with_state state_type |>
              with_exception ``:state_exn`` |>
              with_refs [
                  ("arr", “NONE:(α option)”),
                  ("arr2", “NONE:(α option)”),
                  ("phantom", “NONE:(α#α) option”)];

val _ = start_translation config;

Definition create_def:
  create (p:snapshot->bool) (f:unit->'a) (s:snapshot) =
  do
    cached <- get_arr;
    dtcase cached of
      SOME result => return (SOME result)
    | NONE =>
        if (p s)
        then (do
               result <<- f ();
               set_arr (SOME result);
               return (SOME result)
             od)
        else (return NONE)
  od
End
val create_v_thm = create_def |> m_translate;

Definition run_create_def:
  run_create p f s = run (create p f s) <| arr := NONE; arr2 := NONE |>
End
val run_create_v_thm = m_translate_run run_create_def;

val OPTION_MAP_v_thm = translate optionTheory.OPTION_MAP_DEF;

Definition map_def:
  map (p:snapshot->'c option) (f:'c->'a) (s:snapshot) =
  do
    cached <- get_arr;
    dtcase cached of
      SOME result => return (SOME result)
    | NONE => (do
                result <<- OPTION_MAP f (p s);
                set_arr result;
                return NONE
              od)
  od
End
val map_v_thm = map_def |> m_translate;

Definition run_map_def:
  run_map p f s = run (map p f s) <| arr := NONE; arr2 := NONE |>
End
val run_map_v_thm = m_translate_run run_map_def;

Definition join_def:
  join (p:snapshot->snapshot->'c option) = \s. (p s) s
End
val join_v_thm = translate join_def;

(* Definition bind_def: *)
(*   bind (m:snapshot->'a option) (f:'a->snapshot->'b option) (s:snapshot) = *)
(*   do *)
(*     mapped <- map m f s; *)
(*     dtcase mapped of *)
(*       NONE => return NONE *)
(*     | SOME m => return (m s) *)
(*   od *)
(* End *)
(* val bind_v_thm = bind_def |> m_translate; *)


val _ = export_theory ();
