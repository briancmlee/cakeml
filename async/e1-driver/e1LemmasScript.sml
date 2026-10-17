(*
  Lemmas the E1 programs' Main and Sem theories share (client: e1ClientMain,
  e1ClientSem; proxy: proxyMain, proxySem).

  Arrow_app1/2/3: partial applications of translated functions as CF apps.
  limited_parts_l0, l0_part_in_heap, l0_init_heap, FFI_part_hprop_L0_EV:
  the L0 world as a program's only FFI part (honestEchoL0Sem's lemmas,
  which are outside these directories' INCLUDES).
*)
Theory e1Lemmas
Ancestors
  ml_translator cfHeapsBase cfApp cfMain cfStore
  honestL0 honestL0World honestL0Part honestL0Proof
Libs
  preamble ml_translatorLib cfLib

(* ------------------------------------------------------------------------
   Partial applications of translated functions
   ------------------------------------------------------------------------ *)

Theorem Arrow_app1:
  (a --> b) f fv ∧ a x xv ⇒
  app (p:'ffi ffi_proj) fv [xv] emp (POSTv v. &b (f x) v)
Proof
  rw[app_def] >> metis_tac[Arrow_IMP_app_basic]
QED

Theorem Arrow_app2:
  (a --> b --> c) f fv ∧ a x xv ∧ b y yv ⇒
  app (p:'ffi ffi_proj) fv [xv; yv] emp (POSTv v. &c (f x y) v)
Proof
  rw[app_def] >> drule_all Arrow_IMP_app_basic >>
  disch_then (qspec_then ‘p’ assume_tac) >>
  irule app_basic_weaken >> first_assum (irule_at Any) >>
  Cases >> simp[POSTv_def, cond_def, SEP_EXISTS_THM, STAR_def] >>
  strip_tac >> qexistsl [‘emp’, ‘∅’] >> simp[emp_def, SPLIT_def] >>
  drule_all Arrow_IMP_app_basic >> disch_then (qspec_then ‘p’ mp_tac) >>
  simp[POSTv_def, cond_def, emp_def]
QED

Theorem Arrow_app3:
  (a --> b --> c --> d) f fv ∧ a x xv ∧ b y yv ∧ c z zv ⇒
  app (p:'ffi ffi_proj) fv [xv; yv; zv] emp (POSTv v. &d (f x y z) v)
Proof
  rpt strip_tac >> drule_all Arrow_IMP_app_basic >>
  disch_then (qspec_then ‘p’ assume_tac) >>
  simp[Once app_def] >> irule app_basic_weaken >> first_assum (irule_at Any) >>
  Cases >> simp[POSTv_def, cond_def, SEP_EXISTS_THM, STAR_def] >>
  strip_tac >>
  ‘app p v [yv; zv] emp (POSTv v'. &d (f x y z) v')’ by (irule Arrow_app2 >> metis_tac[]) >>
  qexistsl [‘emp’, ‘∅’] >> simp[emp_def, SPLIT_def] >> gvs[emp_def, POSTv_def, cond_def]
QED

(* ------------------------------------------------------------------------
   The L0 world as the program's only FFI part
   ------------------------------------------------------------------------ *)

Theorem limited_parts_l0:
  limited_parts l0_names (l0_proj w0)
Proof
  simp[limited_parts_def, l0_proj_def]
QED

Theorem l0_part_in_heap:
  st.ffi = l0_ffi w0 ∧ parts_ok st.ffi (l0_proj w0) ⇒
  FFI_part (l0_enc w0 w0) (l0_next w0) l0_names [] ∈ st2heap (l0_proj w0) st
Proof
  strip_tac >> gvs[st2heap_def, l0_proj_def, ffi2heap_def] >>
  simp[l0_ffi_def, l0_names_def] >>
  disj2_tac >> rw[FUPDATE_LIST_THM, FLOOKUP_UPDATE]
QED

Theorem l0_init_heap:
  st.ffi = l0_ffi w0 ∧ l0_rely w0 ∧ w0.hist = [] ⇒
  ∃h1 h2. SPLIT (st2heap (l0_proj w0) st) (h1,h2) ∧ L0_EV w0 w0 [] h1
Proof
  strip_tac >>
  ‘parts_ok st.ffi (l0_proj w0)’ by simp[l0_parts_ok] >>
  drule_all l0_part_in_heap >> strip_tac >>
  qexistsl [‘{FFI_part (l0_enc w0 w0) (l0_next w0) l0_names []}’,
            ‘st2heap (l0_proj w0) st DIFF {FFI_part (l0_enc w0 w0) (l0_next w0) l0_names []}’] >>
  simp[L0_EV_def, l0_reach_init, SEP_CLAUSES, one_def] >>
  rw[SPLIT_def, EXTENSION, IN_DISJOINT] >> metis_tac[]
QED

Theorem FFI_part_hprop_L0_EV:
  FFI_part_hprop (L0_EV w0 w evs)
Proof
  simp[L0_EV_def] >> irule FFI_part_hprop_STAR >> disj1_tac >>
  simp[FFI_part_hprop_def, one_def]
QED
