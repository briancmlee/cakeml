(*
  protoInterface: the framed request protocol interface (design/32 §2.1).

  A protocol is a validity predicate, a printer and a parser for requests
  of some type 'r.  proto_ok states the four facts the server pipelines
  use about a parser (P1-P4); every lemma below is derived from them
  alone, once, for every protocol:

     proto_unique            printed valid requests frame uniquely
     proto_extend            a complete parse survives reading more
     proto_prefix            a proper prefix of a printed request is incomplete
     proto_all_*             all complete requests at the front of a buffer

  The generic spec vocabulary (proto_safe, proto_live, proto_spec) has
  exactly the shapes of HttpGetSpec's, HttpHeadersSpec' and HttpSpec'
  statements; each is an instance by an equality lemma
  (../http-proto-inst).  No trusted file is changed.
*)
Theory protoInterface
Ancestors
  EchoSpec HttpGetSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   The interface
   ------------------------------------------------------------------------ *)

(* What a parser says about a buffer: a request and the rest, not yet
   enough bytes, or never a request *)
Datatype:
  presult = PComplete 'r string | PIncomplete | PInvalid
End

Datatype:
  proto = <| valid : 'r -> bool; print : 'r -> string;
             parse : string -> 'r presult |>
End

(* MAIN: the four obligations of a protocol.
   P1  a printed valid request, followed by anything, parses back;
   P2  a complete parse is a printed valid request and the rest;
   P3  an invalid buffer is never the start of a printed valid request,
       however it is extended;
   P4  printed valid requests are not empty. *)
Definition proto_ok_def:
  proto_ok P ⇔
    (∀r rest. P.valid r ⇒ P.parse (P.print r ++ rest) = PComplete r rest) ∧
    (∀s r rest. P.parse s = PComplete r rest ⇒
                P.valid r ∧ s = P.print r ++ rest) ∧
    (∀s t r rest. P.parse s = PInvalid ∧ P.valid r ⇒
                  s ++ t ≠ P.print r ++ rest) ∧
    (∀r. P.valid r ⇒ P.print r ≠ [])
End

Theorem proto_print:
  proto_ok P ∧ P.valid r ⇒ P.parse (P.print r ++ rest) = PComplete r rest
Proof
  rw[proto_ok_def]
QED

Theorem proto_complete:
  proto_ok P ∧ P.parse s = PComplete r rest ⇒
  P.valid r ∧ s = P.print r ++ rest
Proof
  rw[proto_ok_def] >> metis_tac[]
QED

Theorem proto_invalid:
  proto_ok P ∧ P.parse s = PInvalid ∧ P.valid r ⇒ s ++ t ≠ P.print r ++ rest
Proof
  rw[proto_ok_def] >> metis_tac[]
QED

Theorem proto_nonempty:
  proto_ok P ∧ P.valid r ⇒ P.print r ≠ []
Proof
  rw[proto_ok_def]
QED

(* ------------------------------------------------------------------------
   Derived, once
   ------------------------------------------------------------------------ *)

(* MAIN: printed valid requests frame uniquely (the bite lemma) *)
Theorem proto_unique:
  proto_ok P ∧ P.valid r1 ∧ P.valid r2 ∧ P.print r1 ++ x = P.print r2 ++ y ⇒
  r1 = r2 ∧ x = y
Proof
  strip_tac >>
  ‘P.parse (P.print r1 ++ x) = PComplete r1 x’ by simp[proto_print] >>
  ‘P.parse (P.print r2 ++ y) = PComplete r2 y’ by simp[proto_print] >>
  qpat_x_assum ‘P.print r1 ++ x = _’ (fn th => fs[th])
QED

Theorem proto_complete_shorter:
  proto_ok P ∧ P.parse s = PComplete r rest ⇒ LENGTH rest < LENGTH s
Proof
  strip_tac >> drule_all proto_complete >> strip_tac >>
  drule_all proto_nonempty >> Cases_on ‘P.print r’ >> gvs[]
QED

(* A complete parse survives reading more *)
Theorem proto_extend:
  proto_ok P ∧ P.parse s = PComplete r rest ⇒
  P.parse (s ++ t) = PComplete r (rest ++ t)
Proof
  strip_tac >> drule_all proto_complete >> rw[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[proto_print]
QED

(* A proper prefix of a printed valid request is incomplete: neither a
   complete parse (framing is unique) nor invalid (P3) *)
Theorem proto_prefix:
  proto_ok P ∧ P.valid r ∧ s ++ u = P.print r ∧ u ≠ [] ⇒
  P.parse s = PIncomplete
Proof
  strip_tac >> Cases_on ‘P.parse s’ >> simp[]
  >- (rename1 ‘PComplete q rest’ >> drule_all proto_complete >> strip_tac >>
      ‘q = r ∧ rest ++ u = []’ suffices_by simp[] >>
      irule proto_unique >> qexists_tac ‘P’ >> gvs[] >>
      metis_tac[APPEND_ASSOC, APPEND_NIL])
  >- (drule_all proto_invalid >>
      disch_then (qspecl_then [‘u’, ‘[]’] mp_tac) >> simp[])
QED

(* ------------------------------------------------------------------------
   All complete requests at the front of a buffer
   ------------------------------------------------------------------------ *)

(* The length check makes termination independent of proto_ok; under
   proto_ok it always holds (proto_all_complete) *)
Definition proto_all_def:
  proto_all P s =
    case P.parse s of
      PComplete r rest =>
        if LENGTH rest < LENGTH s then r :: proto_all P rest else []
    | _ => []
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ >> simp[]
End

Theorem proto_all_complete:
  proto_ok P ∧ P.parse s = PComplete r rest ⇒
  proto_all P s = r :: proto_all P rest
Proof
  strip_tac >> drule_all proto_complete_shorter >>
  simp[Once proto_all_def]
QED

Theorem proto_all_not_complete:
  (∀r rest. P.parse s ≠ PComplete r rest) ⇒ proto_all P s = []
Proof
  simp[Once proto_all_def] >> CASE_TAC >> simp[]
QED

(* MAIN: printed valid requests, followed by a rest that does not start
   with a printed valid request, parse to exactly those requests *)
Theorem proto_all_requests:
  ∀rs. proto_ok P ∧ EVERY P.valid rs ∧
       (∀r more. P.valid r ⇒ rest ≠ P.print r ++ more) ⇒
       proto_all P (FLAT (MAP P.print rs) ++ rest) = rs
Proof
  Induct >> rw[]
  >- (irule proto_all_not_complete >> rpt strip_tac >>
      drule_all proto_complete >> metis_tac[]) >>
  ‘P.parse (P.print h ++ (FLAT (MAP P.print rs) ++ rest)) =
   PComplete h (FLAT (MAP P.print rs) ++ rest)’ by simp[proto_print] >>
  drule_all proto_all_complete >> REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED

(* Printed requests in front of any buffer *)
Theorem proto_all_print:
  ∀rs. proto_ok P ∧ EVERY P.valid rs ⇒
       proto_all P (FLAT (MAP P.print rs) ++ s) = rs ++ proto_all P s
Proof
  Induct >> rw[] >>
  ‘P.parse (P.print h ++ (FLAT (MAP P.print rs) ++ s)) =
   PComplete h (FLAT (MAP P.print rs) ++ s)’ by simp[proto_print] >>
  drule_all proto_all_complete >> REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED

Theorem proto_all_printed:
  proto_ok P ∧ EVERY P.valid rs ⇒ proto_all P (FLAT (MAP P.print rs)) = rs
Proof
  strip_tac >>
  ‘proto_all P [] = []’ by (simp[Once proto_all_def] >> CASE_TAC >> simp[]) >>
  drule_all proto_all_print >> disch_then (qspec_then ‘[]’ mp_tac) >> simp[]
QED

(* MAIN (helper): reading more can only add complete requests at the end *)
Theorem proto_all_mono:
  ∀s t. proto_ok P ⇒ proto_all P s ≼ proto_all P (s ++ t)
Proof
  gen_tac >> completeInduct_on ‘LENGTH s’ >> rw[] >>
  Cases_on ‘P.parse s’ >> simp[Once proto_all_def] >>
  drule_all proto_complete_shorter >> strip_tac >> simp[] >>
  drule_all proto_extend >> disch_then (qspec_then ‘t’ assume_tac) >>
  drule_all proto_all_complete >> simp[]
QED

Theorem proto_all_prefix:
  proto_ok P ∧ s ≼ t ⇒ proto_all P s ≼ proto_all P t
Proof
  strip_tac >> gvs[IS_PREFIX_APPEND] >> metis_tac[proto_all_mono, IS_PREFIX_APPEND]
QED

(* An invalid buffer contributes no requests, however it is extended *)
Theorem proto_all_invalid_ext:
  proto_ok P ∧ P.parse b = PInvalid ⇒ proto_all P (b ++ x) = []
Proof
  strip_tac >> irule proto_all_not_complete >> rpt strip_tac >>
  drule_all proto_complete >> strip_tac >>
  drule_all proto_invalid >>
  disch_then (qspecl_then [‘x’, ‘rest’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The generic spec vocabulary (the shapes of HttpGetSpec's statements; not
   trusted: each trusted spec is an instance by an equality lemma)
   ------------------------------------------------------------------------ *)

Definition preqs_def:
  preqs P rs = bytes (FLAT (MAP P.print rs))
End

Definition presps_def:
  presps (resp : 'r -> string) rs = bytes (FLAT (MAP resp rs))
End

(* rest does not start with a complete valid request *)
Definition no_full_def:
  no_full P rest ⇔ ∀r. P.valid r ⇒ ¬(preqs P [r] ≼ rest)
End

(* Safety: what the server has written on a connection is a prefix of the
   responses to the complete requests it has read *)
Definition proto_safe_def:
  proto_safe P resp io ⇔
    ∀evs c rs rest.
      LPREFIX (fromList evs) io ∧ EVERY P.valid rs ∧
      bytes_read_from c evs = preqs P rs ++ rest ∧ no_full P rest ⇒
      bytes_written_to c evs ≼ presps resp rs
End

(* Liveness: the responses to the requests a client has sent are
   eventually written *)
Definition proto_live_def:
  proto_live P resp sk io ⇔
    ∀c n rs.
      EVERY P.valid rs ∧ preqs P rs ≼ sent_upto c n sk ⇒
      ∃evs. LPREFIX (fromList evs) io ∧
            presps resp rs ≼ bytes_written_to c evs
End

(* The statement, for a protocol P answered by resp *)
Definition proto_spec_def:
  proto_spec P resp lfd (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              proto_safe P resp io ∧ proto_live P resp sk io
End
