(*
  protoEnvLive: the generic handler answers everything owed, in any
  environment satisfying design/34's four facts (henv), stated on the
  handler's own transcript (design/32 §2.9, phase 3).

  proto_env_live is design/34's handler_live obligation for proto_handler,
  with henv spelled out: once asyncSWLive (henv, handler_live, sw_live)
  lands, proto_handler_live is its unfolding.  The bound is
  pmachine_live_p's: (|D| + 2)(K + 3) rounds, K the number of complete
  requests in D.

  The bridge from henv to the machine's hypotheses (as m4-server's for _b):
    waiting, fd not readable  ⇒ D read by the next round, and nothing is
                                read in a round that is not a read (Rj_Wj_SUC);
    reading (state PB)        ⇒ an outstanding read in the transcript
                                (pmachine_reading);
    stopped, not invalid      ⇒ an end-of-file read in the transcript
                                (pmachine_eof).
*)
Theory protoEnvLive
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncTranscript echoServer libModel echoProgress
  protoInterface protoServer protoMachine protoDrain
Libs
  BasicProvers

(* What the handler of fd, started on an empty buffer, has read after the
   first j snapshots of g (design/34's hread, for this handler) *)
Overload PR = “λP resp fd g j.
  CONCAT (read fd (trans (proto_handler P resp (fd, "")) (TAKE j g)))”

Theorem pcomp_PA_NIL[local]:
  pcomp P resp fd (PA "") = proto_handler P resp (fd, "")
Proof
  simp[pcomp_def]
QED

(* MAIN: the generic handler is live in every environment satisfying the
   four facts: what it has read and D are comparable; fd not reported
   readable means D is read by the next round; an outstanding read, D not
   yet read, reads all of D or something; end-of-file comes after D.
   Then within (|D| + 2)(K + 3) rounds of j0 it has written the responses
   to the K complete requests in D. *)
Theorem proto_env_live:
  proto_ok P ∧ prompt (proto_handler P resp (fd, "")) g ∧
  (∀j. j0 ≤ j ∧ j ≤ LENGTH g ⇒ PR P resp fd g j ≼ D ∨ D ≼ PR P resp fd g j) ∧
  (∀j. j0 ≤ j ∧ j < LENGTH g ∧ Readable fd ∉ (EL j g).ready ⇒
       D ≼ PR P resp fd g (SUC j)) ∧
  (∀j. j0 ≤ j ∧ j < LENGTH g ∧
       MEM (Read fd, NONE) (trans (proto_handler P resp (fd, "")) (TAKE j g)) ∧
       ¬(D ≼ PR P resp fd g j) ⇒
       D ≼ PR P resp fd g (SUC j) ∨
       LENGTH (PR P resp fd g j) < LENGTH (PR P resp fd g (SUC j))) ∧
  (∀j. j0 ≤ j ∧ j ≤ LENGTH g ∧
       MEM (Read fd, SOME Eof) (trans (proto_handler P resp (fd, "")) (TAKE j g)) ⇒
       D ≼ PR P resp fd g j) ∧
  j0 + (LENGTH D + 2) * (LENGTH (proto_all P D) + 3) ≤ LENGTH g ⇒
  ∃j. j ≤ LENGTH g ∧
      MAP resp (proto_all P D) ≼
        written fd (trans (proto_handler P resp (fd, "")) (TAKE j g))
Proof
  strip_tac >>
  mp_tac (UNDISCH (SPEC_ALL pmachine_live_p)) >>
  REWRITE_TAC[pcomp_PA_NIL] >>
  impl_tac
  >- (rpt conj_tac >> rpt strip_tac >- simp[]
      (* comparable *)
      >- simp[]
      (* waiting while not readable: D read next round, and nothing new read *)
      >- (‘D ≼ PR P resp fd g (SUC j)’ by simp[] >>
          mp_tac (Rj_Wj_SUC |> SPEC_ALL |> REWRITE_RULE [pcomp_PA_NIL]) >>
          impl_tac >- simp[] >> strip_tac >>
          ‘PR P resp fd g (SUC j) = PR P resp fd g j’
            by (first_x_assum irule >> simp[]) >>
          fs[])
      (* reading: an outstanding read *)
      >- (first_x_assum irule >> simp[] >>
          mp_tac (pmachine_reading |> SPEC_ALL |> REWRITE_RULE [pcomp_PA_NIL]) >>
          simp[])
      (* stopped, not invalid: end-of-file was read *)
      >> first_x_assum irule >> simp[] >>
      mp_tac (pmachine_eof |> SPEC_ALL |> REWRITE_RULE [pcomp_PA_NIL]) >>
      simp[])
  >> disch_then (qspecl_then [‘LENGTH D’, ‘j0’] mp_tac) >> simp[]
QED
