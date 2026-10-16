(*
  The key-value server is quiescent (design/37, step E, model side).

  KV is the store server with query handlers, for the bodies protocol
  P_b: each complete request req on fd is a query Kv (fd, req) to the
  store (kv_delta, HttpKvSpec's kv_step), and the answer is printed as the
  response.

     kv_srv  = with_store kv_delta (λk. NONE)
                 (server_v sockV (λfd. proto_handler_v sockV P_b (kv_ansq fd) kv_fin (fd, "")) lfd)
     kv_srv2 = its Level 2 form, with_store2 Always over server_v2

  kv_stable and kv_sleeps are store_stable and store_sleeps for these
  parameters: in a world where finitely many things arrive, KV's polling
  run eventually does nothing, no query is pending, and nothing it waits
  for is ready; and R1's loop running KV blocks forever in select.

  This is the shape the final series' Level 2 KV program takes.  The
  existing Level 1 kv_server (asyncKvModel, kv_handler over
  server_with_k) agrees with kv_srv on the store's histories
  (spike/kv-live's kv_proto_agree and server_with_k_eq_v, at the
  transcript level); relating their polling runs is left to the final
  series.

  MAIN: kv_stable, kv_sleeps.
*)
Theory asyncKvQuiet
Ancestors
  pair list rich_list arithmetic option pred_set words
  asyncCore asyncLevel1 asyncLevel2 asyncServer asyncM4GRounds
  asyncM4SockModel asyncServerV asyncProto asyncProtoV asyncProtoV2
  asyncProtoB asyncWithStore asyncWithStore2 asyncServerVKv HttpSpec
  HttpSpecBodies HttpKvSpec asyncHttpParseB asyncKvModel asyncStoreStable
  asyncOCBusy asyncStoreQuiet QuietSpec
Libs
  preamble

(* KV's query: the request itself, tagged with its connection *)
Definition kv_ansq_def:
  kv_ansq (fd : num) (req : brequest) = SOME (fd, req)
End

(* KV's response: the store's answer, printed *)
Definition kv_fin_def:
  kv_fin (req : brequest) (k : HttpSpec$response option) =
    case k of SOME ans => print_response ans | NONE => ""
End

Theorem kv_ansq_tags:
  ∀fd req q. kv_ansq fd req = SOME q ⇒ FST q = fd
Proof
  rw[kv_ansq_def] >> simp[]
QED

(* MAIN (Q1 for KV) *)
Theorem kv_stable:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
    gacts (EI lfdn) (srelabel (SM kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn)) s0 n = [] ∧
    ¬kv_pending kv_delta (λk. NONE) (server_v sockV (HQ P_b kv_ansq (K kv_fin)) lfdn)
       (MAP sfs (ghist (EI lfdn)
                   (srelabel (SM kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn)) s0 n)) ∧
    ∀x. Readable x ∈
          waiting_on (SM2 kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn)
            (MAP sfs (ghist (EI lfdn)
                        (srelabel (SM kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn)) s0 n)) ⇒
        ¬is_ready (gstate (EI lfdn)
                     (srelabel (SM kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn)) s0 n)
                  (n2w x)
Proof
  strip_tac >> irule store_stable >> rw[proto_ok_b, kv_ansq_def] >> rw[]
QED

(* MAIN (Q2 for KV): R1's loop running KV blocks forever in select *)
Theorem kv_sleeps:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃n kept N s.
    lbgroundsB (SM2 kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn) [n2w lfdn] s0 n =
      SOME (kept, N, s) ∧
    new_actions (log_of (srelabel (SM2 kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn).run))
      kept = [] ∧
    ¬busy (SM2 kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn) (MAP sfs kept) ∧
    sock_wait (qsel (srelabel2 (SM2 kv_delta (λk. NONE) P_b kv_ansq (K kv_fin) lfdn)) kept) s
      = NONE
Proof
  strip_tac >> irule store_sleeps >> rw[proto_ok_b, kv_ansq_def] >> rw[]
QED
