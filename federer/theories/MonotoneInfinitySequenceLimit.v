(** Elementary order-limit connection for Federer (1969),
    3.2.45, p. 279: a monotone family reaches its
    infinity endpoint along every cofinal exponent sequence. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [monotone_infinity_sequence_limit]: supporting
    order-topology helper for the corrected infinity proof
    in Federer 3.2.45, p. 279. A nondecreasing family
    whose finite exponents exceed every strict lower bound
    on its infinity value converges to that value along
    every admissible exponent sequence tending to infinity.
    No finiteness or strict positivity of the values is required. *)
Theorem monotone_infinity_sequence_limit (R : realType) (F : \bar R -> \bar R)
    (p : nat -> \bar R) :
  (forall s t, 1 <= s -> s <= t -> F s <= F t) ->
  (forall c, c < F +oo -> exists r : R, (1 <= r)%R /\ c < F r%:E) ->
  (forall j, 1 <= p j) -> extended_order_limit p +oo ->
  extended_order_limit (fun j => F (p j)) (F +oo).
Proof.
move=> hMono hCofinal hP hLimit; split.
- move=> c hC.
  have [r [hR hValue]] := hCofinal c hC.
  have [N hN] := hLimit.1 r%:E (ltry r).
  exists N=> j hJ.
  have hR1 : 1 <= r%:E by rewrite lee_fin.
  exact: lt_le_trans hValue (hMono r%:E (p j) hR1 (ltW (hN j hJ))).
- move=> c hC; exists 0%N=> j _.
  exact: le_lt_trans (hMono (p j) +oo (hP j) (leey _)) hC.
Qed.
