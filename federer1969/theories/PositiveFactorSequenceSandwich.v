(** Scalar order-limit support for Federer (1969), 3.2.45,
    p. 279. Multiplicative comparisons tending to one
    retain arbitrary nonnegative extended measure values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealScalarOrderLimits PositiveReciprocalOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_factor_fixed_extended_limit]: supporting
    multiplication limit for Federer 3.2.45, p. 279.
    A positive real sequence tending to one may multiply
    any fixed nonnegative extended value, including zero
    and infinity, without changing its limit. *)
Lemma positive_factor_fixed_extended_limit (R : realType) (w : nat -> R) (z : \bar R) :
  (forall j, (0 < w j)%R) -> 0 <= z ->
  extended_order_limit (fun j => (w j)%:E) 1 ->
  extended_order_limit (fun j => (w j)%:E*z) z.
Proof.
move=> hW hZ hLimit.
case: z hZ=> [a| |] hZ.
- have h := @real_scalar_order_limit R w 1 a hLimit.
  have hSequence : (fun j => (w j)%:E*a%:E) = (fun j => (a*w j)%R%:E).
    by apply: funext=> j; rewrite -EFinM mulrC.
  rewrite mulr1 in h; by rewrite hSequence.
- have hSequence : (fun j => (w j)%:E * +oo) = (fun _ : nat => (+oo : \bar R)).
    apply: funext=> j; exact: gt0_muley (lte_tofin (hW j)).
  rewrite hSequence; split.
  + move=> c hC; exists 0%N=> j _; exact hC.
  + move=> c hC; by move: hC; rewrite ltNge leey.
- by move: hZ; rewrite leNgt ltNyr.
Qed.

(** Source for [positive_factor_sequence_sandwich]: supporting
    final limit transfer for Federer 3.2.45, p. 279.
    If both z<=w_j u_j and u_j<=w_j z hold, with positive
    finite w_j tending to one, then u_j tends to z.
    Infinite z and u_j are retained; no subtraction or
    division of infinite measure values is introduced. *)
Theorem positive_factor_sequence_sandwich (R : realType) (w : nat -> R)
    (u : nat -> \bar R) (z : \bar R) :
  (forall j, (0 < w j)%R) -> 0 <= z ->
  extended_order_limit (fun j => (w j)%:E) 1 ->
  (forall j, z <= (w j)%:E*u j) -> (forall j, u j <= (w j)%:E*z) ->
  extended_order_limit u z.
Proof.
move=> hW hZ hLimit hLower hUpper.
have hInversePositive j : (0 < (w j)^-1)%R by rewrite invr_gt0.
have hInverse := @positive_reciprocal_order_limit R w 1 hW (@ltr01 R) hLimit.
rewrite invr1 in hInverse.
have hLowerLimit := @positive_factor_fixed_extended_limit R (fun j => ((w j)^-1)%R) z
  hInversePositive hZ hInverse.
have hUpperLimit := @positive_factor_fixed_extended_limit R w z hW hZ hLimit.
have hLowerBound j : ((w j)^-1)%R%:E*z <= u j.
  have h := lee_wpmul2l (lee_tofin (ltW (hInversePositive j))) (hLower j).
  by rewrite muleA -EFinM mulVf ?(lt0r_neq0 (hW j)) // mul1e in h.
split.
- move=> c hC; have [N hN] := hLowerLimit.1 c hC.
  exists N=> j hJ; exact: lt_le_trans (hN j hJ) (hLowerBound j).
- move=> c hC; have [N hN] := hUpperLimit.2 c hC.
  exists N=> j hJ; exact: le_lt_trans (hUpper j) (hN j hJ).
Qed.
