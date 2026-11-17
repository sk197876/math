(** Supporting Federer (1969), 3.2.45, p. 279:
    normalizer convergence along arbitrary admissible real
    exponent sequences. Reuse the complete scalar norm
    continuity of 2.4.17, including the infinity endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic EuclideanInnerProduct
  EuclideanProjectionMetric ExteriorDiameterUP ExteriorNorm
  OrthogonalProjectionConstants ProjectionConstantNorms ProjectionBeta ProjectionBetaContinuity
  OrthogonalProjectionProbability BoundedProbabilityExponentNorm
  MeasureExponentDomain ExtendedRealOrderLimit ExtendedRealLimitBounds ExtendedOrderLimitTopology
  MeasureExponentFinitePartLimits FiniteExponentPart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_beta_admissible_sequence_limit]:
    supporting removal of the normalizers in Federer 3.2.45,
    p. 279. The real exponents may approach from either
    side and need not be monotone. The limiting exponent
    may be infinity. The original projection norm identity
    and the complete existing scalar norm limit supply the proof. *)
Theorem projection_beta_admissible_sequence_limit (R : realType) (n m : nat)
    (hMN : (m <= n)%N) (p : nat -> R) (t : \bar R) :
  (forall j, (1 <= p j)%R) ->
  extended_order_limit (fun j => (p j)%:E) t ->
  extended_order_limit (fun j => (@projection_beta R n m hMN (p j)%:E)%:E)
    (@projection_beta R n m hMN t)%:E.
Proof.
move=> hP hLimit.
have hT : 1 <= t.
  apply: (@extended_order_limit_lower_bound R (fun j => (p j)%:E) t 1 hLimit)=> j.
  exact: hP j.
have [xi [hSimple hUnit]] := @euclidean_simple_unit_vector_exists R n m hMN.
pose mu := @orthogonal_projection_probability R n m hMN.
have hMu := @theta_star_is_measure R n m hMN.
pose g (q : orthogonal_projection_metric_space R n m) :
    real_norm_metric_space (scalar_absolute_value_norm R) :=
  projection_norm (real_exterior_two_nonzero R) xi q.
have hG := @simple_projection_norm_scalar_measurable R n m hMN xi hSimple.
have hBound q : (`|g q| <= 1)%R.
  rewrite /g (ger0_norm (projection_norm_nonnegative (real_exterior_two_nonzero R) xi q)).
  by rewrite -hUnit; exact: projection_norm_bound.
have hFinite j : finite_exponent_part (measure_finite_norm_exponents mu (partial_function_total g))
    (p j)%:E.
  split; last by rewrite fin_numE.
  split; first exact: hP j.
  exact: (@bounded_probability_exponent_norm_finite R _ mu hMu g 1%R (p j)%:E
    (@theta_star_total R n m hMN) ltr01 hBound (hP j) hG).
have hTopLimit := (extended_order_limit_topology_iff (fun j => (p j)%:E) t).2 hLimit.
have hNormTop := @measure_exponent_finite_part_sequential_limit R _ mu hMu g hG
  (fun j => (p j)%:E) t hFinite hTopLimit.
have hNormLimit := (extended_order_limit_topology_iff _ _).1 hNormTop.
have hValue s (hS : 1 <= s) :
    measure_exponent_norm mu (partial_function_total g) s = (@projection_beta R n m hMN s)%:E.
  exact: (@projection_beta_scalar_norm_value R n m hMN xi s hSimple hUnit hS).
have hSequence : (fun j => measure_exponent_norm mu (partial_function_total g) (p j)%:E) =
    (fun j => (@projection_beta R n m hMN (p j)%:E)%:E).
  apply: funext=> j.
  have hJ : 1 <= (p j)%:E by rewrite lee_fin.
  exact (hValue (p j)%:E hJ).
by rewrite hSequence (hValue t hT) in hNormLimit.
Qed.
