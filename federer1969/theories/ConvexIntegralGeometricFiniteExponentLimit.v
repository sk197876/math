(** Finite-exponent continuity of the original Q_t,
    Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricMeasure
  ConvexIntegralGeometricFiniteExponentComparison ProjectionBeta ProjectionBetaAdmissibleSequenceLimit
  MeasureUP ExtendedRealOrderLimit RealErrorOrderLimit RealScalarOrderLimits
  RealExponentialUP RealExponentialSealed RealExponentialOrderLimit
  PositiveFactorSequenceSandwich PositiveNormalizationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_finite_exponent_sequence_limit]:
    the finite-exponent part of the continuity assertion in
    Federer 3.2.45, p. 279. Every sequence p_j>=1
    tending to q>=1 has Q_p_j(A) tending to Q_q(A).
    The sequence may approach from both sides. The original
    set A is arbitrary, with zero and infinite masses included. *)
Theorem convex_integral_geometric_finite_exponent_sequence_limit (R : realType) n m
    (hMN : (m <= n)%N) (p : nat -> R) (q : R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (forall j, (1 <= p j)%R) -> (1 <= q)%R ->
  extended_order_limit (fun j => (p j)%:E) q%:E ->
  extended_order_limit
    (fun j => @convex_integral_geometric_measure R n m hMN (p j)%:E A)
    (@convex_integral_geometric_measure R n m hMN q%:E A).
Proof.
move=> hP hQ hLimit.
have [C [hC hComparison]] := @convex_integral_geometric_finite_exponent_comparison R n m hMN.
pose F (s : R) := (@projection_beta R n m hMN s%:E)%:E *
  @convex_integral_geometric_measure R n m hMN s%:E A.
pose w (j : nat) := RealExponential.exponential (C*`|p j-q|)%R.
have hW j : (0 < w j)%R := real_exponential_positive (@RealExponential.laws R) _.
have hMagnitude : extended_order_limit (fun j => `|p j-q|%R%:E) 0.
  apply: real_error_extended_order_limit=> e hE.
  have [N hN] := @extended_finite_order_limit_error R p q e hLimit hE.
  exists N=> j hJ; by rewrite subr0 normr_id; exact: hN j hJ.
have hScalar := @real_scalar_order_limit R (fun j => `|p j-q|%R) 0 C hMagnitude.
rewrite mulr0 in hScalar.
have hWLimit := @real_exponential_order_limit R (fun j => (C*`|p j-q|)%R) 0 hScalar.
rewrite (real_exponential_zero (@RealExponential.laws R)) in hWLimit.
have hLower j : F q <= (w j)%:E * F (p j).
  have h := hComparison q (p j) A hQ (hP j).
  by rewrite distrC in h.
have hUpper j : F (p j) <= (w j)%:E * F q.
  exact (hComparison (p j) q A (hP j) hQ).
have hPositive j : (0 < @projection_beta R n m hMN (p j)%:E)%R.
  exact (@projection_beta_positive R n m hMN (p j)%:E (hP j)).
have hEndPositive : (0 < @projection_beta R n m hMN q%:E)%R.
  exact (@projection_beta_positive R n m hMN q%:E hQ).
have hNonnegative j : 0 <= @convex_integral_geometric_measure R n m hMN (p j)%:E A.
  exact (@measure_nonnegative R _ (@convex_integral_geometric_measure R n m hMN (p j)%:E)
    (@convex_integral_geometric_measure_is_measure R n m hMN (p j)%:E (hP j)) A).
have hEndNonnegative : 0 <= @convex_integral_geometric_measure R n m hMN q%:E A.
  exact (@measure_nonnegative R _ (@convex_integral_geometric_measure R n m hMN q%:E)
    (@convex_integral_geometric_measure_is_measure R n m hMN q%:E hQ) A).
have hFNonnegative : 0 <= F q := mule_ge0 (lee_tofin (ltW hEndPositive)) hEndNonnegative.
have hNormalized := @positive_factor_sequence_sandwich R w (fun j => F (p j)) (F q)
  hW hFNonnegative hWLimit hLower hUpper.
have hBetaLimit := @projection_beta_admissible_sequence_limit R n m hMN p q%:E hP hLimit.
exact (@positive_normalization_sequence_limit R
  (fun j => @projection_beta R n m hMN (p j)%:E)
  (@projection_beta R n m hMN q%:E)
  (fun j => @convex_integral_geometric_measure R n m hMN (p j)%:E A)
  (@convex_integral_geometric_measure R n m hMN q%:E A)
  hPositive hEndPositive hNonnegative hEndNonnegative hBetaLimit hNormalized).
Qed.
