(** Corrected infinity-endpoint argument for Federer (1969),
    3.2.45, p. 279. All actual Q_t measures and
    arbitrary target sets retain their original scope. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricMeasure
  IntegralGeometricExponentMonotone ProjectionBeta MeasureUP
  ConvexIntegralGeometricUniformInfinityLower UniformRootInfinitySupremum
  MonotoneInfinitySequenceLimit ExtendedRealBounds ExtendedRealOrderLimit
  ProjectionBetaSequenceLimit PositiveNormalizationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_normalized_infinity_cofinal]:
    expanded replacement for the missing uniform infinity step
    in Federer 3.2.45, p. 279. The original normalized
    finite-exponent measures exceed every strict lower bound
    on the original Q_infinity of every target set. *)
Theorem convex_integral_geometric_normalized_infinity_cofinal (R : realType) n m
    (hMN : (m <= n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  forall c, c < @convex_integral_geometric_measure R n m hMN +oo A ->
    exists j : nat, c < (@projection_beta R n m hMN ((j.+1)%:R)%:E)%:E *
      @convex_integral_geometric_measure R n m hMN ((j.+1)%:R)%:E A.
Proof.
pose F := fun t => (@projection_beta R n m hMN t)%:E *
  @convex_integral_geometric_measure R n m hMN t A.
have hOne j : (1 <= (j.+1)%:R :> R)%R by rewrite ler1n.
have hValue : F +oo = @convex_integral_geometric_measure R n m hMN +oo A.
  by rewrite /F projection_beta_infinity mul1e.
have hNonnegative t (hT : 1 <= t) : 0 <= F t.
  apply: mule_ge0.
  - rewrite lee_fin; exact: ltW (@projection_beta_positive R n m hMN t hT).
  - exact: (@measure_nonnegative R _ _
      (@convex_integral_geometric_measure_is_measure R n m hMN t hT) A).
have hUpper j : F ((j.+1)%:R)%:E <= @convex_integral_geometric_measure R n m hMN +oo A.
  have hJ : 1 <= ((j.+1)%:R : R)%:E by rewrite lee_fin; exact: hOne.
  have h := @convex_integral_geometric_normalized_measure_monotone R n m hMN
    ((j.+1)%:R)%:E +oo A hJ (leey _).
  rewrite projection_beta_infinity mul1e in h; exact h.
have hLower r (hR : (0 < r)%R) (hR1 : (r < 1)%R) : exists a : R, (0 < a)%R /\
    forall j, ((r * RealPower.real_power a ((j.+1)%:R)^-1)%R)%:E *
      @convex_integral_geometric_measure R n m hMN +oo A <= F ((j.+1)%:R)%:E.
  have [a [hA hBound]] := @convex_integral_geometric_uniform_infinity_lower R n m hMN r hR hR1.
  exists a; split=> // j; exact: hBound _ A (hOne j).
apply: (@uniform_root_lower_cofinal R (fun j => F ((j.+1)%:R)%:E)
  (@convex_integral_geometric_measure R n m hMN +oo A))=> //.
- exact: (@measure_nonnegative R _ _
    (@convex_integral_geometric_measure_is_measure R n m hMN +oo (leey 1)) A).
- move=> j.
  have hJ : 1 <= ((j.+1)%:R : R)%:E by rewrite lee_fin; exact: hOne.
  exact (hNonnegative ((j.+1)%:R)%:E hJ).
Qed.

(** Source for [convex_integral_geometric_infinity_sequence_limit]:
    the infinity endpoint of the continuity assertion in
    Federer 3.2.45, p. 279, using the proved uniform
    generator estimate. Every real exponent sequence p_j>=1
    tending to infinity has Q_p_j(A) tending to Q_infinity(A).
    No boundedness, measurability, finite mass or monotonicity
    premise is imposed on A or on the exponent sequence. *)
Theorem convex_integral_geometric_infinity_sequence_limit (R : realType) n m
    (hMN : (m <= n)%N) (p : nat -> R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (forall j, (1 <= p j)%R) ->
  extended_order_limit (fun j => (p j)%:E) +oo ->
  extended_order_limit
    (fun j => @convex_integral_geometric_measure R n m hMN (p j)%:E A)
    (@convex_integral_geometric_measure R n m hMN +oo A).
Proof.
move=> hP hLimit.
pose F := fun t => (@projection_beta R n m hMN t)%:E *
  @convex_integral_geometric_measure R n m hMN t A.
have hFValue : F +oo = @convex_integral_geometric_measure R n m hMN +oo A.
  by rewrite /F projection_beta_infinity mul1e.
have hCofinal c : c < F +oo -> exists r : R, (1 <= r)%R /\ c < F r%:E.
  rewrite hFValue=> hC.
  have [j hJ] := @convex_integral_geometric_normalized_infinity_cofinal R n m hMN A c hC.
  exists (j.+1)%:R; split=> //; by rewrite ler1n.
have hNormalized := @monotone_infinity_sequence_limit R F (fun j => (p j)%:E)
  (fun s t => @convex_integral_geometric_normalized_measure_monotone R n m hMN s t A)
  hCofinal (fun j => hP j) hLimit.
have hPositive j : (0 < @projection_beta R n m hMN (p j)%:E)%R.
  exact (@projection_beta_positive R n m hMN (p j)%:E (hP j)).
have hEndPositive : (0 < @projection_beta R n m hMN +oo)%R.
  exact (@projection_beta_positive R n m hMN +oo (leey 1)).
have hNonnegative j : 0 <= @convex_integral_geometric_measure R n m hMN (p j)%:E A.
  exact (@measure_nonnegative R _ (@convex_integral_geometric_measure R n m hMN (p j)%:E)
    (@convex_integral_geometric_measure_is_measure R n m hMN (p j)%:E (hP j)) A).
have hEndNonnegative : 0 <= @convex_integral_geometric_measure R n m hMN +oo A.
  exact (@measure_nonnegative R _ (@convex_integral_geometric_measure R n m hMN +oo)
    (@convex_integral_geometric_measure_is_measure R n m hMN +oo (leey 1)) A).
have hBetaLimit := @projection_beta_left_sequence_limit R n m hMN p +oo
  (fun j => conj (hP j) (leey _)) hLimit.
exact (@positive_normalization_sequence_limit R
  (fun j => @projection_beta R n m hMN (p j)%:E)
  (@projection_beta R n m hMN +oo)
  (fun j => @convex_integral_geometric_measure R n m hMN (p j)%:E A)
  (@convex_integral_geometric_measure R n m hMN +oo A)
  hPositive hEndPositive hNonnegative hEndNonnegative hBetaLimit hNormalized).
Qed.
