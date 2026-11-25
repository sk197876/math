(** Uniform finite-exponent comparison of the original Q_t,
    supporting Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricMeasure
  IntegralGeometricExponentMonotone ProjectionBeta MeasureUP ReciprocalExponent
  ConvexIntegralGeometricReciprocalBound RealExponentialUP RealExponentialSealed RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_finite_exponent_comparison]:
    a symmetric, weaker consequence of the corrected secant
    step in Federer 3.2.45, p. 279. One C>=0 works
    for every pair of finite admissible exponents and every
    original target set: beta_p Q_p <= exp(C|p-q|) beta_q Q_q.
    This supplies the uniform factor tending to one at each
    finite exponent. Infinite masses and the endpoint p=1 remain. *)
Theorem convex_integral_geometric_finite_exponent_comparison (R : realType) n m
    (hMN : (m <= n)%N) : exists C : R, (0 <= C)%R /\
  forall (p q : R) (A : set (inner_metric_space (@euclidean_inner_productP R n))),
    (1 <= p)%R -> (1 <= q)%R ->
    (@projection_beta R n m hMN p%:E)%:E *
      @convex_integral_geometric_measure R n m hMN p%:E A <=
    (@RealExponential.exponential R (C * `|p-q|)%R)%:E *
      ((@projection_beta R n m hMN q%:E)%:E *
        @convex_integral_geometric_measure R n m hMN q%:E A).
Proof.
have [C [hC hComparison]] := @convex_integral_geometric_reciprocal_bound R n m hMN.
exists C; split=> // p q A hP hQ.
pose F (s : R) := (@projection_beta R n m hMN s%:E)%:E *
  @convex_integral_geometric_measure R n m hMN s%:E A.
have hOrdered (s t : R) (hS : (1 <= s)%R) (hT : (1 <= t)%R) (hST : (s <= t)%R) :
    F t <= (RealExponential.exponential (C*(t-s))%R)%:E * F s.
  case: (eqVneq s t)=> [hEqual|hNe].
  - by rewrite hEqual subrr mulr0 (real_exponential_zero (@RealExponential.laws R)) mul1e.
  have hStrict : (s < t)%R by rewrite lt_neqAle hNe hST.
  have hSPositive : (0 < s)%R := lt_le_trans ltr01 hS.
  have hTPositive : (0 < t)%R := lt_le_trans ltr01 hT.
  have hSInversePositive : (0 < s^-1)%R by rewrite invr_gt0.
  have hTInversePositive : (0 < t^-1)%R by rewrite invr_gt0.
  have hInverse : (t^-1 < s^-1)%R by rewrite (@ltf_pV2 R t s hTPositive hSPositive).
  have hInverseOne : (s^-1 <= 1)%R by rewrite invf_le1.
  have h := hComparison (t^-1)%R (s^-1)%R A (ltW hTInversePositive) hInverse hInverseOne.
  rewrite /reciprocal_lebesgue_exponent (gt_eqF hTInversePositive)
    (gt_eqF hSInversePositive) !invrK in h.
  have hRatioIdentity : (C*(s^-1-t^-1)/s^-1 = C*((t-s)/t))%R.
    field; by rewrite (lt0r_neq0 hSPositive) (lt0r_neq0 hTPositive).
  have hDifference : (0 <= t-s)%R by rewrite subr_ge0.
  have hRatio : ((t-s)/t <= t-s)%R.
    rewrite ler_pdivrMr //.
    have hMul := ler_wpM2l hDifference hT.
    by rewrite mulr1 in hMul.
  have hExponent : (C*(s^-1-t^-1)/s^-1 <= C*(t-s))%R.
    rewrite hRatioIdentity.
    have hScaled := ler_wpM2l hC hRatio.
    exact hScaled.
  have hWeight : (RealExponential.exponential (C*(s^-1-t^-1)/s^-1)%R <=
      RealExponential.exponential (C*(t-s))%R)%R by rewrite real_exponential_order.
  have hFNonnegative : 0 <= F s.
    apply: mule_ge0.
    - rewrite lee_fin; exact: ltW (@projection_beta_positive R n m hMN s%:E hS).
    - exact: (@measure_nonnegative R _ _
        (@convex_integral_geometric_measure_is_measure R n m hMN s%:E hS) A).
  have hScaled := lee_wpmul2r hFNonnegative (lee_tofin hWeight).
  rewrite invrK in hScaled.
  exact (le_trans h hScaled).
case: (leP p q)=> [hPQ|hQP].
- have hMono := @convex_integral_geometric_normalized_measure_monotone R n m hMN p%:E q%:E A hP hPQ.
  have hFNonnegative : 0 <= F q.
    apply: mule_ge0.
    - rewrite lee_fin; exact: ltW (@projection_beta_positive R n m hMN q%:E hQ).
    - exact: (@measure_nonnegative R _ _
        (@convex_integral_geometric_measure_is_measure R n m hMN q%:E hQ) A).
  have hExponent : (0 <= C*`|p-q|)%R := mulr_ge0 hC (normr_ge0 _).
  have hWeight : (1 <= RealExponential.exponential (C*`|p-q|)%R)%R.
    by rewrite -(real_exponential_zero (@RealExponential.laws R)) real_exponential_order.
  have hScaled := lee_wpmul2r hFNonnegative (lee_tofin hWeight).
  rewrite mul1e in hScaled.
  exact: le_trans hMono hScaled.
- have hDifference : (0 <= p-q)%R by rewrite subr_ge0; exact: ltW hQP.
  rewrite (ger0_norm hDifference).
  exact: hOrdered q p hQ hP (ltW hQP).
Qed.
