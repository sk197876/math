(** Federer (1969), 3.3.20, p. 306:
    exact printed lower and upper real-degree mass bounds
    for the unchanged original Cantor square. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanCantorProduct PowerCantorPairUP PowerCantorCarrierCoefficient
  PowerCantorSquareMassLower PowerCantorSelfProduct RealHausdorffMeasure
  RealHausdorffNormalisation RealPower RealPowerSuccessor EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [twice_degree_upper_normalisation]: the
    upper coefficient alpha(2m)2^(-m) in
    3.3.20, p. 306, is exactly the actual
    coefficient alpha(2m)2^(-2m) times 2^m.
    Actual sealed Euler Gamma and real powers remain;
    no alternate dimensional normalization is substituted. *)
Lemma twice_degree_upper_normalisation (R:realType) (m:R) (hDegree:(0<=2* m)%R):
  real_hausdorff_normalisation hDegree*real_power 2 m=
  (real_power (euler_gamma_half R) (2* m)/
    euler_gamma (real_dimension_gamma_parameter hDegree))/real_power 2 m.
Proof.
have h2:(0<2:>R)%R by rewrite ltr0n.
have hPower:real_power (2:R) (2* m)=real_power 2 m*real_power 2 m.
  have hTwice:(2* m=m+m)%R by ring.
  by rewrite hTwice real_power_add_exponents_positive.
have hNonzero:real_power (2:R) m!=0 by rewrite gt_eqF //;exact:real_power_strictly_positive.
have hGammaP:=@euler_gamma_positive R _ (real_dimension_gamma_parameter hDegree).
have hGammaN:euler_gamma (real_dimension_gamma_parameter hDegree)!=0 by rewrite (gt_eqF hGammaP).
rewrite /real_hausdorff_normalisation hPower.
field;by rewrite !hNonzero !hGammaN.
Qed.

(** Source for [power_cantor_square_real_mass_bounds]:
    both exact bounds in 3.3.20, p. 306,
    with the actual positive Euler Gamma coefficient
    b=alpha(2m)2^(-2m). The upper value b*2^m
    is proved equal to alpha(2m)2^(-m) above.
    Every original Cantor schedule and positive initial
    coefficient remain; the original carrier is preserved.
    The degree-domain proof follows from m>0. *)
Theorem power_cantor_square_real_mass_bounds (R:realType) (c m:R)
    (hDegree:(0<=2* m)%R) (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->(0<m)%R ->(m<1)%R ->is_power_cantor_pair c m n A f ->
  let b:=real_hausdorff_normalisation hDegree in
  (b%:E<=@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2))
    (2* m)%R hDegree (euclidean_cantor_product A A))%E /\
  (@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2))
    (2* m)%R hDegree (euclidean_cantor_product A A)<=(b*real_power 2 m)%R%:E)%E.
Proof.
move=>hc hm hm1 hPair b.
have [g hUnit]:=@power_cantor_carrier_coefficient_change R c 1 m n A f hc ltr01 hm hm1 hPair.
have hb:(0<b)%R:=real_hausdorff_normalisation_positive hDegree.
split.
- exact:(@power_cantor_square_power_measure_lower R m b n A g hm hm1 hb hUnit).
- exact:(@power_cantor_self_product_bound R c m b n A f hc hm hm1 (ltW hb) hPair).
Qed.
