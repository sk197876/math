(** Federer (1969), 3.3.20, p. 306:
    actual positive real-degree product mass, retaining
    every original set and the explicit covering coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanRealPlane EuclideanCantorProduct PowerCantorPairUP PowerCantorProductMeasure
  PowerCantorSquareDiameterBound MetricRealPowerCost MetricRealPowerMeasure
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleMeasureBound CaratheodoryLimitUP HausdorffLengthUP FiniteMeasureScaling
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_square_power_measure_lower]:
    the lower bound in 3.3.20, p. 306, before
    inserting the actual Euler Gamma normalization b.
    The original unit product restriction has mass one.
    Its proved diameter bound supplies the comparison
    for every actual generator at cutoff one, including
    diameter zero. No source measurability is added. *)
Theorem power_cantor_square_power_measure_lower (R:realType) (m b:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  (0<m)%R ->(m<1)%R ->(0<b)%R ->is_power_cantor_pair 1 m n A f ->
  b%:E<=@metric_real_power_measure R
    (inner_metric_space (@euclidean_inner_productP R 2)) b (2* m)%R
      (euclidean_cantor_product A A).
Proof.
move=>hm hm1 hb hPair.
pose E:=inner_metric_space (@euclidean_inner_productP R 2).
pose nu:=@power_cantor_product_measure R [the metricType R of E]
  (@euclidean_real_plane_pair R) 1 m ler01 A A.
have hNu:is_measure nu:=@power_cantor_product_is_measure R E (@euclidean_real_plane_pair R) 1 m ler01 A A.
pose mu:=fun S:set E=>b%:E*nu S.
have hMu:is_measure mu:=finite_scale_is_measure hNu (ltW hb).
have hMass:mu (euclidean_cantor_product A A)=b%:E.
  have h:=@power_cantor_product_cantor_mass R E (@euclidean_real_plane_pair R)
    (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) 1 m ler01 n n A A f f
    ltr01 hm hm1 hPair hPair.
  by rewrite /mu /nu h mul1r mule1.
pose xi:=@metric_scale_envelope R [the metricType R of E] (@nonempty_metric_sets R E)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b (2* m)%R (val S)) 1.
have hXi:=@metric_scale_envelope_specification R [the metricType R of E] (@nonempty_metric_sets R E)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b (2* m)%R (val S)) 1.
have hGenerator (S:nonempty_metric_sets E):extended_metric_diameter (val S)<=1 ->
    mu (val S)<=metric_real_diameter_cost b (2* m)%R (val S).
  move=>hDiameter.
  have hNonnegative:=metric_diameter_nonnegative (extended_metric_diameter_specification (val S)).
  case hD:(extended_metric_diameter (val S)) hNonnegative hDiameter=>[d| |] hd hd1;last 2 first.
  - by rewrite leye_eq in hd1.
  - by [].
  have hd0:(0<=d)%R by move:hd;rewrite lee_fin.
  case:(eqVneq d (0:R)%R)=>hZero.
  - have hNull:=@power_cantor_product_zero_diameter R E (@euclidean_real_plane_pair R)
      (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
      (@euclidean_real_plane_is_metric_product R) 1 m ler01 n n A A f f
      ltr01 hm hm1 hPair hPair (val S).
    have hDZero:extended_metric_diameter (val S)=0 by rewrite hD hZero.
    rewrite /mu /nu (hNull hDZero) mule0.
    exact:metric_real_power_cost_nonnegative _ _ (ltW hb).
  - have hdPositive:(0<d)%R by rewrite lt_neqAle eq_sym hZero hd0.
    have hBound:=@power_cantor_square_finite_diameter_bound R m n A f (val S) d
      hm hm1 hPair hdPositive (ltac:(by rewrite hD)).
    have hScaled:=lee_wpmul2l (lee_tofin (ltW hb)) hBound.
    by rewrite /metric_real_diameter_cost hD metric_real_power_cost_finite EFinM.
have hBound:=@measure_bounded_by_metric_scale_envelope R E (@nonempty_metric_sets R E)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b (2* m)%R (val S)) 1 xi mu hXi hMu hGenerator
  (euclidean_cantor_product A A).
rewrite hMass in hBound.
apply:le_trans hBound _.
exact:(@caratheodory_limit_upper R E (@nonempty_metric_sets R E)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b (2* m)%R (val S)) _
  (@metric_real_power_measure_specification R E b (2* m)%R)
  (euclidean_cantor_product A A) 1 xi (ltac:(by [])) hXi).
Qed.
