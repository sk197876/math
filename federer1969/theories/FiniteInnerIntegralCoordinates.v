(** Federer (1969), 3.2.48, p. 284: signed integrals in
    actual finite inner spaces pass to orthonormal coordinates by
    2.4.18 and 2.10.11. Only public chart and measure laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerMetric
  FiniteInnerChartUP FiniteInnerChartMeasureTransport FiniteInnerChartMeasuredImages
  HausdorffMeasure MeasureUP MeasureRestriction MeasurePushforward
  InjectiveRestrictionPushforward InjectivePushforwardIntegral PartialFunctionUP
  PartialFunctionPrecomposition MeasureIntegralUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_chart_restricted_integral_coordinates]:
    coordinate change in the coarea application of 3.2.48, p. 284.
    The original restricted source is retained. Neither a Borel-set
    hypothesis nor a separate composition-measurability premise is needed. *)
Theorem finite_inner_chart_restricted_integral_coordinates (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N)) q (S:set V)
    (f:partial_function V (extended_real_line R)) a:
  is_finite_inner_chart B e p ->
  (is_measure_integral (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R N)) q) (p @` S))
      (partial_function_precompose e f) a <->
   is_measure_integral (measure_restrict (@hausdorff_measure R (inner_metric_space hB) q) S) f a).
Proof.
move=>hChart.
have he:injective e.
  move=>x y h; have h0:=congr1 p h.
  by rewrite !(finite_inner_chart_left_inverse hChart) in h0.
have hImage:e @` (p @` S)=S.
  apply/seteqP; split=>x.
  - move=>[z [y hy <-] <-]; by rewrite (finite_inner_chart_right_inverse hChart).
  - move=>hx; exists (p x); first by exists x.
    exact (finite_inner_chart_right_inverse hChart x).
have hPush:=@injective_restriction_pushforward R
  (inner_metric_space (@euclidean_inner_productP R N)) (inner_metric_space hB)
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R N)) q)
  e (p @` S) he.
rewrite (@finite_inner_chart_direct_hausdorff_pushforward R V B hB N e p q hChart) hImage in hPush.
have hIff:=@injective_pushforward_integral_iff R
  (inner_metric_space (@euclidean_inner_productP R N)) (inner_metric_space hB)
  (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R N)) q) (p @` S))
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) q) (p @` S)) e f he a.
by rewrite hPush in hIff.
Qed.

(** Source for [finite_inner_chart_integral_coordinates]: the full
    ambient signed-coordinate change used for whole fibres in 3.2.48,
    p. 284. This also applies to a zero extension from an arbitrary
    fibre, without presupposing that the fibre is measurable. *)
Theorem finite_inner_chart_integral_coordinates (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N)) q
    (f:partial_function V (extended_real_line R)) a:
  is_finite_inner_chart B e p ->
  (is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R N)) q)
      (partial_function_precompose e f) a <->
   is_measure_integral (@hausdorff_measure R (inner_metric_space hB) q) f a).
Proof.
move=>hChart.
have he:injective e.
  move=>x y h; have h0:=congr1 p h.
  by rewrite !(finite_inner_chart_left_inverse hChart) in h0.
have hIff:=@injective_pushforward_integral_iff R
  (inner_metric_space (@euclidean_inner_productP R N)) (inner_metric_space hB)
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R N)) q)
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R N)) q) e f he a.
by rewrite (@finite_inner_chart_direct_hausdorff_pushforward R V B hB N e p q hChart) in hIff.
Qed.
