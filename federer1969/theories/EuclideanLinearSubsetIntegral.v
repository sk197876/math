(** Federer (1969), 2.4.18, p. 90, and
    2.7.16, pp. 134–135: genuine subset integrals
    transform under invertible linear coordinates by the
    determinant. This supports 3.2.46, p. 282,
    retaining the original measurable set and partial graph. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLinearMeasureTransport
  PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasureRestriction
  MeasurePushforward MeasureScaleIntegral MeasureIntegralUP MeasureSubsetIntegral
  RestrictedIntegralIdentity InjectivePushforwardIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_linear_subset_integral_iff]:
    the actual coordinate substitution of 2.4.18, p. 90,
    with the determinant law of 2.7.16, pp. 134–135,
    used in the frozen coarea reduction of 3.2.46,
    p. 282. Both definedness directions and signed
    infinite values are preserved; no finiteness premise
    is imposed on the original set or integral. *)
Theorem euclidean_linear_subset_integral_iff (R : realType) n
    (L : {linear R_n R n -> R_n R n})
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (w : partial_function (R_n R n) (extended_real_line R)) a :
  injective L -> measure_measurable (@euclidean_lebesgue_measure R n) S ->
  (is_measure_subset_integral (@euclidean_lebesgue_measure R n) S
      (partial_function_precompose L w) a <->
    is_measure_subset_integral (@euclidean_lebesgue_measure R n) (L @` S) w
      (`|euclidean_det L|%:E*a)%E).
Proof.
move=> hInj hS.
pose E := [the choiceType of inner_metric_space (@euclidean_inner_productP R n)].
pose Leb := @euclidean_lebesgue_measure R n.
pose d := `|euclidean_det L|.
have hLeb := euclidean_lebesgue_is_measure R n.
have hd : 0<d by rewrite /d normr_gt0; exact:(euclidean_det_injective L).2 hInj.
have hdi : 0<d^-1 by rewrite invr_gt0.
have hdNe := lt0r_neq0 hd.
have hImage := euclidean_linear_image_measurable hInj hS.
have hPush := @euclidean_linear_restricted_pushforward R n L S hInj.
have hTransport := @injective_pushforward_integral_iff R E E
  (measure_restrict Leb S) (measure_restrict_is_measure hLeb S) L w hInj.
have hSource := @restricted_integral_zero_extension_iff R E Leb hLeb S
  (partial_function_precompose L w) a hS.
have hCancel : measure_scale d (measure_scale d^-1 (measure_restrict Leb (L @` S)))=
    measure_restrict Leb (L @` S).
  apply:funext=> T; by rewrite /measure_scale muleA -EFinM mulfV // mul1e.
split.
- move=> hIntegral.
  have hPushIntegral := (hTransport a).1 (hSource.2 hIntegral).
  rewrite hPush in hPushIntegral.
  have hScaled := @measure_scale_integral R E
    (measure_scale d^-1 (measure_restrict Leb (L @` S)))
    (measure_scale_is_measure (measure_restrict_is_measure hLeb (L @` S)) hdi)
    d hd w a hPushIntegral.
  rewrite hCancel in hScaled.
  exact:(@restricted_integral_zero_extension_iff R E Leb hLeb (L @` S) w
    (d%:E*a)%E hImage).1 hScaled.
- move=> hIntegral.
  have hRestricted := (@restricted_integral_zero_extension_iff R E Leb hLeb (L @` S)
    w (d%:E*a)%E hImage).2 hIntegral.
  have hScaled := @measure_scale_integral R E (measure_restrict Leb (L @` S))
    (measure_restrict_is_measure hLeb (L @` S)) d^-1 hdi w (d%:E*a)%E hRestricted.
  rewrite muleA -EFinM mulVf // mul1e in hScaled.
  have hPushIntegral : is_measure_integral (measure_pushforward L (measure_restrict Leb S)) w a.
    by rewrite hPush.
  exact:hSource.1 ((hTransport a).2 hPushIntegral).
Qed.
