(** Federer (1969), 3.2.46, pp. 281–282:
    an ordinary coordinate integral supported in the
    actual chart equals its chart-reference integral.
    Exact injective pushforward and 2.4.18, p. 90,
    retain signed definedness and infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartReference RiemannianReferencePushforward
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  PartialZeroExtension PartialZeroExtensionLaws MeasureUP MeasureRestriction
  MeasurePushforward MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  RestrictedIntegralIdentity InjectivePushforwardIntegral TopologicalBorel
  BorelRegularMeasureUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_supported_reference_integral]:
    exact coordinate integration of an original function
    vanishing outside the chart, supporting 3.2.46,
    p. 282, through 2.4.18, p. 90.
    No global inverse chart point, finite mass or
    absolute integrability is assumed; empty charts remain. *)
Theorem riemannian_supported_reference_integral (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (u : R_n R n -> extended_real_line R) a :
  (forall z, ~A z -> u z=0) ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (partial_function_total u) a ->
  is_measure_integral (@riemannian_chart_reference R n A g hg)
    (partial_function_total (fun x : riemannian_metric_space hg=>u (val x))) a.
Proof.
move=> hSupport hIntegral.
pose E := [the choiceType of inner_metric_space (@euclidean_inner_productP R n)].
pose X := [the choiceType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R n A g hg.
have hPhi := @riemannian_chart_reference_is_measure R n A g hg.
have hA : measure_measurable (@euclidean_lebesgue_measure R n) A.
  exact:(@borel_regular_borel_measurable R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_borel_regular R n) A (open_borel_set (riemannian_chart_domain_open hg))).
have hCut : is_measure_subset_integral (@euclidean_lebesgue_measure R n) A
    (partial_function_total u) a.
  apply:(measure_integral_graph_equivalent _ hIntegral)=> z r.
  case:(pselect (A z))=> hz.
  - rewrite (partial_function_zero_extension_on _ _ _ hz); by [].
  - rewrite (partial_function_zero_extension_off _ _ _ hz).
    change (u z=r <-> r=0); rewrite (hSupport z hz).
    split; exact:esym.

have hRestricted := (@restricted_integral_zero_extension_iff R E (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) A (partial_function_total u) a hA).2 hCut.
have hPush : is_measure_integral (measure_pushforward (fun x : X=>val x) phi)
    (partial_function_total u) a by rewrite riemannian_reference_pushforward.
have hPre := (@injective_pushforward_integral_iff R X E phi hPhi (fun x=>val x)
  (partial_function_total u) (fun x y hEq=>val_inj hEq) a).2 hPush.
apply:(measure_integral_graph_equivalent _ hPre)=> x r; by [].
Qed.
