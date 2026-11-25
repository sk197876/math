(** Federer (1969), 4.1.2, p. 347: locally bounded measurable
    input fields satisfy the original local norm
    integrability requirement. The proof reuses compact
    boundedness, Lebesgue finiteness on compact sets
    and the earlier scalar summability theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClassOneUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet NormCompactFunctionBound TopologicalBorel CharacteristicFunctionUP CharacteristicFunctionSealed
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension ExtendedRealOrderTopology
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableZeroExtension MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP BoundedSubsetSummability
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext NormClassZeroTotalMeasurable
  TotalVectorNormIntegrability LocallyIntegrableVectorFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [locally_bounded_measurable_field_locally_integrable]:
    the local norm integrability of the actual derivative field
    used in Federer 4.1.2, p. 347. Its original measurability
    and proved compact bounds imply every required finite integral. *)
Theorem locally_bounded_measurable_field_locally_integrable (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R n->Y):
  is_measure_measurable_function (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) ->
  (forall K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True),
    exists M:R,0<=M /\forall x,smooth_compact_carrier K x ->NY (f x)<=M) ->
  @is_locally_integrable_vector_field R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
    (@euclidean_lebesgue_measure R n) f.
Proof.
move=>hMeas hCompactBound.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
constructor; first exact hMeas.
move=>K.
have hCompact:=smooth_compact_is_compact K.
have hKMeas:measure_measurable mu (smooth_compact_carrier K).
  apply:(@euclidean_distribution_measure_borel R n).
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hN)) hCompact)).
have hKFinite:=@euclidean_distribution_measure_compact_finite R n (smooth_compact_carrier K) hCompact.
have [M [hM hBound]]:=hCompactBound K.
pose chi:=@CharacteristicFunction.value R X (smooth_compact_carrier K).
have hChi:=@CharacteristicFunction.laws R X (smooth_compact_carrier K).
pose F:=partial_function_zero_extension (0:extended_real_line R) (smooth_compact_carrier K)
  (real_total_integrand (fun x=>NY (f x))).
have hFMeas:=@measurable_zero_extension R X (extended_real_line R) mu hm 0
  (smooth_compact_carrier K) _ hKMeas
  (@total_vector_norm_integrand_measurable R X Y NY hNY mu hm f hMeas).
have hFBound:measure_almost_everywhere mu [set x|exists z:R,
    partial_function_graph F x z%:E /\ `|z|<=M*chi x].
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ (measure_almost_everywhere_true hm))=>x _.
  case:(pselect (smooth_compact_carrier K x))=>hx.
  - exists (NY (f x)); split.
    + apply:(partial_function_zero_extension_on _ _ _ hx).2.
      by apply/real_total_integrand_graph.
    + rewrite /chi (ger0_norm (real_seminorm_nonnegative hNY.1 (f x)))
        (characteristic_on_set hChi hx) mulr1; exact:hBound x hx.
  - exists 0; split.
    + apply:(partial_function_zero_extension_off _ _ _ hx).2; reflexivity.
    + by rewrite /chi normr0 (characteristic_off_set hChi hx) mulr0.
have [b hb]:=@bounded_supported_partial_summable R X mu F (smooth_compact_carrier K) chi M
  hm hKMeas hKFinite hChi hM hFMeas hFBound.
exists b.
apply:(measure_integral_graph_equivalent _ hb)=>x z.
rewrite /F real_total_integrand_graph.
case:(pselect (smooth_compact_carrier K x))=>hx.
- by rewrite (partial_function_zero_extension_on _ _ _ hx) real_total_integrand_graph.
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  change (z=(0:extended_real_line R)<->(0:extended_real_line R)=z); split=>->; reflexivity.
Qed.
