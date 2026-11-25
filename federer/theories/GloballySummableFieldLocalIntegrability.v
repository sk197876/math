(** Federer (1969), 4.1.18, p. 375: an
    original globally summable field satisfies the
    local input condition for 4.1.2 convolution.
    Restrict the existing finite norm integral to
    each original compact set. No continuity or
    finite whole source measure is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext IsotropyGroupTopology TopologicalBorel
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialZeroExtensionLaws
  MeasurableFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP SummableSubsetRestriction LocallyIntegrableVectorFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [globally_summable_field_locally_integrable]:
    the Omega input in the first proposition of
    Federer 4.1.18, p. 375, meets the original
    local norm-integrability hypothesis of 4.1.2,
    p. 347, including dimension zero. *)
Theorem globally_summable_field_locally_integrable (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f:R_n R n->Y) b:
  is_measure_measurable_function (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x=>NY (f x))) b%:E ->
  @is_locally_integrable_vector_field R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
    (@euclidean_lebesgue_measure R n) f.
Proof.
move=>hMeas hIntegral;constructor;first exact:hMeas.
move=>K.
pose X:=R_n R n.
pose XT:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
have hK:measure_measurable mu (smooth_compact_carrier K).
  apply:euclidean_distribution_measure_borel.
  exact:closed_borel_set (compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K)).
have hSummable:is_measure_summable mu (real_total_integrand (fun x=>NY (f x))).
  by exists b.
have[a hA]:=@summable_measurable_zero_extension R X mu hm (smooth_compact_carrier K)
  _ hK hSummable.
exists a;apply:(@measure_integral_graph_equivalent R X mu _ _ a%:E _ hA)=>x y.
rewrite real_total_integrand_graph.
case:pselect=>hx.
- by rewrite (partial_function_zero_extension_on _ _ _ hx) real_total_integrand_graph.
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  change (y=0%E<->0%E=y);by split=>->.
Qed.
