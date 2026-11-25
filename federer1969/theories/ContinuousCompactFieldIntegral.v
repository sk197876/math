(** Federer (1969), 4.1.2, p. 347: continuous
    compactly supported fields have actual Banach-valued
    integrals, including fields in higher differential spaces.
    Only their actual range is required to be separable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric CompleteMetricUP LinearBasis
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormClassOneUP NormContinuousSeparableRange ClosedLinearSpanUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages MeasureUP MeasureBasic MeasureAlmostBasic MeasurableNormedFunctionUP SummableRealFunctionUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureVectorIntegralUP MeasureVectorIntegralSealed
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext SmoothCompactSet
  NormClassZeroTotalMeasurable ContinuousFieldLocalIntegrability LocallyIntegrableVectorFieldUP TotalNormedLone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_euclidean_field_measurable_normed]:
    the separable-range reduction of Federer 3.1.1, p. 211,
    applies to the continuous derivative fields integrated in
    4.1.2, p. 347. No separability of their
    whole Banach target is assumed. *)
Theorem continuous_euclidean_field_measurable_normed (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R n->Y):
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY (fun _=>True) f ->
  is_measurable_normed_function (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))).
Proof.
move=>hf.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
have [S [hClosed [hRange hSep]]]:=@norm_class_zero_separable_linear_range R X Y NX NY hNX hNY
  n (@coordinate_basis R n) (@coordinate_basisP R n) setT f hf.
split.
- exact:(@norm_class_zero_total_measurable R X Y NX NY hNX hNY mu
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_open R n) f hf).
- exists S; split=>//.
  rewrite partial_function_total_preimage.
  have he:(fun x:X=>(f x:real_norm_metric_space hNY)) @^-1` [set y|~S y]=set0.
    apply/seteqP; split; last by move=>x [].
    move=>x hx; apply:hx; apply:hRange; by exists x.
  rewrite he; exact:measure_empty (euclidean_lebesgue_is_measure R n).
Qed.

(** Source for [continuous_compact_field_integral_exists]: actual
    integration of continuous compactly supported higher differential
    fields in Federer 4.1.2, p. 347. The
    original compact norm-integral bound supplies L1 membership. *)
Theorem continuous_compact_field_integral_exists (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY))
    (f:R_n R n->Y)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True)):
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY (fun _=>True) f ->
  (forall x,~smooth_compact_carrier K x ->f x=0) ->
  exists y:Y,is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) y.
Proof.
move=>hf hOff.
have hLocal:=@continuous_field_locally_norm_integrable R n Y NY hNY f hf.
have [b hb]:=@locally_integrable_vector_compact_norm R (R_n R n) Y
  (inner_norm (@euclidean_inner_productP R n)) NY
  (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
  (@euclidean_lebesgue_measure R n) f hLocal K.
have hIntegral:is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x=>NY (f x))) b%:E.
  apply:(@measure_integral_graph_equivalent R (R_n R n) _ _ _ _ _ hb)=>x z.
  rewrite !real_total_integrand_graph.
  case:(pselect (smooth_compact_carrier K x))=>hx; first reflexivity.
  by rewrite (hOff x hx) (real_seminorm_zero hNY.1).
have hLone:=@total_normed_lone_from_norm_integral R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) f b
  (@continuous_euclidean_field_measurable_normed R n Y NY hNY f hf) hIntegral.
exists (@MeasureVectorIntegral.value R (R_n R n) Y NY hNY hY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) _ hLone).
exact:MeasureVectorIntegral.laws.
Qed.
