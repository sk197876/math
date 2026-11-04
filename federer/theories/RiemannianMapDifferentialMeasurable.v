(** Federer (1969), 3.2.46, p. 282: local
    coordinates measure the actual original partial differential.
    The Borel graph assertion of 3.1.1, p. 211,
    and Rademacher supply its measurability and conull domain;
    no globally chosen derivative field is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness NormMetric NormDifferentialUP NormDifferential EuclideanHomOperator
  RiemannianTensorUP RiemannianMetricCarrier RiemannianPathLipschitz
  RiemannianMapDifferential RiemannianMapDifferentialLocal RiemannianChartReference
  RiemannianReferenceFunction EuclideanWholeDifferentialMeasurable
  PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasurableFunctionUP
  MeasureLocalFunctionMeasurability MeasureRestrictedGraphAgreement
  TopologicalBorel ContinuousBorelPreimages LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_differential_measurable]:
    measurability of the original Hom-valued partial Df,
    supporting 3.2.46, p. 282. Path-Lipschitz continuity
    proves the local Euclidean representatives and Rademacher
    domain; no coordinate or differential field is a premise. *)
Theorem riemannian_map_differential_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f ->
  @is_measure_measurable_function R _
    [the topologicalType of real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)]
    (@riemannian_chart_reference R m A g hg) (riemannian_map_differential f).
Proof.
move=> hLip.
pose X := [the topologicalType of riemannian_metric_space hg].
pose E := [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)].
pose T := [the topologicalType of real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)].
pose phi := @riemannian_chart_reference R m A g hg.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have [C hBase] := @riemannian_chart_countable_open_base R m A g hg.
apply: (@measure_local_function_measurability R X T phi C
  (riemannian_map_differential f) hPhi hBase).
- move=> V hV; exact:riemannian_chart_reference_borel_measurable (open_borel_set hV).
- move=> a.
  have [U [K [F [hU [hUa [hUA [hK [hBound [hRange hAgree]]]]]]]]] :=
    @riemannian_path_map_local_coordinates R m n A B g h hg hh f hLip a.
  pose V : set X := (fun x : X=>(val x : E)) @^-1` U.
  have hV : open V := @open_comp X E (fun x=>val x) U
    (fun x _=>@riemannian_chart_inclusion_continuous R m A g hg x) hU.
  exists V; split; first exact hV; split; first exact hUa.
  have hFLip : is_metric_lipschitz setT F by exists K; split.
  pose DF := norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT F.
  have hDMeas := @riemannian_reference_function_precompose R m A g hg T DF
    (@euclidean_whole_differential_measurable R m n F hFLip).
  apply: (@restricted_graph_agreement_measurable R X T phi V
    (partial_function_precompose (fun x : X=>val x) DF)
    (riemannian_map_differential f) hPhi hDMeas).
  move=> x hx D.
  change (partial_function_graph DF (val x) D <->
    partial_function_graph (riemannian_map_differential f) x D).
  rewrite /DF (norm_differential_graph _ _ setT F (val x) D).
  exact:iff_sym (@riemannian_map_differential_local_coordinates R m n A B g h
    hg hh f U F hU hUA hAgree x hx D).
Qed.
