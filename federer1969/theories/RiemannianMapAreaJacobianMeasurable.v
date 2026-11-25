(** Federer (1969), 3.2.46, p. 282: measurability
    of the actual original-map area Jacobian follows from
    proved local coordinate extensions, the actual differential
    graph and the positive continuous source volume density.
    No global coordinate bound or selected derivative field
    is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground RiemannianTensorUP RiemannianMetricCarrier
  RiemannianMapJacobian RiemannianMapJacobianLocal RiemannianPathLipschitz
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianReferenceFunction
  RiemannianTargetJacobian RiemannianAreaJacobianMeasurable
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionPrecomposition
  PartialFunctionPostcomposition PartialFunctionPair PartialDensityProduct
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureLocalFunctionMeasurability MeasureRestrictedGraphAgreement
  MeasurableFunctionUP MeasurableGraphEquivalence MeasurablePostcomposition
  MeasurableRealArithmetic MeasurableRealEmbedding RealReciprocalBorel
  TopologicalBorel ContinuousBorelPreimages LipschitzUP
  MeasureStepIntegralIdentification ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_coordinate_area_jacobian_measurable]:
    the actual Euclidean-source, Riemannian-target area
    Jacobian of the original map is measurable for chart
    reference volume, supporting 3.2.46, p. 282.
    Original path-distance Lipschitz continuity supplies all
    local coordinate representatives and their bounds. *)
Theorem riemannian_map_coordinate_area_jacobian_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f ->
  @is_measure_measurable_function R [the choiceType of riemannian_metric_space hg]
    [the topologicalType of real_line_metric R] (@riemannian_chart_reference R m A g hg)
    (riemannian_map_euclidean_source_jacobian f m).
Proof.
move=> hLip.
pose X := [the topologicalType of riemannian_metric_space hg].
pose E := [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)].
pose phi := @riemannian_chart_reference R m A g hg.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have [C hBase] := @riemannian_chart_countable_open_base R m A g hg.
apply: (@measure_local_function_measurability R X [the topologicalType of real_line_metric R]
  phi C (riemannian_map_euclidean_source_jacobian f m) hPhi hBase).
- move=> V hV; exact: riemannian_chart_reference_borel_measurable (open_borel_set hV).
- move=> a.
  have [U [K [F [hU [hUa [hUA [hK [hBound [hRange hAgree]]]]]]]]] :=
    @riemannian_path_map_local_coordinates R m n A B g h hg hh f hLip a.
  pose V : set X := (fun x : X=>(val x : E)) @^-1` U.
  have hV : open V.
    exact (@open_comp X E (fun x=>val x) U
      (fun x _=>@riemannian_chart_inclusion_continuous R m A g hg x) hU).
  exists V; split; first exact hV; split; first exact hUa.
  have hFLip : is_metric_lipschitz setT F by exists K; split.
  pose J := @target_riemannian_jacobian R m n B h hh F hRange m.
  have hJMeas := @riemannian_reference_function_precompose R m A g hg
    [the topologicalType of real_line_metric R] J
    (@target_riemannian_area_jacobian_measurable R m n B h hh F hRange hFLip).
  apply: (@restricted_graph_agreement_measurable R X [the topologicalType of real_line_metric R]
    phi V (partial_function_precompose (fun x : X=>val x) J)
    (riemannian_map_euclidean_source_jacobian f m) hPhi hJMeas).
  move=> x hx j; exact: (iff_sym (@riemannian_map_jacobian_local_coordinates R m n A B g h
    hg hh f U F hRange hU hUA hAgree x hx m j)).
Qed.

(** Source for [riemannian_map_area_jacobian_measurable]:
    the actual original Riemannian area Jacobian is
    measurable, supporting 3.2.46, p. 282. Divide
    its proved coordinate form by the strictly positive
    source density; zero Jacobians and dimension zero remain. *)
Theorem riemannian_map_area_jacobian_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f ->
  @is_measure_measurable_function R [the choiceType of riemannian_metric_space hg]
    [the topologicalType of real_line_metric R] (@riemannian_chart_reference R m A g hg)
    (riemannian_map_jacobian f m).
Proof.
move=> hLip.
pose X := [the topologicalType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R m A g hg.
pose w := partial_function_total (fun x : X=>(riemannian_chart_volume_density hg x : real_line_metric R)).
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have hW : is_measure_measurable_function phi w.
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hPhi.
  - move=> U hU; rewrite /w partial_function_total_preimage.
    apply: (@riemannian_chart_reference_borel_measurable R m A g hg).
    exact (@continuous_borel_preimage X (real_line_metric R) (riemannian_chart_volume_density hg)
      (@riemannian_chart_volume_density_continuous R m A g hg) U (open_borel_set hU)).
have hInv := @measurable_function_borel_postcomposition R X [the topologicalType of real_line_metric R]
  [the topologicalType of real_line_metric R] phi hPhi w (fun r=>r^-1) hW (@real_reciprocal_borel R).
have hJ := @riemannian_map_coordinate_area_jacobian_measurable R m n A B g h hg hh f hLip.
have hProduct := measurable_real_function_multiply hPhi hJ hInv.
apply: (@measurable_function_graph_equivalent R X [the topologicalType of real_line_metric R]
  phi _ (riemannian_map_jacobian f m) _ hProduct)=> x j.
split.
- move=> [[q r] [[hq [s [hs <-]]] hValue]].
  change (riemannian_chart_volume_density hg x=s) in hs; rewrite -hs in hValue.
  have [t [ht hQ]] := (@riemannian_map_source_volume_graph R m n A B g h hg hh f x q).1 hq.
  have hNonzero := lt0r_neq0 (@riemannian_chart_volume_density_positive R m A g hg x).
  have hEq : t=j by rewrite -hQ mulfK in hValue.
  by rewrite -hEq.
- move=> hJx.
  pose d := riemannian_chart_volume_density hg x.
  exists (j*d,d^-1); split.
  + split.
    * apply: (@riemannian_map_source_volume_graph R m n A B g h hg hh f x _).2.
      exists j; by split.
    * exists d; by split.
  + change (j*d*d^-1=j); rewrite mulfK //.
    exact: lt0r_neq0 (@riemannian_chart_volume_density_positive R m A g hg x).
Qed.

(** Source for [extended_riemannian_map_area_jacobian_measurable]:
    the actual extended-real area integrand retains its
    original partial domain, supporting 3.2.46, p. 282.
    Measurability and the conull differential domain are
    consequences of the original path-Lipschitz premise. *)
Corollary extended_riemannian_map_area_jacobian_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f ->
  is_measure_measurable_function (@riemannian_chart_reference R m A g hg)
    (extended_riemannian_map_jacobian f m).
Proof.
move=> hLip.
exact (@measurable_partial_real_embedding R _ (@riemannian_chart_reference R m A g hg)
  (@riemannian_chart_reference_is_measure R m A g hg) _
  (@riemannian_map_area_jacobian_measurable R m n A B g h hg hh f hLip)).
Qed.
