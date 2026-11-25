(** Joint normal-map counts supporting Federer (1969), 2.10.16, p. 178.
    Continuous parameter substitutions preserve the Suslin incidence
    argument of 2.10.10, p. 176; partition counts increase to actual
    multiplicity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric Hom
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HomogeneousSpaceUP HomogeneousSpaceLaws
  TopologicalProductMaps StackedNormalFamily ContinuousFamilyIncidence ContinuousFamilyMultiplicity
  ContinuousFamilyPrecomposition MetricProductBackground MetricProductCompleteness MetricProductSeparability
  ExtendedRealOrderTopology PartialFunctionBasic MeasurableFunctionUP MeasureUP TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stacked_normal_count_precomposition_measurable]:
    supporting actual joint count measurability for the
    double-slicing formula of 2.10.16, p. 178.
    The parameter source need only be topological with
    measurable closed sets; the metric incidence argument
    takes place in the complete separable projection product. *)
Theorem stacked_normal_count_precomposition_measurable (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)})
    (T : topologicalType) (mu : set T -> \bar R) (hm : is_measure mu)
    (u : T -> inner_metric_space (@euclidean_inner_productP R (a+r))*
      (orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_stacked_normal_family F -> continuous u -> borel_set A ->
  (forall C, closed C -> measure_measurable mu C) ->
  is_measure_measurable_function mu (partial_function_total (fun z =>
    family_multiplicity (R:=R) (fun w => F w.1 w.2) A (u z))).
Proof.
move=> hF hu hA hc.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose P := [the metricType R of metric_product (orthogonal_projection_metric_space R n a)
  (orthogonal_projection_metric_space R n r)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R (a+r))].
have hnon : (@setT X)!=set0 by exists (0%R : X).
exact (@continuous_family_multiplicity_precomposition_measurable R X P Y T
  (fun w => F w.1 w.2) mu hm u A (@euclidean_metric_complete R n)
  (complete_metric_product (@orthogonal_projection_metric_complete R n a) (@orthogonal_projection_metric_complete R n r))
  (euclidean_metric_separable R n)
  (separable_metric_product (orthogonal_projection_metric_separable R n a) (orthogonal_projection_metric_separable R n r))
  hnon (@metric_hausdorff R Y) (@stacked_normal_family_continuous R n a r F hF) hu (metric_borel_suslin hA) hc).
Qed.

Section FramePair.
Variable R : realType.
Variables n a r : nat.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Local Notation Aa := (orthogonal_projection_action (@euclidean_inner_productP R a) hBn hbn hO).
Local Notation Ar := (orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO).

(** Source for [normal_frame_pair_continuous]: supporting
    continuous double-frame parameter in 2.10.16,
    p. 178, from the orbit continuity of 2.7.1,
    p. 121, for the actual action of 2.7.16(6), p. 139. *)
Lemma normal_frame_pair_continuous (p : orthogonal_projection_metric_space R n a)
    (q : orthogonal_projection_metric_space R n r) :
  continuous (fun z : O*O => (Aa z.1 p,Ar z.2 q)).
Proof.
pose P := euclidean_projection_space R n a.
pose Q := euclidean_projection_space R n r.
change (continuous (fun z : O*O => ((Aa z.1 p : P),(Ar z.2 q : Q)))).
have hp := orbit_map_continuous (orthogonal_projections_homogeneous
  (@euclidean_inner_productP R a) (@coordinate_basisP R a) hO) p.
have hq := orbit_map_continuous (orthogonal_projections_homogeneous
  (@euclidean_inner_productP R r) (@coordinate_basisP R r) hO) q.
apply (@topological_pair_continuous (O*O)%type P Q (fun z => Aa z.1 p) (fun z => Ar z.2 q)).
- move=> z; exact (continuous_comp (@first_projection_continuous O O z) (hp z.1)).
- move=> z; exact (continuous_comp (@second_projection_continuous O O z) (hq z.2)).
Qed.

(** Source for [stacked_normal_family_rotation]: supporting
    diagonal normal-map rotation for 2.10.16, p. 178.
    The defining block laws show that simultaneous rotation
    of both normal maps is precomposition by g inverse. *)
Lemma stacked_normal_family_rotation
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q g x,
  F (Aa g p,Ar g q) x=F (p,q) (orthogonal_element_map (invO g) x).
Proof.
move=> hF p q g x.
rewrite !(@stacked_normal_familyE R n a r F hF).
congr (EuclideanBlockCoordinates.euclidean_block_join (_, _));
  exact: orthogonal_projection_actionE.
Qed.
End FramePair.
