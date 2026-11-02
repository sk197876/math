(** Supporting the projection slicing identity in Federer (1969), 2.10.16,
    p. 178. For fixed p in O*(n,k), integrate N(q composed with p restricted
    to A,y) over (y,q). On each source partition cell, use the already
    proved Suslin-source Crofton identity for its p-image. Counting
    sandwiches and increasing convergence identify the limit. This expands
    the printed phrase referring to similar arguments; it does not add a
    finiteness assumption. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricCompleteness
  EuclideanMetricSeparability EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanProjectionComposition EuclideanLebesgueDimensions OrthogonalProjectionProbability
  ProjectionBeta IntegralGeometricMeasure ProjectionJointMultiplicity ProjectionProductRegularity
  ProjectionMultiplicityPrecomposition ProjectionPartitionPrecomposition
  SuslinProjectionJointIntegral ProjectionJointMultiplicityIntegral
  SuslinSetUP BorelImageMeasurability BorelClosedProjection SuslinPartitionCostLimits
  TopologicalBorel BorelRegularMeasureUP TopologicalProductMaps
  ClosedCoverTreeUP CoverPartitionTreeUP ClosedCoverTreeSealed CoverPartitionTreeSealed
  PartitionHitCounts PartitionCountingLimit PartitionComposedMultiplicity ShrinkingBorelPartitionLevels
  MappingMultiplicity CountingMeasure NonnegativeSum NonnegativeSumScale
  MeasureUP MeasureBasic MeasureIntegralUP TotalCountableNonnegativeIntegral
  ExtendedRealOrderTopology PartialFunctionBasic BorelImageCoverCost BorelPartitionCostLimits
  BorelCaratheodoryMeasure PositiveFiniteSupremumScale TotalSandwichIntegralSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_composed_count_tree_integral]: supporting
    fixed-p calculation for the last formula of 2.10.16,
    p. 178. The actual product integral equals beta_1(k,m)
    times the image-cost measure for p and I_1^m on R^k. *)
Theorem projection_composed_count_tree_integral (R : realType) (n k m : nat)
    (hmk : (m<=k)%N)
    (C : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k ->
      orthogonal_projection_metric_space R n m)
    (p : orthogonal_projection_metric_space R n k)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_projection_composition C ->
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A ->
  is_measure_integral (@projection_product_measure R k m hmk)
    (partial_function_total (fun z => projection_joint_multiplicity A (z.1,C (z.2,p))))
    ((@projection_beta R k m hmk 1)%:E*
      @borel_caratheodory_measure R (inner_metric_space (@euclidean_inner_productP R n))
        (borel_image_cover_cost (euclidean_projection_linear p)
          (@integral_geometric_measure R k m hmk 1)) A).
Proof.
move=> hC hE hP hA.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Q := orthogonal_projection_metric_space R k m.
pose Z := (Y*Q)%type.
pose mu := @projection_product_measure R k m hmk.
have hm := @projection_product_measure_is_measure R k m hmk.
have hclosed B : closed B -> measure_measurable mu B.
  move=> hB; exact (@borel_regular_borel_measurable R Z mu hm
    (@projection_product_measure_borel_regular R k m hmk) B (closed_borel_set hB)).
pose u (z : Z) := (z.1,C (z.2,p)).
have hu : continuous u.
  apply (@topological_pair_continuous Z Y (orthogonal_projection_metric_space R n m)
    (@fst Y Q) (fun z : Z => C (z.2,p))); first exact: first_projection_continuous.
  have hpair : continuous (fun z : Z => (z.2,p)).
    apply (@topological_pair_continuous Z Q (orthogonal_projection_metric_space R n k)
      (@snd Y Q) (fun _ : Z => p)); [exact: second_projection_continuous|exact: cst_continuous].
  move=> z; exact: continuous_comp (hpair z) (@euclidean_projection_composition_continuous R n k m C hC (z.2,p)).
pose U j z := projection_joint_partition_count P A j (u z).
pose V j (z : Z) : extended_real_line R := nonnegative_sum [set s | size s=j]
  (fun s => projection_joint_multiplicity (euclidean_projection_linear p @` (A `&` P s)) z).
pose g z := projection_joint_multiplicity A (u z).
pose beta := @integral_geometric_measure R k m hmk 1.
pose c : set X -> \bar R := borel_image_cover_cost (euclidean_projection_linear p) beta.
pose b := @projection_beta R k m hmk 1.
have hb : (0<b)%R := @projection_beta_positive R k m hmk 1 (lexx _).
have hS s : @is_suslin_set R (inner_metric_space (@euclidean_inner_productP R k))
    (euclidean_projection_linear p @` (A `&` P s)).
  apply: (@continuous_suslin_image R X (inner_metric_space (@euclidean_inner_productP R k))
    (euclidean_projection_linear p) _ (@euclidean_metric_complete R n)
    (euclidean_metric_separable R n) (@metric_hausdorff R _) (@euclidean_projection_continuous R n k p)).
  exact (@suslin_partition_cell R X E P hE hP A s (metric_borel_suslin hA)).
have hV j : is_measure_integral mu (partial_function_total (V j))
    (b%:E*borel_partition_level_cost c P A j).
  have hi := @total_countable_nonnegative_integral R Z [the choiceType of (seq nat : Type)]
    mu hm [set s | size s=j]
    (fun s z => projection_joint_multiplicity (euclidean_projection_linear p @` (A `&` P s)) z)
    (fun s => b%:E*c (A `&` P s))
    (@cover_partition_level_countable j)
    (fun s hs z => projection_joint_multiplicity_nonnegative _ z)
    (fun s hs => @projection_joint_suslin_multiplicity_integral R k m hmk _ (hS s)).
  have he : nonnegative_sum [set s | size s=j] (fun s => b%:E*c (A `&` P s))=
      b%:E*borel_partition_level_cost c P A j.
    rewrite /borel_partition_level_cost nonnegative_sum_scale; first by [].
    - exact: ltW hb.
    - move=> s hs; exact (@measure_nonnegative R
      [the choiceType of inner_metric_space (@euclidean_inner_productP R k)] beta
      (@integral_geometric_measure_is_measure R k m hmk 1 (lexx _))
      (euclidean_projection_linear p @` (A `&` P s))).
  by rewrite he in hi.
have hs j z : U j z<=V j z /\ V j z<=g z.
  have hh := @partition_composed_multiplicity_sandwich R X
    [the choiceType of inner_metric_space (@euclidean_inner_productP R k)] Y
    (euclidean_projection_linear p) (euclidean_projection_linear z.2) E P hP A j z.1.
  have he : (fun x : X => euclidean_projection_linear z.2 (euclidean_projection_linear p x))=
      (euclidean_projection_linear (C (z.2,p)) : X -> Y).
    apply/funext=> x; exact: esym (hC z.2 p x).
  rewrite he in hh.
  exact hh.
apply (@total_sandwich_integral_supremum R Z mu hm U V g
  (fun j => b%:E*borel_partition_level_cost c P A j)
  (b%:E*@borel_caratheodory_measure R X c A)).
- move=> j z; exact (@measure_nonnegative R [the choiceType of (seq nat : Type)]
    _ (counting_measure_is_measure R _) _).
- move=> z; exact (@partition_hit_count_limit R X E P hE hP
    (mapping_fibre (euclidean_projection_linear (u z).2) A (u z).1)).
- move=> j; exact (@projection_joint_partition_precomposition_integral R Z n m mu u E P A j
    hm hclosed hu hE hP (metric_borel_suslin hA)).1.
- exact (@projection_joint_precomposition_measurable R Z n m mu u A hm hclosed hu hA).
- exact hs.
- exact hV.
- apply: (positive_finite_scaled_sequence_supremum hb).
  exact (@borel_partition_cost_supremum R X c
    (@borel_image_cover_cost_laws R X _ _ beta (@integral_geometric_measure_is_measure R k m hmk 1 (lexx _)))
    E P hE hP A hA).
Qed.
