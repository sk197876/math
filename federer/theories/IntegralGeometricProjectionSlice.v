(** Supporting the last formula of Federer (1969), 2.10.16, p. 178: the
    inner integral is with respect to actual I_1^m on R^k, while counting
    fibres of p restricted to A. The fixed-p average follows from the
    composed-count calculation and Fubini. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanMetricCompleteness EuclideanMetricSeparability EuclideanLebesgueDimensions
  ProjectionMultiplicityIntegral ProjectionJointMultiplicity ProjectionJointMultiplicityIntegral
  EuclideanProjectionComposition ProjectionComposedCountIntegral
  IntegralGeometricMeasure ProjectionBeta OrthogonalProjectionProbability
  BorelImageCoverCost BorelCaratheodoryMeasure BorelMultiplicityIntegral BorelImageMeasurability
  TopologicalBorel BorelRegularMeasureUP ExtendedRealOrderTopology PartialFunctionBasic PartialProductSections
  MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  ClosedCoverTreeSealed CoverPartitionTreeSealed CountablyMeasurableUP CountablyMeasurableFunctions
  CountablyMeasurableNullModification ProductFunctionFubini ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_slice_multiplicity_integral]: direct
    inner integral in the final display of 2.10.16, p. 178.
    Count p-fibres using N and integrate over R^k with actual
    I_1^m. No alternative measure is defined here. *)
Definition projection_slice_multiplicity_integral (R : realType) (n k m : nat)
    (hmk : (m<=k)%N) (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n k) : extended_real_line R :=
  measure_lower_integral (@integral_geometric_measure R k m hmk 1)
    (projection_multiplicity_integrand A p).

(** Source for [projection_slice_image_measure_integral]: supporting
    actual inner integral of 2.10.16, p. 178. Apply
    2.10.10, p. 176, with target measure I_1^m on R^k;
    2.2.13, pp. 69–70, discharges image measurability. *)
Lemma projection_slice_image_measure_integral (R : realType) (n k m : nat)
    (hmk : (m<=k)%N) (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n k) : borel_set A ->
  is_measure_integral (@integral_geometric_measure R k m hmk 1)
    (projection_multiplicity_integrand A p)
    (@borel_caratheodory_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (borel_image_cover_cost (euclidean_projection_linear p) (@integral_geometric_measure R k m hmk 1)) A).
Proof.
move=> hA; have [D [hD hden]] := euclidean_metric_separable R n.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R k)].
pose beta := @integral_geometric_measure R k m hmk 1.
have hb : is_measure beta := @integral_geometric_measure_is_measure R k m hmk 1 (lexx _).
have hr : is_borel_regular_measure beta := @integral_geometric_measure_borel_regular R k m hmk 1 (lexx _).
apply: (@borel_multiplicity_integral R X Y (euclidean_projection_linear p) beta hb D A hD hden _ hA)=> S hS.
apply: (@continuous_borel_image_measurable R X Y (euclidean_projection_linear p) beta hb S
  (@euclidean_metric_complete R n) (ex_intro _ D (conj hD hden)) (@metric_hausdorff R Y)
  (@euclidean_projection_continuous R n k p) _ hS).
move=> C hC; exact (@borel_regular_borel_measurable R Y beta hb hr C (closed_borel_set hC)).
Qed.

(** Source for [projection_slice_multiplicity_integral_specification]:
    supporting actual integrability assertion for the inner
    integral in 2.10.16, p. 178, with infinite values retained. *)
Theorem projection_slice_multiplicity_integral_specification (R : realType) (n k m : nat)
    (hmk : (m<=k)%N) (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n k) : borel_set A ->
  is_measure_integral (@integral_geometric_measure R k m hmk 1)
    (projection_multiplicity_integrand A p) (projection_slice_multiplicity_integral hmk A p).
Proof.
move=> hA; have hi := projection_slice_image_measure_integral hmk p hA.
have he := measure_lower_integral_unique (measure_lower_integral_specification _ _) hi.2.2.
by rewrite /projection_slice_multiplicity_integral he.
Qed.

(** Source for [projection_slice_multiplicity_image_measure]:
    supporting partition-cost identification of the actual
    inner integral in 2.10.16, p. 178, by 2.10.10, p. 176. *)
Lemma projection_slice_multiplicity_image_measure (R : realType) (n k m : nat)
    (hmk : (m<=k)%N) (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n k) : borel_set A ->
  projection_slice_multiplicity_integral hmk A p=
    @borel_caratheodory_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (borel_image_cover_cost (euclidean_projection_linear p) (@integral_geometric_measure R k m hmk 1)) A.
Proof.
move=> hA; exact: measure_integral_unique
  (projection_slice_multiplicity_integral_specification hmk p hA)
  (projection_slice_image_measure_integral hmk p hA).
Qed.

(** Source for [projection_sliced_parameter_integral]: supporting
    fixed-p averaged calculation for the final formula in
    2.10.16, p. 178. The q-average of the actual Lebesgue
    composite multiplicity integral is beta_1(k,m) times
    the actual I_1^m multiplicity integral of p. *)
Theorem projection_sliced_parameter_integral (R : realType) (n k m : nat)
    (hmk : (m<=k)%N)
    (C : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k ->
      orthogonal_projection_metric_space R n m)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n k) :
  is_euclidean_projection_composition C -> borel_set A ->
  is_measure_integral (@orthogonal_projection_probability R k m hmk)
    (partial_function_total (fun q => projection_multiplicity_integral A (C (q,p))))
    ((@projection_beta R k m hmk 1)%:E*projection_slice_multiplicity_integral hmk A p).
Proof.
move=> hC hA.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose Q := orthogonal_projection_metric_space R k m.
have [D [hD hden]] := euclidean_metric_separable R n.
have hX : (@setT X) !=set0 by exists (0%R : X).
pose E := @ClosedCoverTree.value R X D hD hden hX.
pose P := @CoverPartitionTree.value X E.
have hi := @projection_composed_count_tree_integral R n k m hmk C p E P A hC
  (@ClosedCoverTree.laws R X D hD hden hX) (@CoverPartitionTree.laws X E) hA.
have he := @projection_slice_multiplicity_image_measure R n k m hmk A p hA.
rewrite -he in hi.
pose f := partial_function_total (fun z : Y*Q => projection_joint_multiplicity A (z.1,C (z.2,p))).
have hcount : is_countably_measure_measurable_function (@projection_product_measure R k m hmk)
    (0 : extended_real_line R) f.
  exact: (@countably_measurable_function_on_countable_source R (Y*Q)%type (extended_real_line R)
    _ (@projection_product_measure_is_measure R k m hmk) 0 f (@extended_real_zero_closed R)
    (@projection_product_whole_countably_measurable R k m hmk) hi.1).
have ho := (@product_function_fubini R Y Q (@euclidean_lebesgue_measure R m)
  (@orthogonal_projection_probability R k m hmk) (@euclidean_lebesgue_is_measure R m)
  (@theta_star_is_measure R k m hmk) f _ hi hcount).2.
apply: (@measure_integral_graph_equivalent R Q _ _ _ _ _ ho)=> q z.
rewrite parameterized_integral_specification.
change (is_measure_integral (@euclidean_lebesgue_measure R m)
  (projection_multiplicity_integrand A (C (q,p))) z <-> projection_multiplicity_integral A (C (q,p))=z).
have hsec := projection_multiplicity_integral_specification (C (q,p)) hA.
split; first by move=> hz; exact: esym (measure_integral_unique hz hsec).
by move=> <-.
Qed.
