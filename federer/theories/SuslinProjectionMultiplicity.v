(** Supporting Federer (1969), 2.10.16, p. 178: actual
    projection-multiplicity integrals on Suslin images of Borel sets,
    extending the Borel-source result of 2.10.15, p. 178. Use the proved
    continuous Suslin multiplicity theorem; neither the public integral
    value nor the counting function is redefined. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanLebesgueDimensions EuclideanLebesgueHaar ExtendedRealOrderTopology
  PartialFunctionBasic MappingMultiplicity MeasureUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness NonnegativeExtendedNormOrder
  BorelRegularMeasureUP TopologicalBorel BorelImageMeasurability
  BorelImageCoverCost BorelCaratheodoryMeasure BorelMultiplicityIntegral ProjectionMultiplicityIntegral SuslinSetUP SuslinMultiplicityIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_multiplicity_suslin_image_measure_integral]:
    supporting Suslin extension of 2.10.10, p. 176,
    for the projection slices of 2.10.16, p. 178. The actual image-cost measure
    integrates counting multiplicity for each orthogonal projection. *)
Lemma projection_multiplicity_suslin_image_measure_integral (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : is_suslin_set R A ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A p)
    (@borel_caratheodory_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (borel_image_cover_cost (euclidean_projection_linear p) (@euclidean_lebesgue_measure R m)) A).
Proof.
move=> hA; have [D [hD hden]] := euclidean_metric_separable R n.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
have hm := @euclidean_lebesgue_is_measure R m.
have hreg := @euclidean_lebesgue_borel_regular R m.
apply: (@continuous_suslin_multiplicity_integral R X Y (euclidean_projection_linear p)
  (@euclidean_lebesgue_measure R m) hm hreg A (@euclidean_metric_complete R n)
  (ex_intro _ D (conj hD hden)) (@metric_hausdorff R Y) _ hA).
exact: euclidean_projection_continuous.
Qed.

(** Source for [projection_multiplicity_suslin_integral_specification]:
    direct actual integral in 2.10.15, p. 178. Measurability
    of counting multiplicity is part of this conclusion. *)
Theorem projection_multiplicity_suslin_integral_specification (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : is_suslin_set R A ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A p) (projection_multiplicity_integral A p).
Proof.
move=> hA; have hi := projection_multiplicity_suslin_image_measure_integral p hA.
have he := measure_lower_integral_unique
  (measure_lower_integral_specification (@euclidean_lebesgue_measure R m) _) hi.2.2.
by rewrite /projection_multiplicity_integral he.
Qed.

(** Source for [projection_multiplicity_suslin_integral_image_measure]:
    supporting image-cost identification in the 2.10.15 proof,
    p. 178, by integral uniqueness in 2.10.10, p. 176. *)
Lemma projection_multiplicity_suslin_integral_image_measure (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : is_suslin_set R A ->
  projection_multiplicity_integral A p=@borel_caratheodory_measure R (inner_metric_space (@euclidean_inner_productP R n))
    (borel_image_cover_cost (euclidean_projection_linear p) (@euclidean_lebesgue_measure R m)) A.
Proof.
move=> hA; exact: measure_integral_unique
  (projection_multiplicity_suslin_integral_specification p hA)
  (projection_multiplicity_suslin_image_measure_integral p hA).
Qed.
