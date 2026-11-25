(** Federer (1969), 2.10.15, p. 178, opening display: g(p) is the Lebesgue
    integral of N(p restricted to A,y). Use the already abstract integral
    value and prove its actual integrability from 2.10.10, p. 176. Its
    equality with the image-cost Caratheodory measure is a consequence, not
    the definition of g. The source is Euclidean, complete and separable;
    projections are continuous and Borel images are Lebesgue measurable by
    2.2.13, pp. 69–70. No relevant local erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanLebesgueDimensions EuclideanLebesgueHaar ExtendedRealOrderTopology
  PartialFunctionBasic MappingMultiplicity MeasureUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness NonnegativeExtendedNormOrder
  BorelRegularMeasureUP TopologicalBorel BorelImageMeasurability
  BorelImageCoverCost BorelCaratheodoryMeasure BorelMultiplicityIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_multiplicity_integrand]: direct
    counting integrand N(p restricted to A,y) in the first
    display of 2.10.15, p. 178, including infinite fibres. *)
Definition projection_multiplicity_integrand (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :=
  partial_function_total (fun y => (@mapping_multiplicity R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear p) A y : extended_real_line R)).

(** Source for [projection_multiplicity_integral]: direct g(p)
    from 2.10.15, p. 178. Its nonnegative integral uses
    the abstract lower-integral value; actual integrability on
    Borel A is proved below, not postulated. *)
Definition projection_multiplicity_integral (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : extended_real_line R :=
  measure_lower_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A p).

(** Source for [euclidean_projection_borel_image_measurable]:
    supporting projection-image measurability in 2.10.15, p. 178,
    by 2.2.13, pp. 69–70. It is needed for the
    partition characteristic integrals of 2.10.10, p. 176. *)
Lemma euclidean_projection_borel_image_measurable (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  borel_set S -> measure_measurable (@euclidean_lebesgue_measure R m)
    (euclidean_projection_linear p @` S).
Proof.
move=> hS; have [D [hD hden]] := euclidean_metric_separable R n.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
have hm := @euclidean_lebesgue_is_measure R m.
have hreg := @euclidean_lebesgue_borel_regular R m.
apply: (@continuous_borel_image_measurable R X Y (euclidean_projection_linear p)
  (@euclidean_lebesgue_measure R m) hm S (@euclidean_metric_complete R n)
  (ex_intro _ D (conj hD hden)) (@metric_hausdorff R Y)
  (@euclidean_projection_continuous R n m p) _ hS).
move=> C hC; apply: (borel_regular_borel_measurable hm hreg); exact: closed_borel_set hC.
Qed.

(** Source for [projection_multiplicity_image_measure_integral]:
    supporting application of 2.10.10, p. 176, in the proof
    of 2.10.15, p. 178. The actual image-cost measure
    integrates counting multiplicity for each orthogonal projection. *)
Lemma projection_multiplicity_image_measure_integral (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : borel_set A ->
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
apply: (@borel_multiplicity_integral R X Y (euclidean_projection_linear p)
  (@euclidean_lebesgue_measure R m) hm D A hD hden _ hA).
move=> S hS; exact: euclidean_projection_borel_image_measurable hS.
Qed.

(** Source for [projection_multiplicity_integral_specification]:
    direct actual integral in 2.10.15, p. 178. Measurability
    of counting multiplicity is part of this conclusion. *)
Theorem projection_multiplicity_integral_specification (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : borel_set A ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A p) (projection_multiplicity_integral A p).
Proof.
move=> hA; have hi := projection_multiplicity_image_measure_integral p hA.
have he := measure_lower_integral_unique
  (measure_lower_integral_specification (@euclidean_lebesgue_measure R m) _) hi.2.2.
by rewrite /projection_multiplicity_integral he.
Qed.

(** Source for [projection_multiplicity_integral_image_measure]:
    supporting image-cost identification in the 2.10.15 proof,
    p. 178, by integral uniqueness in 2.10.10, p. 176. *)
Lemma projection_multiplicity_integral_image_measure (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : borel_set A ->
  projection_multiplicity_integral A p=@borel_caratheodory_measure R (inner_metric_space (@euclidean_inner_productP R n))
    (borel_image_cover_cost (euclidean_projection_linear p) (@euclidean_lebesgue_measure R m)) A.
Proof.
move=> hA; exact: measure_integral_unique
  (projection_multiplicity_integral_specification p hA)
  (projection_multiplicity_image_measure_integral p hA).
Qed.

(** Source for [projection_multiplicity_integral_nonnegative]:
    supporting nonnegativity of g in 2.10.15, p. 178,
    from counting multiplicity and 2.4.4(2), p. 82. *)
Lemma projection_multiplicity_integral_nonnegative (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : borel_set A ->
  0<=projection_multiplicity_integral A p.
Proof.
move=> hA; apply: (@nonnegative_total_integral_value_ge0 R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) (@euclidean_lebesgue_is_measure R m)
  _ _ _ (projection_multiplicity_integral_specification p hA)).
move=> y; exact: mapping_multiplicity_nonnegative.
Qed.
