(** Supporting Suslin-source extension of Federer (1969), 2.10.16, p. 178,
    for the projected images appearing in its further slicing identities.
    The actual joint count remains the same sealed counting measure of the
    fibres. Source context and scalar convergence references:
    ProjectionJointMultiplicity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanMetricSeparability EuclideanLebesgueDimensions
  OrthogonalProjectionProbability ProjectedVolumeIncidence ProjectedVolumeMeasurability
  ProjectionIncidenceMeasure ExtendedRealOrderTopology ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum PartialFunctionBasic TotalExtendedLowerLimit
  MeasureUP MeasureBasic MeasureIntegralUP MeasurableFunctionUP ProductMeasure
  TopologicalBorel BorelFamilyBasic BorelClosedProjection
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic
  ClosedCoverTreeSealed CoverPartitionTreeSealed ShrinkingBorelPartitionLevels
  PartitionHitCounts PartitionCountingLimit PartitionImageCharacteristicSum MappingMultiplicity
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral
  NonnegativeSum NonnegativeSumSupport TotalCountableNonnegativeIntegral ProjectionJointMultiplicity SuslinPartitionCostLimits SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_joint_suslin_partition_count_integral]: supporting
    measurability of every joint count approximation in 2.10.16,
    p. 178. Countable characteristic integration gives its actual
    product integral as the sum of incidence measures of the cells. *)
Lemma projection_joint_suslin_partition_count_integral (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  is_measure_integral (@projection_product_measure R n m hmn)
    (partial_function_total (projection_joint_partition_count (m:=m) P A j))
    (nonnegative_sum [set s | size s=j]
      (fun s => @projected_incidence_measure R n m hmn (A `&` P s))).
Proof.
move=> hE hP hA.
pose Z := (inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m)%type.
pose mu := @projection_product_measure R n m hmn.
pose chi s := @CharacteristicFunction.value R Z (projection_incidence (m:=m) (A `&` P s)).
have hchi s := @CharacteristicFunction.laws R Z (projection_incidence (m:=m) (A `&` P s)).
have hS s : is_suslin_set R (A `&` P s) :=
  @suslin_partition_cell R (inner_metric_space (@euclidean_inner_productP R n)) E P hE hP A s hA.
have hinc s : measure_measurable mu (projection_incidence (m:=m) (A `&` P s)).
  exact: (@projection_incidence_product_measurable R n m _ (@theta_star_is_measure R n m hmn)
    _ (@theta_star_borel_regular R n m hmn) (hS s)).
have hi := @total_countable_nonnegative_integral R [the choiceType of Z]
  [the choiceType of (seq nat : Type)] mu (@projection_product_measure_is_measure R n m hmn)
  [set s | size s=j] (fun s z => ((chi s z)%:E : extended_real_line R))
  (fun s => @projected_incidence_measure R n m hmn (A `&` P s))
  (cover_partition_level_countable j)
  (fun s hs z => characteristic_extended_nonnegative (hchi s) z)
  (fun s hs => @measure_total_characteristic_integral R [the choiceType of Z] mu
    (@projection_product_measure_is_measure R n m hmn) _ (chi s) (hchi s) (hinc s)).
have he : (fun z => nonnegative_sum [set s | size s=j] (fun s => (chi s z)%:E))=
    projection_joint_partition_count (m:=m) P A j.
  apply/funext=> z; exact: projection_joint_partition_characteristic_sum.
by rewrite he in hi.
Qed.

(** Source for [projection_joint_suslin_multiplicity_tree_measurable]: supporting Suslin-source
    joint-measurability calculation of 2.10.16, p. 178, for
    an abstract shrinking Borel partition tree. Both finite and
    infinite fibre counts are the actual pointwise limit. *)
Theorem projection_joint_suslin_multiplicity_tree_measurable (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  is_measure_measurable_function (@projection_product_measure R n m hmn)
    (partial_function_total (projection_joint_multiplicity (m:=m) A)).
Proof.
move=> hE hP hA.
pose F j := projection_joint_partition_count (m:=m) P A j.
have hlim z : extended_increases_to (fun j => F j z) (projection_joint_multiplicity A z).
  exact: (@partition_hit_count_limit R (inner_metric_space (@euclidean_inner_productP R n))
    E P hE hP (mapping_fibre (euclidean_projection_linear z.2) A z.1)).
have hmon i j z : (i<=j)%N -> F i z<=F j z := (hlim z).1 i j.
have he : total_extended_lower_limit F=projection_joint_multiplicity (m:=m) A.
  apply/funext=> z; exact: extended_order_limit_unique
    (total_extended_lower_limit_increases hmon z).2 (hlim z).2.
rewrite -he; apply: (total_extended_lower_limit_measurable
  (@projection_product_measure_is_measure R n m hmn))=> j.
exact: (@projection_joint_suslin_partition_count_integral R n m hmn E P A j hE hP hA).1.
Qed.

(** Source for [projection_joint_suslin_multiplicity_measurable]: supporting Suslin-source extension of the
    first sentence of 2.10.16, p. 178. The previously sealed
    tree existence supplies the partition without any extra
    hypothesis on the Suslin set A. *)
Theorem projection_joint_suslin_multiplicity_measurable (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) : is_suslin_set R A ->
  is_measure_measurable_function (@projection_product_measure R n m hmn)
    (partial_function_total (projection_joint_multiplicity (m:=m) A)).
Proof.
move=> hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have [D [hD hden]] := euclidean_metric_separable R n.
have hX : (@setT X) !=set0 by exists (0%R : X).
pose E := @ClosedCoverTree.value R X D hD hden hX.
pose P := @CoverPartitionTree.value X E.
exact: (@projection_joint_suslin_multiplicity_tree_measurable R n m hmn E P A
  (@ClosedCoverTree.laws R X D hD hden hX) (@CoverPartitionTree.laws X E) hA).
Qed.
