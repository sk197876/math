(** Supporting the affine-slice integral in Federer (1969), 2.10.16, p. 178:
    continuous reparametrisation of (y,p) preserves measurability of its
    counting function for any source measure with measurable closed sets.
    Use the Suslin incidence sets of 2.10.5, p. 172, their continuous
    inverse images (2.2.10, p. 66), and 2.2.13, pp. 69–70. This proves the
    needed composition rather than assuming that an arbitrary
    completed-measurable function stays measurable under every continuous
    map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanMetricSeparability ProjectedVolumeIncidence ProjectionJointMultiplicity
  ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  PartialFunctionBasic TotalExtendedLowerLimit MeasureUP MeasureIntegralUP MeasurableFunctionUP
  TopologicalBorel BorelFamilyBasic BorelClosedProjection SuslinPreimages SuslinMeasurability
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic ClosedCoverTreeSealed CoverPartitionTreeSealed
  ShrinkingBorelPartitionLevels PartitionCountingLimit MappingMultiplicity
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral
  NonnegativeSum NonnegativeSumSupport TotalCountableNonnegativeIntegral SuslinSetUP SuslinPartitionCostLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_joint_tree_precomposition_measurable]:
    supporting reparametrisation of the joint count in 2.10.16,
    p. 178. The partition characteristic sets have Suslin
    continuous inverse images, hence are measurable for the
    actual source measure. Their countable sums increase to N. *)
Lemma projection_joint_tree_precomposition_measurable (R : realType)
    (X : topologicalType) (n m : nat) (mu : set X -> \bar R)
    (u : X -> inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure mu -> (forall C, closed C -> measure_measurable mu C) -> continuous u ->
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  is_measure_measurable_function mu
    (partial_function_total (fun x => projection_joint_multiplicity A (u x))).
Proof.
move=> hm hclosed hu hE hP hA.
pose Z := (inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m)%type.
pose F j x := projection_joint_partition_count (m:=m) P A j (u x).
pose chi s := @CharacteristicFunction.value R Z (projection_incidence (m:=m) (A `&` P s)).
have hS s : is_suslin_set R (A `&` P s) :=
  @suslin_partition_cell R (inner_metric_space (@euclidean_inner_productP R n)) E P hE hP A s hA.
have hchi s : is_characteristic_function
    (u @^-1` projection_incidence (m:=m) (A `&` P s)) (fun x => chi s (u x)).
  have hh := @CharacteristicFunction.laws R Z (projection_incidence (m:=m) (A `&` P s)).
  constructor.
  - move=> x hx; exact (characteristic_on_set hh hx).
  - move=> x hx; exact (characteristic_off_set hh hx).
have hmeas s : measure_measurable mu (u @^-1` projection_incidence (m:=m) (A `&` P s)).
  apply: (@suslin_set_measurable R X mu hm _ hclosed).
  apply: (@continuous_preimage_suslin R X Z u _ hu).
  exact: projection_incidence_suslin (hS s).
have hF j : is_measure_measurable_function mu (partial_function_total (F j)).
  have hi := @total_countable_nonnegative_integral R X [the choiceType of (seq nat : Type)]
    mu hm [set s | size s=j] (fun s x => ((chi s (u x))%:E : extended_real_line R))
    (fun s => mu (u @^-1` projection_incidence (m:=m) (A `&` P s)))
    (cover_partition_level_countable j)
    (fun s hs x => characteristic_extended_nonnegative (hchi s) x)
    (fun s hs => @measure_total_characteristic_integral R X mu hm _ _ (hchi s) (hmeas s)).
  have he : (fun x => nonnegative_sum [set s | size s=j] (fun s => (chi s (u x))%:E))=F j.
    apply/funext=> x; exact: projection_joint_partition_characteristic_sum.
  by rewrite he in hi; exact: hi.1.
have hlim x : extended_increases_to (fun j => F j x) (projection_joint_multiplicity A (u x)).
  exact: (@partition_hit_count_limit R (inner_metric_space (@euclidean_inner_productP R n))
    E P hE hP (mapping_fibre (euclidean_projection_linear (u x).2) A (u x).1)).
have hmon i j x : (i<=j)%N -> F i x<=F j x := (hlim x).1 i j.
have he : total_extended_lower_limit F=(fun x => projection_joint_multiplicity A (u x)).
  apply/funext=> x; exact: extended_order_limit_unique
    (total_extended_lower_limit_increases hmon x).2 (hlim x).2.
rewrite -he; exact (@total_extended_lower_limit_measurable R X mu hm F hF).
Qed.

(** Source for [projection_joint_suslin_precomposition_measurable]: supporting
    actual affine-parameter measurability in 2.10.16, p. 178.
    Suslin source sets are allowed. No completeness, separability
    or finite-mass assumption on the parameter source is added; measurable closed sets suffice. *)
Theorem projection_joint_suslin_precomposition_measurable (R : realType)
    (X : topologicalType) (n m : nat) (mu : set X -> \bar R)
    (u : X -> inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure mu -> (forall C, closed C -> measure_measurable mu C) ->
  continuous u -> is_suslin_set R A ->
  is_measure_measurable_function mu
    (partial_function_total (fun x => projection_joint_multiplicity A (u x))).
Proof.
move=> hm hclosed hu hA.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
have [D [hD hden]] := euclidean_metric_separable R n.
have hY : (@setT Y) !=set0 by exists (0%R : Y).
pose E := @ClosedCoverTree.value R Y D hD hden hY.
pose P := @CoverPartitionTree.value Y E.
exact: (@projection_joint_tree_precomposition_measurable R X n m mu u E P A hm hclosed hu
  (@ClosedCoverTree.laws R Y D hD hden hY) (@CoverPartitionTree.laws Y E) hA).
Qed.

(** Source for [projection_joint_precomposition_measurable]: supporting
    actual affine-parameter measurability in 2.10.16, p. 178.
    Suslin source sets are allowed. No completeness, separability
    or finite-mass assumption on the parameter source is added; measurable closed sets suffice. *)
Theorem projection_joint_precomposition_measurable (R : realType)
    (X : topologicalType) (n m : nat) (mu : set X -> \bar R)
    (u : X -> inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure mu -> (forall C, closed C -> measure_measurable mu C) ->
  continuous u -> borel_set A ->
  is_measure_measurable_function mu
    (partial_function_total (fun x => projection_joint_multiplicity A (u x))).
Proof.
move=> hm hclosed hu hA.
exact (@projection_joint_suslin_precomposition_measurable R X n m mu u A hm hclosed hu
  (metric_borel_suslin hA)).
Qed.
