(** Supporting the partition limits in Federer (1969), 2.10.16, p. 178:
    actual integrals of the joint cell counts after continuous parameter
    substitution. The characteristic preimages are Suslin, hence measurable,
    and countable summation supplies the actual integral. Source context and
    descriptive-set background: ProjectionMultiplicityPrecomposition.v. *)
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

(** Source for [projection_joint_partition_precomposition_integral]:
    supporting countable characteristic integral for the
    parameter substitutions in 2.10.16, p. 178. Only
    measurable closed source sets and continuity are required;
    the original source set A may be Suslin. *)
Lemma projection_joint_partition_precomposition_integral (R : realType)
    (X : topologicalType) (n m : nat) (mu : set X -> \bar R)
    (u : X -> inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j :
  is_measure mu -> (forall C, closed C -> measure_measurable mu C) -> continuous u ->
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  is_measure_integral mu
    (partial_function_total (fun x => projection_joint_partition_count P A j (u x)))
    (nonnegative_sum [set s | size s=j]
      (fun s => mu (u @^-1` projection_incidence (m:=m) (A `&` P s)))).
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
have hi := @total_countable_nonnegative_integral R X [the choiceType of (seq nat : Type)]
    mu hm [set s | size s=j] (fun s x => ((chi s (u x))%:E : extended_real_line R))
    (fun s => mu (u @^-1` projection_incidence (m:=m) (A `&` P s)))
    (cover_partition_level_countable j)
    (fun s hs x => characteristic_extended_nonnegative (hchi s) x)
    (fun s hs => @measure_total_characteristic_integral R X mu hm _ _ (hchi s) (hmeas s)).
have he : (fun x => nonnegative_sum [set s | size s=j] (fun s => (chi s (u x))%:E))=F j.
  apply/funext=> x; exact: projection_joint_partition_characteristic_sum.
by rewrite he in hi.
Qed.
