(** Supporting the slicing formulas of Federer (1969), 2.10.16, p. 178:
    projected-volume partition sums for Suslin source images, extending the
    Borel-source argument in 2.10.15, p. 178. The actual definitions are
    reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  EuclideanProjectionMetric OrthogonalProjectionProbability ProjectionBeta
  ProjectionIncidenceMeasure IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts
  ProjectionMultiplicityIntegral ProjectionMultiplicityPartitions NonnegativeExtendedNormLimitBound
  NonnegativeExtendedExponentNorm NonnegativeExtendedExponentNormUP
  NonnegativeExtendedNormOrder ExtendedPositivePower PositiveFiniteSupremumScale
  ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealOrderLimit PartialFunctionBasic
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic ClosedCoverTreeSealed CoverPartitionTreeSealed
  TopologicalBorel BorelFamilyBasic BorelClosedProjection BorelPartitionCostLimits
  TotalIncreasingIntegralSupremum MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  NonnegativeSumSupport NonnegativeSumScale SuslinProjectionPartitions SuslinPartitionCostLimits
  SuslinIntegralGeometricPartitions SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_multiplicity_suslin_tree_parameter_integral]:
    supporting Suslin-source exponent-one calculation for 2.10.16,
    p. 178, using any of the shrinking partition trees
    specified in 2.10.10, p. 176. The resulting integral
    value is beta_1 times I_1(A), including infinity. *)
Theorem projection_multiplicity_suslin_tree_parameter_integral (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> is_suslin_set R A ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projection_multiplicity_integral (m:=m) A))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A).
Proof.
move=> hE hP hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose b := @projection_beta R n m hmn 1.
pose c := @integral_geometric_gauge R n m hmn 1.
pose k := @projected_incidence_measure R n m hmn.
have hb : (0<b)%R := @projection_beta_positive R n m hmn 1 (lexx _).
have hS s : is_suslin_set R (A `&` P s) :=
  @suslin_partition_cell R X E P hE hP A s hA.
have hecost j : borel_partition_level_cost k P A j=b%:E*borel_partition_level_cost c P A j.
  rewrite /borel_partition_level_cost -nonnegative_sum_scale; last first.
  - move=> s hs; exact: (@integral_geometric_gauge_nonnegative R n m hmn 1 (lexx _) _ (hS s)).
  - exact: ltW hb.
  apply: nonnegative_sum_ext=> s hs.
  exact: esym (@integral_geometric_one_gauge_incidence R n m hmn _ (hS s)).
have hsup0 := @suslin_integral_geometric_partition_supremum R n m hmn E P A hE hP hA.
have hsup : is_extended_real_supremum [set z | exists j, z=borel_partition_level_cost k P A j]
    (b%:E*@integral_geometric_measure R n m hmn 1 A).
  have he : [set z | exists j, z=borel_partition_level_cost k P A j]=
      [set z | exists j, z=b%:E*borel_partition_level_cost c P A j].
    apply/seteqP; split=> z [j ->]; exists j; [exact: hecost|exact: esym (hecost j)].
  rewrite he; exact: positive_finite_scaled_sequence_supremum hb hsup0.
apply: (@total_increasing_integral_supremum R (orthogonal_projection_metric_space R n m)
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (fun j => projection_partition_volume_sum (m:=m) P A j)
  (projection_multiplicity_integral (m:=m) A)
  (fun j => borel_partition_level_cost k P A j)
  (b%:E*@integral_geometric_measure R n m hmn 1 A)).
- move=> j p; exact: projection_partition_volume_sum_nonnegative.
- move=> p; exact: projection_suslin_partition_volume_sum_increases hE hP hA.
- move=> j; exact: projection_suslin_partition_volume_sum_integral hE hP hA.
- exact hsup.
Qed.


(** Source for [suslin_integral_geometric_multiplicity_integral]:
    supporting Suslin-source Crofton identity for the further
    slicing formulas in 2.10.16, p. 178, extending the
    exponent-one case of 2.10.15, p. 178. It proves the
    actual theta-star integral, including infinite values. *)
Theorem suslin_integral_geometric_multiplicity_integral (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R A ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projection_multiplicity_integral (m:=m) A))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A).
Proof.
move=> hA; pose X := inner_metric_space (@euclidean_inner_productP R n).
have [D [hD hden]] := euclidean_metric_separable R n.
have hX : (@setT X) !=set0 by exists (0%R : X).
pose E := @ClosedCoverTree.value R X D hD hden hX.
pose P := @CoverPartitionTree.value X E.
exact (@projection_multiplicity_suslin_tree_parameter_integral R n m hmn E P A
  (@ClosedCoverTree.laws R X D hD hden hX) (@CoverPartitionTree.laws X E) hA).
Qed.
