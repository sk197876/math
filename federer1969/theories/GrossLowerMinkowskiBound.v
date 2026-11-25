(** Federer (1969), 3.2.37, p. 274: lower Minkowski content
    dominates Gross measure on every source subset. Expand the
    compact-family reduction from the all-Borel-partition theorem
    2.10.8 using actual compact-source projection approximation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanMetricSeparability MinkowskiContents MinkowskiContentsBasic
  LowerMinkowskiProjectionBound FiniteCompactMinkowskiProjectionSum
  CompactProjectionFamilyUP CompactProjectionFamilyBounds GrossCompactProjectionSupremum
  FiniteCompactProjectionApproximation ProjectedVolumeGauge ProjectionMeasure
  BorelPartition BorelPartitionCoverBounds BorelPartitionCharacterization
  BorelCaratheodoryMeasure BorelClosedProjection TopologicalBorel
  NonnegativeSum MeasureUP MeasureBasic ExtendedRealBoundsUP ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_measure_borel_lower_minkowski_bound]: the
    Borel case in the proof of the last display of Federer 3.2.37,
    p. 274. Each finite Borel partition subfamily is approximated
    by genuinely disjoint compact source pieces with their own actual
    projections. No Radon or finite Gross-mass premise is imposed. *)
Lemma gross_measure_borel_lower_minkowski_bound (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->borel_set A ->@gross_measure R n m A<=lower_minkowski_content m A.
Proof.
move=>hmn hA.
have hSup:=@gross_measure_compact_projection_supremum R n m A hmn hA.
apply:(extended_real_supremum_least hSup)=>v [I [K [p [hFamily ->]]]].
exact:(@compact_projected_family_lower_minkowski_bound R n m A I K p hmn hFamily).

Qed.

(** Source for [gross_measure_lower_minkowski_bound]: the last
    display in Federer 3.2.37, p. 274, for every original A.
    Closure gives a Borel superset without changing either tube
    content; measure monotonicity restores the arbitrary source.
    No source measurability or finite-mass premise is added. *)
Theorem gross_measure_lower_minkowski_bound (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->@gross_measure R n m A<=lower_minkowski_content m A.
Proof.
move=>hmn.
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
have hMono:=@measure_mono R X (@gross_measure R n m)
  (@gross_measure_is_measure R n m hmn) A (closure A) (fun x hx=>subset_closure hx).
have hClosed:=@closed_borel_set X (closure A) (@closed_closure X A).
have hBound:=@gross_measure_borel_lower_minkowski_bound R n m (closure A) hmn hClosed.
rewrite (minkowski_contents_closure m A).2 in hBound.
exact:le_trans hMono hBound.
Qed.
