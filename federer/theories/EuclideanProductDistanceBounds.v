(** Federer (1969), 3.2.36, p. 273:
    the actual first distance is bounded
    by the actual distance to the product. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanCartesianMap CompactSetDistanceProfile CompactHausdorffMetric EuclideanFirstCylinderDistance
  MetricSetDistanceUP MetricSetDistanceSubset.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_first_distance_le_product]:
    supporting the exact positive-strip inclusion
    in the product coarea calculation of
    Federer 3.2.36, p. 273.
    The actual product is contained in the
    first-factor cylinder, whose distance laws
    have been proved. Distance antitonicity
    gives the required pointwise inequality.
    The second factor may be arbitrary;
    no derivative or fibre property is assumed. *)
Lemma euclidean_first_distance_le_product (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (m+n))->R):
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (m+n))) (euclidean_cartesian_set (val A) B) d ->forall z,
    compact_set_distance_profile A (euclidean_block_split z).1<=d z.
Proof.
move=>hD z.
have [_ [_ hCylinder]]:=@euclidean_first_cylinder_distance R m n A.
apply:(@metric_set_distance_subset_bound R
  (inner_metric_space (@euclidean_inner_productP R (m+n)))
  (euclidean_cartesian_set (val A) B)
  [set z|val A (euclidean_block_split z).1] d
  (fun z=>compact_set_distance_profile A (euclidean_block_split z).1)
  _ hD hCylinder z).
by move=>w [hw _].
Qed.
