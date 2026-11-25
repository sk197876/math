(** Supporting full support of theta*_{n,m} for Federer (1969), 2.10.5(2),
    p. 173, essential supremum versus supremum. The normalized invariant
    measure of 2.7.16(6), p. 139, has a nonzero invariant integral;
    positivity on nonzero nonnegative compactly supported tests follows from
    2.7.2–2.7.4, pp. 122–125. The previously proved cutoff argument then
    gives positive measure to each nonempty open parameter set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct FiniteCoordinates EuclideanProjectionMetric
  OrthogonalProjectionProbabilityUP OrthogonalProjectionProbability OrthogonalProjectionConstants
  OrthogonalGroupTopology OrthogonalInjectionSpaces TopologicalGroupUP
  HomogeneousCovariantMeasureRadon InvariantIntegralPositivity SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [theta_star_nonempty_open_positive]:
    supporting positive mass of every nonempty
    open subset of O*(n,m) for the infinity-
    exponent comparison in Federer 2.10.5(2),
    p. 173. It follows from the actual
    normalized invariant probability, not an
    additional full-support assumption. *)
Theorem theta_star_nonempty_open_positive (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (U : set (orthogonal_projection_metric_space R n m)) :
  open U -> (exists p, U p) -> (0<@orthogonal_projection_probability R n m hmn U)%E.
Proof.
move=> hU hne.
have [mulS [invS [eS hS]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have htheta := @orthogonal_projection_probability_specification R n m hmn mulS invS eS hS.
have [nu [hnu hrep hm _]] := normalised_invariant_measure_integral htheta.
have hc := @orthogonal_projections_compact R _ _ _ _
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) n (@coordinate_basis R n)
  (@coordinate_basisP R m) (@coordinate_basisP R n) mulS invS eS hS.
apply: (positive_integral_open_positive
  (@metric_hausdorff R (orthogonal_projection_metric_space R n m))
  (compact_space_locally_compact hc) hm hrep _ hU hne).
move=> v hv hv0 hvne.
exact: (nonzero_invariant_integral_positive
  (topological_group_laws (lch_group_topological (orthogonal_group_lch hS)))
  (orthogonal_projections_homogeneous (@euclidean_inner_productP R m)
    (@coordinate_basisP R m) hS) hnu hv hv0 hvne).
Qed.
