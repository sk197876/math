(** Existence witness for the normalized projection probability used in
    Federer (1969), 2.10.5, p. 172. Reuse the proved existence and
    uniqueness in 2.7.16(6), p. 139, and the independence of its action from
    restricted group operations. This witness is hidden by a seal. Source
    context: OrthogonalProjectionProbabilityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct FiniteCoordinates
  EuclideanOrthogonalInvariantMeasures EuclideanProjectionMetric
  OrthogonalGroupTopology OrthogonalInjectionSpaces OrthogonalProjectionConstants
  OrthogonalProjectionProbabilityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_projection_probability_exists]:
    existence in Federer 2.7.16(6), p. 139,
    supplying the actual theta* used in 2.10.5,
    p. 172. The sole dimension premise m<=n
    ensures the projection space is nonempty. *)
Theorem orthogonal_projection_probability_exists (R : realType) (n m : nat) :
  (m<=n)%N -> exists theta : set (orthogonal_projection_metric_space R n m) -> \bar R,
    is_orthogonal_projection_probability theta.
Proof.
move=> hmn.
have [mulS0 [invS0 [eS0 hS0]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [theta [htheta _ _]] := euclidean_theta_star_nm_exists_unique hS0 hmn.
exists theta=> mulS invS eS hS.
have he : orthogonal_projection_action (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS =
  orthogonal_projection_action (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS0.
  exact: orthogonal_projection_action_independent.
by rewrite he.
Qed.
