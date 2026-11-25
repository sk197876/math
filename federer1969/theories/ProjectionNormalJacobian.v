(** Unit normal Jacobian of an orthogonal projection, supporting Federer
    (1969), 2.10.16, p. 178. Its adjoint is an isometry by 1.7.4, p. 30, and
    preserves the unit top-vector norm by 1.7.5, p. 32. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectionNormalVector EuclideanNormalJacobian ExteriorDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_projection_normal_jacobian_unit]:
    supporting normal-Jacobian normalization for 2.10.16,
    p. 178, directly from the exterior isometry law
    of 1.7.5, p. 32. Degree zero is included. *)
Lemma euclidean_projection_normal_jacobian_unit (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) :
  euclidean_normal_jacobian (euclidean_projection_linear p)= 1.
Proof.
rewrite (@euclidean_normal_jacobian_unit_value R n m (euclidean_projection_linear p)
  (@top_vector R m (R_n R m) (@coordinate_basis R m)) (@euclidean_coordinate_top_vector_unit R m)).
exact: projection_normal_vector_unit.
Qed.
