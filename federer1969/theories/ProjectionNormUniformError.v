(** Federer (1969), 3.2.26(3), p. 262: replacing
    a simple unit tangent vector by a nearby fixed vector
    changes every projection norm by at most that distance.
    This is the contraction law of 1.7.7, p. 34. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerNorm InnerMetric
  HilbertFormCompactness InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorNorm ExteriorMaps
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionConstants
  RealNormUP NormMetricContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_norm_difference_bound]: the projection
    error estimate in 3.2.26(3), p. 262. The
    reverse triangle inequality followed by exterior projection
    contraction bounds the difference of the two real norms.
    Simplicity and unit length are unnecessary for this step. *)
Lemma projection_norm_difference_bound (R:realType) m n
    (xi eta:exterior_power (R_n R n) m) (p:orthogonal_projection_metric_space R n m):
  projection_norm (euclidean_two_nonzero R) xi p-projection_norm (euclidean_two_nonzero R) eta p<=
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (xi-eta).
Proof.
pose L:=exterior_power_map (euclidean_projection_linear p) m.
pose N (x:exterior_power (R_n R m) m):R:=
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) x.
have hN:is_real_norm N:=inner_norm_real_norm (@exterior_inner_productP R (euclidean_two_nonzero R)
  (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m).
have hDifference:=@real_norm_difference_bound R (exterior_power (R_n R m) m) N hN (L xi) (L eta).
rewrite -linearB in hDifference.
have hContraction:=projection_norm_bound (euclidean_two_nonzero R) (xi-eta) p.
exact:(le_trans hDifference hContraction).
Qed.

(** Source for [projection_norm_nearby_lower]: the integrand
    inequality used before the last norm bound in 3.2.26(3),
    p. 262. If T(w) is within delta of xi,
    every projection norm of T(w) is at least the
    projection norm of xi minus delta. *)
Lemma projection_norm_nearby_lower (R:realType) m n
    (xi eta:exterior_power (R_n R n) m) (p:orthogonal_projection_metric_space R n m) (d:R):
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (eta-xi)<=d ->
  projection_norm (euclidean_two_nonzero R) xi p-d<=projection_norm (euclidean_two_nonzero R) eta p.
Proof.
move=>hDistance.
have hDifference:=projection_norm_difference_bound xi eta p.
have hN:=inner_norm_real_norm (@exterior_inner_productP R (euclidean_two_nonzero R)
  (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).
rewrite /exterior_norm (real_seminorm_subtract hN.1) in hDifference.
rewrite /exterior_norm in hDistance.
lra.
Qed.
