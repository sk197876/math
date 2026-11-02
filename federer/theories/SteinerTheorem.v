(** Federer (1969), 2.10.30, p. 195: Steiner symmetrisation of bounded
    Euclidean sets, its compactness and volume, convexity, reflection, and
    containing-ball boundary properties. The operation is specified by
    normal-line laws and supplied through an opaque existence interface.
    Source context: SteinerSymmetrisationUP.v, SteinerVolume.v and
    SteinerBoundary.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm
  InnerConvex CoveringFamilyUP MetricClosedBalls UnitNormalGeometry OrthogonalMaps
  SteinerSymmetrisationUP SteinerSymmetrisation SteinerSymmetrisationLaws SteinerNormalLines
  SteinerCompact SteinerConvex SteinerVolume SteinerBallBounds SteinerBoundary EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_30]: direct collected
    assertions of 2.10.30, p. 195. A unit
    normal represents its orthogonal hyperplane. The
    positive-dimensional setting is enforced by the
    existence of that normal, without a fictitious
    zero-dimensional direction. Empty sources, null
    nonempty line sections and radius-zero balls
    retain the separately proved conventions. *)
Theorem federer_2_10_30 (R : realType) n
    (u : inner_metric_space (@euclidean_inner_productP R n))
    (hu : euclidean_inner_product u u= 1)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (hb : metric_set_bounded S) :
  let hB := @euclidean_inner_productP R n in
  let T : set (inner_metric_space hB) := steiner_symmetrisation hB hu hb in
  is_steiner_symmetrisation hB u S T /\
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n)
    (GRing.Linear.clone _ _ _ _ (normal_reflection hB u) _) /\
  normal_reflection hB u @` T=T /\
  (compact S -> compact T /\ euclidean_lebesgue_measure n S=euclidean_lebesgue_measure n T) /\
  (is_inner_convex S -> is_inner_convex T) /\
  forall r : R, 0<=r -> compact S -> S `<=` metric_closed_ball (0 : inner_metric_space hB) r ->
    T `<=` metric_closed_ball (0 : inner_metric_space hB) r /\
    let C := metric_closed_ball (0 : inner_metric_space hB) r in
    let Z := closure C `\` interior C in
    (Z `\` S) `|` (normal_reflection hB u @` (Z `\` S)) `<=` Z `\` T.
Proof.
move=> hB T.
have hT : is_steiner_symmetrisation hB u S T := steiner_symmetrisation_specification hB hu hb.
split=> //; split; first exact (@normal_reflection_orthogonal R (R_n R n)
  (@euclidean_inner_product R n) hB u hu).
split; first exact (steiner_reflection_image hT).
split.
- move=> hS; split.
  + exact (steiner_preserves_compactness hT hS).
  + exact (steiner_preserves_euclidean_volume hT hS).
split.
- move=> hc; exact (steiner_preserves_convexity hT hb hc).
- move=> r hr hS hball; split.
  + have hnorm z : S z -> inner_norm hB z<=r.
      move=> hz; move: (hball z hz).
      by rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
    move=> x hx; have hh := steiner_preserves_centered_ball hT hr hnorm hx.
    by rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
  + exact (steiner_closed_ball_boundary_exclusion hT hS hr hball).
Qed.
