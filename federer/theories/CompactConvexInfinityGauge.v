(** Federer (1969), 2.10.5(2), p. 173, supporting compact-convex
    infinity-gauge identity for the closed generator comparison. The proved
    lower continuity gives open strict superlevels; full support of the
    actual theta-star then identifies essential supremum with supremum. Beta
    at infinity is one. No joint Hausdorff- space continuity theorem or
    Steiner formula is assumed. Source context and the local geometric
    argument: CompactConvexProjectedVolumeLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  ProjectedVolumeGauge OrthogonalProjectionProbability NonnegativeExtendedExponentNormUP
  NonnegativeExtendedExponentNorm NonnegativeExtendedEssentialBounds ProjectionProbabilitySupport
  ExtendedRealBoundsUP IntegralGeometricGauge ProjectionBeta BorelClosedProjection TopologicalBorel
  CompactConvexProjectedVolumeLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_infinity_compact_convex]:
    supporting equality of the infinity integral-
    geometric gauge and the projection-volume
    supremum on compact convex generators in
    Federer 2.10.5(2), p. 173. Empty sets and
    zero-dimensional auxiliary interfaces are included. *)
Theorem integral_geometric_gauge_infinity_compact_convex (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact S -> @InnerConvex.is_inner_convex R (R_n R n) S ->
  @integral_geometric_gauge R n m hmn +oo S=projected_volume_gauge m S.
Proof.
move=> hK hc.
pose P := euclidean_projection_space R n m.
pose f : P -> _ := projected_volume_function (m:=m) S.
pose theta := @orthogonal_projection_probability R n m hmn.
pose a := nonnegative_extended_exponent_norm theta f +oo.
have hsus := @metric_borel_suslin R (inner_metric_space (@euclidean_inner_productP R n))
  S (closed_borel_set (compact_closed (@metric_hausdorff R
    (inner_metric_space (@euclidean_inner_productP R n))) hK)).
have hn := @nonnegative_extended_exponent_norm_specification R _ theta f +oo
  (@theta_star_is_measure R n m hmn) (fun p => projected_volume_function_nonnegative S p)
  (leey 1) (@theta_star_projected_volume_measurable R n m hmn S hsus).
have [p hp] := @euclidean_projection_exists R n m hmn.
have [q hq] := @euclidean_projection_linear_complete R n m p hp.
have hsup := @nonnegative_extended_essential_supremum R P theta
  (@theta_star_is_measure R n m hmn) f a (ex_intro _ q I)
  (fun p => projected_volume_function_nonnegative S p)
  (fun b => @compact_convex_projected_volume_open_superlevel R n m S b hK hc)
  (fun U => @theta_star_nonempty_open_positive R n m hmn U) hn.
rewrite /integral_geometric_gauge projection_beta_infinity invr1 mul1e.
change (a=projected_volume_gauge m S).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (extended_real_supremum_least hsup)=> b [r _ <-].
  exact: (@projected_volume_gauge_projection_bound R n m S (euclidean_projection_linear r)
    (euclidean_projection_linear_member r)).
- apply: projected_volume_gauge_least_bound=> r hr.
  have [s hs] := @euclidean_projection_linear_complete R n m r hr.
  have he : euclidean_projection_linear s @` S=r @` S.
    apply/seteqP; split=> y.
    - move=> [x hx <-]; exists x=> //; exact: esym (hs x).
    - move=> [x hx <-]; exists x=> //; exact: hs x.
  have hh : f s<=a by apply: (extended_real_supremum_upper hsup); by exists s.
  by rewrite /f /projected_volume_function he in hh.
Qed.
