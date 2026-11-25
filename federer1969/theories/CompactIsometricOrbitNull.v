(** Federer (1969), 3.4.8(6),(8), pp. 329–330:
    an actual compact transitive isometric
    action carries Hausdorff-null sets to
    Haar-null orbit preimages. Apply the
    existing invariant-orbit measure theorem and
    Haar normalization independence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws
  HaarIntegralUP CompactGroupHaarNormalisation CompactMetricInvariantOrbitMeasure
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffIsometryMeasurability MeasureScaleIntegral MeasurePushforward
  HaarMeasureNullComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_transitive_isometric_orbit_null]:
    the original sphere-to-Haar nullity passage
    in 3.4.8(8), p. 330, with its
    invariant-measure argument already proved in
    2.7.11 and 3.3.4. This supporting
    connection retains arbitrary null subsets
    and every original Haar normalization. *)
Theorem compact_transitive_isometric_orbit_null (R:realType) (G:topologicalType) (X:metricType R)
  (mul:G->G->G) (inv:G->G) (unit:G) (A:G->X->X)
  (hG:is_locally_compact_hausdorff_group mul inv unit) (hA:is_homogeneous_space mul A)
  d (C:R) (mu:set G->\bar R) (u:X) (D:set X):
  compact (@setT G) ->0<C ->@hausdorff_measure R X d setT = C%:E ->
  (forall g x y,mdist (A g x) (A g y) = mdist x y) ->
  is_left_haar_measure mul mu ->@hausdorff_measure R X d D = 0%:E ->
  mu ((orbit_map A u) @^-1` D) = 0%:E.
Proof.
move=>hCompact hPositive hMass hDistance hMu hNull.
have hGroup:=topological_group_laws (lch_group_topological hG).
have hInvariant g:measure_pushforward (A g) (@hausdorff_measure R X d) = @hausdorff_measure R X d.
  exact:(@hausdorff_bijective_isometry_pushforward R X X (A g) (A (inv g))
    (homogeneous_translation_inverse_left hGroup hA g)
    (homogeneous_translation_inverse_right hGroup hA g) (hDistance g) d).
have [theta hTheta]:=@normalised_haar_measure_exists R G mul inv unit hG hCompact.
have hComparison:=@compact_metric_finite_invariant_orbit_measure R G X mul inv unit A hG hA
  (@hausdorff_measure R X d) theta C u hCompact (@hausdorff_measure_is_measure R X d)
  (@hausdorff_measure_borel_regular R X d) hPositive hMass hInvariant hTheta.
pose rho:=measure_pushforward (orbit_map A u) theta.
have hInverse:measure_scale C^-1 (@hausdorff_measure R X d) = rho.
  rewrite hComparison;exact:(measure_scale_inverse rho hPositive).
have hThetaNull:theta ((orbit_map A u) @^-1` D) = 0%:E.
  change (rho D = 0%:E);by rewrite -hInverse /measure_scale hNull mule0.
exact:((left_haar_measures_same_null_sets hG hMu hTheta.1 _).2 hThetaNull).
Qed.
