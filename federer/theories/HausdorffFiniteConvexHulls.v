(** Federer (1969), 2.10.21, p. 184, final statement: hulls of nonempty
    finite sets are dense in the nonempty compact convex sets. Follow finite
    approximation by the one-Lipschitz convex-hull map. Apply the erratum p.
    3, book p. 184 lines 8 and 10, so the ambient convex sets in this
    assertion are explicitly compact and nonempty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric InnerConvex ConvexHullUP ConvexHull LinearBasis
  CompactSetDistanceProfile CompactHausdorffMetric HausdorffDistance HausdorffFiniteNets
  HausdorffConvexHulls FiniteNormBoundedCompact CompactBallProfiles ConvexProfileClosed
  MetricClosedBalls LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_finite_convex_hull]: direct finite
    hull family of 2.10.21, p. 184, with
    a nonempty finite generating set. *)
Definition is_finite_convex_hull (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (C : compact_metric_set (real_norm_metric_space hN)) :=
  exists D : set V, finite_set D /\ D !=set0 /\ val C=@convex_hull R V D.

(** Source for [finite_convex_hulls_dense]: direct
    final density assertion of 2.10.21, p. 184,
    in the corrected nonempty compact convex scope.
    Arbitrary finite-dimensional norms and dimension zero are retained. *)
Theorem finite_convex_hulls_dense (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) d (e : 'I_d -> V) (he : is_basis e)
    (C : compact_hausdorff_space (real_norm_metric_space hN)) :
  is_inner_convex (val C) ->
  closure [set D : compact_hausdorff_space (real_norm_metric_space hN) |
    is_inner_convex (val D) /\ is_finite_convex_hull D] C.
Proof.
move=> hC W hW.
have [eps heps hball] := (metricType_numDomainType.nbhs_mdistP C W).1 hW.
have heps2 : 0<eps/2 by rewrite divr_gt0 // ltr0n.
have [D [hfin [hDC hdist]]] := compact_hausdorff_finite_approximation C heps2.
pose E := finite_norm_hull he D.
have hCh : finite_norm_hull he C=C.
  apply: val_inj; apply/seteqP; split.
  - exact: (@convex_hull_least R V (val C) (val C) (fun x hx=>hx) hC).
  - exact: (@convex_hull_includes R V (val C)).
have hbound := finite_norm_hull_hausdorff_lipschitz he C D.
rewrite hCh in hbound.
exists (E : compact_hausdorff_space (real_norm_metric_space hN)); split.
- split; first exact: (@convex_hull_convex R V (val D)).
  exists (val D); split=> //; split; first exact: (set_valP D).2; by [].
- apply: hball; change (is_true (hausdorff_distance C E<eps)).
  apply: le_lt_trans (le_trans hbound hdist) _.
  by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
Qed.

(** Source for [federer_2_10_21_compact_convex]: direct
    compactness of convex members of F_(a,r),
    2.10.21, p. 184, with the printed
    finite-dimensional normed-space hypothesis. *)
Theorem federer_2_10_21_compact_convex (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) d (e : 'I_d -> V) (he : is_basis e)
    (a : V) (r : R) : 0<r ->
  compact [set C : compact_hausdorff_space (real_norm_metric_space hN) |
    is_inner_convex (val C) /\ @compact_sets_in_ball R (real_norm_metric_space hN) a r C].
Proof.
move=> hr; exact: compact_convex_sets_in_ball_compact
  (@finite_norm_metric_boundedly_compact R V N hN d e he) (ltW hr).
Qed.
