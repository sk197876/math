(** Federer (1969), 3.2.36, p. 272:
    a common source norm bound controls
    projected-volume errors uniformly in the projection. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability EuclideanProjectionConvexImage
  CompactSetDistanceProfile CompactHausdorffMetric CompactEuclideanProjectionImage HausdorffLipschitzImage
  CompactConvexCommonNormVolumeBound EuclideanLebesgueDimensions EuclideanBallVolume LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_projected_volume_uniform_error]:
    supporting intrinsic-volume continuity in
    Federer 3.2.36, p. 272.
    A common norm bound for two compact
    convex sources bounds every actual projected
    volume difference by the same small-radius
    error. Projection nonexpansion proves both
    the target norm bound and Hausdorff image
    control. Every compact image witness is
    proved locally; no projection-dependent
    regularity or volume bound is assumed. *)
Theorem compact_convex_projected_volume_uniform_error (R:realType) n m
    (A B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))) (c r:R):
  is_inner_convex (val A) ->is_inner_convex (val B) ->0<=c ->
  (forall x,val A x ->inner_norm (@euclidean_inner_productP R n) x<=c) ->
  (forall x,val B x ->inner_norm (@euclidean_inner_productP R n) x<=c) ->
  0<r ->r<=1 ->mdist A B<r ->forall p:euclidean_projection_space R n m,
  `|fine (projected_volume_function (val A) p)-fine (projected_volume_function (val B) p)|<=
    r*(euclidean_unit_ball_volume R m*(c+1)^+m).
Proof.
move=>hA hB hc hNormA hNormB hr hr1 hAB p.
have [P hP]:=compact_euclidean_projection_image_exists p A.
have [Q hQ]:=compact_euclidean_projection_image_exists p B.
have hPConvex:is_inner_convex (val P).
  rewrite hP; exact:euclidean_projection_convex_image hA.
have hQConvex:is_inner_convex (val Q).
  rewrite hQ; exact:euclidean_projection_convex_image hB.
have hNorm (S:set (inner_metric_space (@euclidean_inner_productP R n))):
    (forall x,S x ->inner_norm (@euclidean_inner_productP R n) x<=c) ->
    forall y,(euclidean_projection_linear p @` S) y ->inner_norm (@euclidean_inner_productP R m) y<=c.
  move=>hS y [x hx <-].
  have hContraction:=@euclidean_projection_nonexpanding R n m p x
    (0%R:inner_metric_space (@euclidean_inner_productP R n)).
  rewrite linear0 !inner_metric_distanceE !subr0 in hContraction.
  exact:le_trans hContraction (hS x hx).
have hNormP y:val P y ->inner_norm (@euclidean_inner_productP R m) y<=c.
  rewrite hP; exact:hNorm hNormA y.
have hNormQ y:val Q y ->inner_norm (@euclidean_inner_productP R m) y<=c.
  rewrite hQ; exact:hNorm hNormB y.
have hLipschitz:@is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R m)) setT (euclidean_projection_linear p) 1.
  split; first exact:ler01.
  move=>x y _ _; rewrite mul1r; exact:euclidean_projection_nonexpanding.
have hImages:=@compact_hausdorff_lipschitz_image_bound R
  (inner_metric_space (@euclidean_inner_productP R n))
  (inner_metric_space (@euclidean_inner_productP R m)) (euclidean_projection_linear p) 1 A B P Q
  hLipschitz hP hQ.
rewrite mul1r in hImages.
have hMass:=@compact_convex_common_norm_volume_bound R m P Q c r hPConvex hQConvex hc
  hNormP hNormQ hr hr1 (le_lt_trans hImages hAB).
have hPValue:euclidean_lebesgue_measure m (val P)=projected_volume_function (val A) p by rewrite hP.
have hQValue:euclidean_lebesgue_measure m (val Q)=projected_volume_function (val B) p by rewrite hQ.
by rewrite hPValue hQValue in hMass.
Qed.
