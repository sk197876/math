(** Federer (1969), 3.2.26(2), p. 261: choose
    thin convex neighbourhoods of the unit tangent disc
    with integral-geometric cost arbitrarily close to alpha(m).
    Expand the compact approximation separately at finite
    exponent and infinity, without using later 3.2.36. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric OrthogonalMaps MetricClosedBalls MetricDiameterUP MetricDiameter
  InnerConvex InnerClosedBallConvex OrthogonalDiscGeometricGauge EuclideanBallVolume
  IntegralGeometricGauge IntegralGeometricFiniteEnlargement IntegralGeometricInfinity
  CompactConvexInfinityGauge ProjectedVolumeGauge ProjectedVolumeOpenEnlargement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linear_closed_ball_convex]: the convex
    unit tangent disc in 3.2.26(2), p. 261.
    Linear images preserve the defining segment laws;
    this supporting fact also allows a singular map. *)
Lemma linear_closed_ball_convex (R:realType) m n
    (f:{linear R_n R m->R_n R n}):
  @is_inner_convex R (R_n R n)
    (f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R)).
Proof.
move=>x y [u hu <-] [v hv <-] s hs0 hs1.
exists (((1-s)*:u+s*:v)%R).
- exact:(@inner_metric_closed_ball_convex R (R_n R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) (0%R:R_n R m) 1%R u v hu hv s hs0 hs1).
- by rewrite linearD !linearZ.
Qed.

(** Source for [orthogonal_unit_disc_diameter_bound]: the
    unit tangent disc in 3.2.26(2), p. 261,
    has diameter at most two. This bound suffices
    for a neighbourhood of diameter at most three,
    and remains valid when the source is zero-dimensional. *)
Lemma orthogonal_unit_disc_diameter_bound (R:realType) m n
    (f:{linear R_n R m->R_n R n}):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) f ->
  @extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n))
    (f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R))<=2%:E.
Proof.
move=>hF; apply:(metric_diameter_least (extended_metric_diameter_specification _)).
- by rewrite lee_fin ler0n.
- move=>x y [u hu <-] [v hv <-].
  rewrite lee_fin !inner_metric_distanceE -linearB
    (orthogonal_map_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) hF).
  have hBound:=@metric_closed_ball_diameter_bound R (inner_metric_space (@euclidean_inner_productP R m))
    (0%R:R_n R m) 1%R u v hu hv.
  rewrite inner_metric_distanceE in hBound; exact hBound.
Qed.

(** Source for [orthogonal_disc_near_optimal_convex_neighbourhood]:
    the limiting thin-cover cost choice in 3.2.26(2),
    p. 261. Use compact convex open approximation with
    the already proved unit-disc normalization. The neighbourhood
    may depend on the tangent plane: pointwise Vitali fineness
    does not require a uniformly chosen thickness or any
    unproved rotation-invariance formula. *)
Theorem orthogonal_disc_near_optimal_convex_neighbourhood (R:realType) m n
    (hmn:(m<=n)%N) (f:{linear R_n R m->R_n R n}) (t: \bar R) (d:R):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) f ->
  1<=t ->(0<d)%R ->
  exists U:set (inner_metric_space (@euclidean_inner_productP R n)),
    open U /\@is_inner_convex R (R_n R n) U /\
    f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R) `<=` U /\
    extended_metric_diameter U<=3%:E /\
    @integral_geometric_gauge R n m hmn t U<=((1+d)*euclidean_unit_ball_volume R m)%R%:E.
Proof.
move=>hF ht hd.
pose K:=f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R).
pose b:R:=((1+d)*euclidean_unit_ball_volume R m)%R.
have hCompact:=orthogonal_unit_disc_compact hF.
have hConvex:=@linear_closed_ball_convex R m n f.
have hDiam:=orthogonal_unit_disc_diameter_bound hF.
have hGap:(euclidean_unit_ball_volume R m<b)%R.
  have hAlpha:=(euclidean_unit_ball_volumeE R m).2.
  rewrite /b; nra.
have hTwo:(0<=(2:R))%R by rewrite ler0n.
have hTwoThree:(2<(3:R))%R by rewrite ltr_nat.
have hCost:@integral_geometric_gauge R n m hmn t K<b%:E.
  rewrite (@orthogonal_unit_disc_integral_geometric_gauge R m n hmn f t hF ht) lte_fin.
  exact hGap.
case:t ht hCost=>[p| |] ht hCost; last by [].
- exact:(@integral_geometric_finite_convex_open_enlargement R n m hmn K p 2 3 b
    hCompact hConvex ht hTwo hTwoThree hDiam hCost).
- have hProjected:projected_volume_gauge m K<b%:E.
    by rewrite -(@integral_geometric_gauge_infinity_compact_convex R n m hmn K hCompact hConvex).
  have [U [hOpen [hConv [hKU [hDU hGauge]]]]]:=@projected_volume_convex_open_enlargement
    R n m K 2 3 b hCompact hConvex hTwo hTwoThree hDiam hProjected.
  exists U; split; first exact hOpen; split; first exact hConv; split; first exact hKU.
  split; first exact hDU.
  by rewrite (@integral_geometric_gauge_infinity_open R n m hmn U hOpen).
Qed.
