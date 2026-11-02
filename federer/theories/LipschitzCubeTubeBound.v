(** Federer (1969), 3.2.38, p. 275: the bad source cubes H
    have a uniform normalized tube-volume bound from the actual global
    Lipschitz estimate and the actual Euclidean ball volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerNormedTopology
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry
  MetricOpenThickening MinkowskiContents LipschitzUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_coordinate_cube_tube_volume_bound]: supporting
    the bound on rho(K) for K in H, Federer 3.2.38, p. 275.
    The actual image tube lies in one open ball about the image of
    the cube's lower corner. Zero Lipschitz bound, dimension zero
    and degenerate source cubes are retained; no distance function
    for an empty image is silently used. *)
Lemma lipschitz_coordinate_cube_tube_volume_bound (R:realType) m n
    (a:R_n R m) (h r L:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m)))
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_euclidean_coordinate_cube a h Q ->0<r ->0<=L ->is_metric_lipschitz_bound setT f L ->
  (@euclidean_lebesgue_measure R n (metric_open_thickening (f @` Q) r)<=
    (euclidean_unit_ball_volume R n*(r+L* m%:R*h)^+n)%:E)%E.
Proof.
move=>hQ hr hL hLip.
have ha:Q a by apply:(hQ.2 a).2=>i; rewrite lexx /= lerDl; exact:hQ.1.
have hRadius:0<r+L* m%:R*h.
  have hNonnegative:0<=L* m%:R*h.
    exact:mulr_ge0 (mulr_ge0 hL (ler0n R m)) hQ.1.
  have hIncrease:r<=r+L* m%:R*h by rewrite lerDl.
  exact:lt_le_trans hr hIncrease.
have hSubset:metric_open_thickening (f @` Q) r `<=`
    [set z:inner_metric_space (@euclidean_inner_productP R n) | `|z-f a|<r+L* m%:R*h].
  move=>z [y [x hx <-] hy].
  have hDistance:=coordinate_cube_distance_bound hQ ha hx.
  have hMap:=hLip.2 a x Logic.I Logic.I.
  have hBound:=ler_wpM2l hL hDistance.
  have hTriangle:=metric_triangle (f a) (f x) z.
  change (is_true (`|z-f a|<r+L* m%:R*h)).
  rewrite -inner_metric_normE; change (is_true (mdist (f x) z<r)) in hy.
  rewrite mulrA in hBound; lra.
have hVolume:=@measure_mono R _ (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ hSubset.
by rewrite (@euclidean_ball_measure R n (f a) (r+L* m%:R*h) hRadius) in hVolume.
Qed.

