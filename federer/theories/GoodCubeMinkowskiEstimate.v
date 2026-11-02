(** Federer (1969), 3.2.38, pp. 274--275: combine the actual
    first-order remainder with the corrected affine Steiner estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm HilbertFormCompactness
  NormDifferentialUP NormDifferentialLipschitzBound EuclideanLinearJacobian LipschitzUP
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanUniformRemainderPoints
  DifferentialCubeTubeInclusion AffineCubeSteinerEstimate MetricOpenThickening
  MinkowskiContents MinkowskiContentsBasic EuclideanLebesgueDimensions EuclideanBallVolume
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [good_coordinate_cube_minkowski_estimate]: the actual
    good-cube estimate in Federer 3.2.38, pp. 274--275, before
    the scalar mean or compact-core integral comparison. A genuine
    differential at a good point supplies both its Lipschitz norm
    bound and its exact Jacobian. The full affine polynomial keeps
    j=0. The uniform xi depends only on n,m,L, and the source cube,
    original global map and positive radius remain actual objects.
    No selected derivative field or affine tube estimate is assumed. *)
Theorem good_coordinate_cube_minkowski_estimate (R:realType) m n (hmn:(m<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (J:inner_metric_space (@euclidean_inner_productP R m)->R) (L:R):
  is_metric_lipschitz_bound setT f L ->
  (forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
    J x=euclidean_linear_jacobian m D) ->
  exists xi:R,0<=xi /\forall v:nat,forall (r d:R) (corner a:R_n R m)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m))),
    (0<v)%N ->0<r ->is_euclidean_coordinate_cube corner (v%:R*r) Q ->Q a ->
    euclidean_uniform_remainder_points f (((v%:R:R)^-1)^+2) d a ->
    m%:R*(v%:R*r)<d ->
    (minkowski_tube_quotient m (f @` Q) r<=((J a+xi/v%:R)*(v%:R*r)^+m)%R%:E)%E.
Proof.
move=>hLip hActual.
have [xi [hXi hAffine]]:=@affine_coordinate_cube_steiner_estimate R m n hmn L hLip.1.
exists xi; split=>// v r d corner a Q hv hr hQ ha [D [hD hRemainder]] hDiameter.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose V:R:=v%:R.
have hV:0<V by rewrite /V ltr0n.
have hV0:V!=0 by rewrite gt_eqF.
have hError:0<=(V^-1)^+2:=sqr_ge0 _.
have hRate x:Q x ->inner_norm (@euclidean_inner_productP R n) (f x-f a-D (x-a))<=
    (V^-1)^+2*inner_norm (@euclidean_inner_productP R m) (x-a).
  move=>hx; apply:hRemainder.
  have hDistance:=coordinate_cube_distance_bound hQ hx ha.
  rewrite inner_metric_distanceE in hDistance.
  exact:le_lt_trans hDistance hDiameter.
have hDN u:inner_norm (@euclidean_inner_productP R n) (D u)<=
    L*inner_norm (@euclidean_inner_productP R m) u.
  apply:(@norm_differential_global_lipschitz_bound R (R_n R m) (R_n R n)
    _ _ (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) f a D L hD).
  move=>x y; exact:hLip.2 x y Logic.I Logic.I.
have hTube:=@differential_coordinate_cube_tube_inclusion R m n corner a (V*r) ((V^-1)^+2) r
  Q f D hQ ha hError hRate.
have hInflation:r+(V^-1)^+2* m%:R*(V*r)=(1+m%:R/V)*r.
  rewrite expr2; field; exact hV0.
rewrite hInflation in hTube.
have hVolume:=@measure_mono R Y (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ hTube.
have hDenominator:=minkowski_tube_denominator_positive n m hr.
have hInverse:(0<=((euclidean_unit_ball_volume R (n-m)*r^+(n-m))%:E)^-1)%E.
  rewrite inver (gt_eqF hDenominator) lee_fin invr_ge0; exact:ltW hDenominator.
have hNormalized:=lee_wpmul2r hInverse hVolume.
apply:le_trans hNormalized _.
rewrite (hActual a D hD).
exact:(hAffine v r corner a (f a) Q D hv hr hQ ha hDN).
Qed.
