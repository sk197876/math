(** Federer (1969), 3.2.38, p. 275: normalization of the
    actual bad-cube tube estimate by the normal-ball volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume EuclideanCoordinateCubeUP MetricOpenThickening MinkowskiContents MinkowskiContentsBasic
  LipschitzUP LipschitzCubeTubeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_coordinate_cube_normalized_tube_bound]:
    the estimate rho(K) <= eta L^m(K) on side-r bad cubes,
    Federer 3.2.38, p. 275. Actual radius powers cancel only
    after positivity is proved. All admissible natural dimensions,
    singular maps, and the positive degree-zero source atom remain. *)
Lemma lipschitz_coordinate_cube_normalized_tube_bound (R:realType) m n
    (a:R_n R m) (r L:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m)))
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  (m<=n)%N ->is_euclidean_coordinate_cube a r Q ->0<r ->0<=L ->
  is_metric_lipschitz_bound setT f L ->
  (minkowski_tube_quotient m (f @` Q) r<=
    ((euclidean_unit_ball_volume R n*(1+L* m%:R)^+n/
      euclidean_unit_ball_volume R (n-m))*r^+m)%:E)%E.
Proof.
move=>hmn hQ hr hL hLip.
have hVolume:=lipschitz_coordinate_cube_tube_volume_bound hQ hr hL hLip.
have hDenominator:=minkowski_tube_denominator_positive n m hr.
have hNormE:(0<=((euclidean_unit_ball_volume R (n-m)*r^+(n-m))^-1)%:E)%E.
  by rewrite lee_fin invr_ge0; exact:ltW hDenominator.
rewrite /minkowski_tube_quotient inver (gt_eqF hDenominator).
apply:le_trans (lee_wpmul2r hNormE hVolume) _.
rewrite -EFinM lee_fin.
have hRadius:r+L* m%:R*r=(1+L* m%:R)*r by ring.
have hPower:r^+n=r^+m*r^+(n-m) by rewrite -exprD addnC subnK.
have hPowerPositive:0<r^+(n-m):=exprn_gt0 _ hr.
have hPowerNonzero:r^+(n-m)!=0 by rewrite (gt_eqF hPowerPositive).
rewrite hRadius exprMn hPower invfM.
have hRearrange:
    euclidean_unit_ball_volume R n*((1+L* m%:R)^+n*(r^+m*r^+(n-m)))*
      ((euclidean_unit_ball_volume R (n-m))^-1*(r^+(n-m))^-1)=
    (euclidean_unit_ball_volume R n*(1+L* m%:R)^+n/euclidean_unit_ball_volume R (n-m))*r^+m*
      (r^+(n-m)*(r^+(n-m))^-1) by ring.
by rewrite hRearrange mulfV // mulr1.
Qed.
