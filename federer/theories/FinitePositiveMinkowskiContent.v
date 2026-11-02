(** Federer (1969), 3.2.37, pp. 273--274: finite sources
    have zero positive-dimensional Minkowski contents. This supplies
    the singleton side of the printed failure of countable additivity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBallVolume
  MinkowskiContents MinkowskiContentsBasic FinitePointTubeVolume
  PositiveRadiusPowerLimit PositiveRadiusEventualCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_tube_power_normalization]: supporting
    cancellation of the positive normalizing factor in Federer
    3.2.37, p. 273. The numerator's exact ambient power splits
    into tangential and normal powers; no zero radius is cancelled. *)
Lemma finite_tube_power_normalization (R:realType) (a b r:R) l m:
  (0<b)%R ->(0<r)%R ->
  (a*r^+(l+m))%:E/(b*r^+l)%:E=(a/b*r^+m)%:E.
Proof.
move=>hb hr.
have hDen:(0<b*r^+l)%R:=mulr_gt0 hb (exprn_gt0 _ hr).
rewrite inver (gt_eqF hDen) -EFinM exprD invfM.
have hAlgebra:(a*(r^+l*r^+m)*(b^-1*(r^+l)^-1))%R=
    ((a/b*r^+m)*(r^+l*(r^+l)^-1))%R by ring.
rewrite hAlgebra mulfV ?mulr1 //.
by rewrite (gt_eqF (exprn_gt0 l hr)).
Qed.

(** Source for [finite_positive_minkowski_contents]: supporting
    finite-source computation for Federer 3.2.37, pp. 273--274.
    Every positive admissible natural degree gives both actual
    contents zero, while the separate degree-zero theorem retains
    every positive point atom. *)
Theorem finite_positive_minkowski_contents (R:realType) n m
    (B:{fset inner_metric_space (@euclidean_inner_productP R n)}):
  (0<m)%N ->(m<=n)%N ->
  upper_minkowski_content m [set` B]=0 /\
  lower_minkowski_content m [set` B]=0.
Proof.
move=>hm hmn.
have [e [he hTube]]:=finite_point_tube_volume (R:=R) B.
pose c:=(#|` B|%:R*euclidean_unit_ball_volume R n/
  euclidean_unit_ball_volume R (n-m))%R.
have hc:(0<=c)%R.
  rewrite /c; apply:divr_ge0; last exact:ltW (euclidean_unit_ball_volumeE R (n-m)).2.
  exact:mulr_ge0 (ler0n R _) (ltW (euclidean_unit_ball_volumeE R n).2).
have hQuotient r:(0<r<e)%R ->minkowski_tube_quotient m [set` B] r=(c*r^+m)%:E.
  move=>hr; rewrite /minkowski_tube_quotient (hTube r hr).
  have hDim:(n-m+m=n)%N by rewrite subnK.
  have hExponent:(r^+n=r^+(n-m+m))%R by rewrite hDim.
  rewrite hExponent.
  have hA:(#|` B|%:R*(euclidean_unit_ball_volume R n*r^+(n-m+m)))%R=
      ((#|` B|%:R*euclidean_unit_ball_volume R n)*r^+(n-m+m))%R by ring.
  rewrite hA; exact:finite_tube_power_normalization
    (euclidean_unit_ball_volumeE R (n-m)).2 (andP hr).1.
have [hu hl]:=positive_radius_limits_eventual_congr he hQuotient.
rewrite /upper_minkowski_content /lower_minkowski_content hu hl.
exact:positive_radius_natural_power_limit hc hm.
Qed.
