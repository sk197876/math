(** Federer (1969), 3.2.37, p. 274: every orthogonal
    projection volume is at most the lower Minkowski content.
    Take liminf only after proving the whole positive-radius
    outer-volume bound; arbitrary sources and infinities remain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume MinkowskiContents MinkowskiContentsBasic
  EuclideanProjectionTubeLower CoordinateProjection PositiveRadiusLowerApproximation
  ProjectedVolumeGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_tube_projection_bound_blocks]: the whole
    positive-radius Fubini estimate underlying Federer 3.2.37,
    p. 274, in normal and projected coordinate blocks. *)
Lemma minkowski_tube_projection_bound_blocks (R:realType) l m
    (p:{linear R_n R (l+m)->R_n R m})
    (S:set (inner_metric_space (@euclidean_inner_productP R (l+m)))) (r:R):
  O_star p ->(0<r)%R ->@euclidean_lebesgue_measure R m (p @` S)<=
    minkowski_tube_quotient m S r.
Proof.
move=>hp hr.
have hTube:=euclidean_projection_tube_lower_bound S hp hr.
have hPositive:(0<euclidean_unit_ball_volume R l*r^+l)%R.
  apply:mulr_gt0; first exact:(euclidean_unit_ball_volumeE R l).2.
  exact:exprn_gt0 _ hr.
have hReciprocal:0<=(euclidean_unit_ball_volume R l*r^+l)%:E^-1.
  rewrite inve_ge0 lee_fin; exact:ltW hPositive.
have h:=lee_wpmul2l hReciprocal hTube.
rewrite inver (gt_eqF hPositive) muleA -EFinM mulVf ?gt_eqF // mul1e in h.
rewrite /minkowski_tube_quotient addnK inver (gt_eqF hPositive).
by rewrite muleC.
Qed.

(** Source for [minkowski_tube_projection_bound]: supporting whole
    tube estimate for Federer 3.2.37, p. 274, in the printed
    natural dimensions m<=n and at every positive real radius. *)
Theorem minkowski_tube_projection_bound (R:realType) n m
    (p:{linear R_n R n->R_n R m})
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  (m<=n)%N ->O_star p ->(0<r)%R ->
  @euclidean_lebesgue_measure R m (p @` S)<=minkowski_tube_quotient m S r.
Proof.
move=>hmn.
have [l hn]:exists l,n=(l+m)%N by exists (n-m)%N; rewrite subnK.
move: p S; rewrite hn=>p S hp hr.
exact:minkowski_tube_projection_bound_blocks hp hr.
Qed.

(** Source for [lower_minkowski_projection_bound]: the printed
    inequality in Federer 3.2.37, p. 274, for every natural
    0<=m<=n and every original source subset S. *)
Theorem lower_minkowski_projection_bound (R:realType) n m
    (p:{linear R_n R n->R_n R m})
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->O_star p ->
  @euclidean_lebesgue_measure R m (p @` S)<=lower_minkowski_content m S.
Proof.
move=>hmn hp; apply:(@positive_radius_lower_eventual_bound R
  (minkowski_tube_quotient m S) _ 1%R ltr01)=>r /andP[hr _].
exact:minkowski_tube_projection_bound hmn hp hr.
Qed.

(** Source for [projected_volume_gauge_lower_minkowski_bound]:
    supporting supremum version of the first inequality in
    Federer 3.2.37, p. 274. No maximizing projection is assumed. *)
Corollary projected_volume_gauge_lower_minkowski_bound (R:realType) n m
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->projected_volume_gauge m S<=lower_minkowski_content m S.
Proof. move=>hmn; apply:projected_volume_gauge_least_bound=>p hp.
exact:lower_minkowski_projection_bound hmn hp. Qed.
