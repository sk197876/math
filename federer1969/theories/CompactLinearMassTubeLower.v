(** Federer (1969), 3.2.40, p. 276: supporting positive
    lower tube content at the critical Cantor-square exponent.
    Prove the actual finite-net volume comparison before
    applying it to the existing product restriction measure. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume MetricClosedBalls
  MetricOpenThickening MetricOpenThickeningClosure MinkowskiContents
  FiniteSeparatedMetricNetUP FiniteSeparatedPointTube
  FinitePositiveMinkowskiContent FiniteCoverMeasureBounds
  MeasureUP MeasureBasic PositiveRadiusLowerApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_linear_mass_tube_lower_bound]: supporting
    critical lower-content positivity in Federer 3.2.40, p. 276.
    A unit competing measure with actual C*r closed-ball bounds
    forces a uniform positive planar tube quotient. Finite net
    existence, covering and ball separation are proved internally;
    no packing or content inequality is assumed. *)
Lemma compact_linear_mass_tube_lower_bound (R:realType)
    (K:set (inner_metric_space (@euclidean_inner_productP R 2)))
    (nu:set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R) (C r:R):
  compact K ->is_measure nu ->nu K= 1 ->(0<C)%R ->(0<r)%R ->
  (forall x,K x ->forall t:R,(0<t)%R ->nu (metric_closed_ball x t)<=(C*t)%R%:E) ->
  (euclidean_unit_ball_volume R 2/(4*C))%R%:E<=minkowski_tube_quotient 1 K r.
Proof.
move=>hK hNu hMass hC hr hBall.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
have hTwo:(0<(2:R))%R by rewrite ltr0n.
have hTwoR:(0<2*r)%R:=mulr_gt0 hTwo hr.
have [B hNet]:=@compact_finite_separated_metric_net_exists R X (0:X)%R K (2*r)%R hK hTwoR.
have hInside:forall a,a \in B ->K a:=@finite_metric_net_inside R X K (2*r)%R B hNet.
have hSeparated a b:a \in B ->b \in B ->a!=b ->(2*r<=mdist a b)%R.
  move=>ha hb hab; exact:ltW (@finite_metric_net_separated R X K (2*r)%R B hNet a b ha hb hab).
pose N:=size (B:seq X).
pose I:=[the finType of 'I_N].
pose a (i:I):=nth (0:X)%R B i.
have hMember i:a i \in B:=mem_nth (0:X)%R (ltn_ord i).
have hCover:K `<=` \bigcup_(i:I) metric_closed_ball (a i) (2*r)%R.
  move=>x hx.
  have [b hb hbx]:=(@finite_metric_net_covers R X K (2*r)%R B hNet) x hx.
  have hi:(index b (B:seq X)<N)%N by rewrite /N index_mem.
  exists (Ordinal hi:I); first exact Logic.I.
  by rewrite /a /= nth_index.
have hCoverMass:=@measure_finite_indexed_cover R X I nu hNu K
  (fun i=>metric_closed_ball (a i) (2*r)%R) hCover.
have hSum:((\sum_i nu (metric_closed_ball (a i) (2*r)%R))<=
    (\sum_(i:I) (C*(2*r))%R%:E))%E.
  apply:lee_sum=>i _; exact:hBall (a i) (hInside _ (hMember i)) (2*r)%R hTwoR.
have hCoverage:(1<=N%:R*(C*(2*r)))%R.
  have h:=le_trans hCoverMass hSum.
  rewrite hMass sumEFin sumr_const card_ord lee_fin in h.
  change (is_true ((1<=(C*(2*r)) *+ N)%R)) in h.
  by rewrite -(mulr_natl (C*(2*r))%R N) in h.
have hSub:[set` B] `<=` K by move=>x hx; exact:hInside x hx.
have hPacking:=measure_mono (euclidean_lebesgue_is_measure R 2)
  (@metric_open_thickening_monotone R X [set` B] K r hSub).
rewrite (@finite_separated_point_tube_volume R 2 B r hr hSeparated) in hPacking.
have hInverse:0<=((2*r)%R%:E)^-1.
  rewrite inve_ge0 lee_fin; exact:ltW hTwoR.
have hScaled:=lee_wpmul2r hInverse hPacking.
have hNumerator:(#|` B|%:R*(euclidean_unit_ball_volume R 2*r^+2))%R=
    ((N%:R*euclidean_unit_ball_volume R 2)*r^+2)%R by rewrite /N; ring.
have hNormalize:=@finite_tube_power_normalization R
  (N%:R*euclidean_unit_ball_volume R 2)%R 2 r 1 1 hTwo hr.
rewrite !expr1 in hNormalize.
rewrite hNumerator hNormalize in hScaled.
have hQuotient:minkowski_tube_quotient 1 K r=
    @euclidean_lebesgue_measure R 2 (metric_open_thickening K r)/(2*r)%R%:E.
  by rewrite /minkowski_tube_quotient euclidean_unit_ball_volume1 expr1.
rewrite -hQuotient in hScaled.
have hFactor:(0<euclidean_unit_ball_volume R 2/(4*C))%R.
  have hFour:(0<(4:R))%R by rewrite ltr0n.
  have hDenominator:(0<4*C)%R:=mulr_gt0 hFour hC.
  have hAlpha:=(euclidean_unit_ball_volumeE R 2).2.
  by rewrite divr_gt0.
have hComparison:=ler_wpM2l (ltW hFactor) hCoverage.
have hAlgebra:((euclidean_unit_ball_volume R 2/(4*C))*(N%:R*(C*(2*r))))%R=
    ((N%:R*euclidean_unit_ball_volume R 2)/2*r)%R.
  by field; rewrite (gt_eqF hC).
rewrite mulr1 hAlgebra in hComparison.
apply:le_trans _ hScaled; by rewrite lee_fin.
Qed.

(** Source for [compact_linear_mass_lower_minkowski_bound]: supporting
    positive critical lower content in Federer 3.2.40, p. 276.
    The preceding bound holds at every positive radius and hence
    at the full real-radius liminf. Infinite upper contents are
    unrestricted. *)
Corollary compact_linear_mass_lower_minkowski_bound (R:realType)
    (K:set (inner_metric_space (@euclidean_inner_productP R 2)))
    (nu:set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R) (C:R):
  compact K ->is_measure nu ->nu K= 1 ->(0<C)%R ->
  (forall x,K x ->forall t:R,(0<t)%R ->nu (metric_closed_ball x t)<=(C*t)%R%:E) ->
  (euclidean_unit_ball_volume R 2/(4*C))%R%:E<=lower_minkowski_content 1 K.
Proof.
move=>hK hNu hMass hC hBall.
apply:(@positive_radius_lower_eventual_bound R (minkowski_tube_quotient 1 K)
  (euclidean_unit_ball_volume R 2/(4*C))%R%:E 1 ltr01)=>r /andP[hr _].
exact:compact_linear_mass_tube_lower_bound hK hNu hMass hC hr hBall.
Qed.
