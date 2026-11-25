(** Federer (1969), 3.3.21, p. 309: a genuine sparse-radius ball meets at most one original small square. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP PowerCantorWidthLawsUP PowerCantorLevelPointGap
  PowerCantorUniformGapScalar MetricClosedBalls EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct EuclideanIntervalRectangles MetricCartesianProductUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scheduled_original_ball_in_one_piece]: at the
    actual radius r_j=kappa*w_j/(3*n_j), the original E intersect
    the closed ball is either empty or lies in a SINGLE actual
    original square at level j+1. This supplies the low-density
    radii of 3.3.21, p. 309. All earlier-parent and same-parent
    separation estimates are proved from the original Phi laws.
    The original centre is arbitrary, including centres outside E. *)
Theorem scheduled_original_ball_in_one_piece (R:realType) (c m:R)
    (J:compact_real_intervals R) n H w (A:set (real_line_metric R)) j
    (a:inner_metric_space (@euclidean_inner_productP R 2)):
  0<c ->0<m ->m<1 ->(forall k,(2<=n k)%N) ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_special_interval_tree_limit H A ->is_power_cantor_widths c m n w ->
  let r:=(1-2 * real_power 2 (-m^-1)) * w j/(3 * (n j)%:R) in
  (euclidean_cantor_product A A `&` metric_closed_ball a r=set0) \/
  exists S T,S \in H j.+1 /\T \in H j.+1 /\
    euclidean_cantor_product A A `&` metric_closed_ball a r `<=`
      euclidean_cantor_product A A `&` euclidean_interval_rectangle S T.
Proof.
move=>hc hm hm1 hn hJ hTree hA hWidths r.
pose k:= 1-2 * real_power (2:R) (-m^-1).
have hk:0<k:=(andP (power_cantor_uniform_gap_positive hm hm1)).1.
have hw:=power_cantor_width_positive hWidths j.
have hN:0<((n j)%:R:R) by rewrite ltr0n;exact:leq_trans (leqnSn 1) (hn j).
have hr:0<r by rewrite /r divr_gt0 ?mulr_gt0 // ?ltr0n.
have hGap:2 * r<k * w j/(n j)%:R.
  have hPositive:0<k * w j/(n j)%:R by rewrite divr_gt0 // mulr_gt0.
  have hIdentity:r=(k * w j/(n j)%:R)/3 by rewrite /r /k;field;by rewrite ?gt_eqF // ?pnatr_eq0.
  rewrite hIdentity;nra.
case:(eqVneq (euclidean_cantor_product A A `&` metric_closed_ball a r) set0)=>hEmpty.
- by left.
- right;have [x [hxA hxBall]]:euclidean_cantor_product A A `&` metric_closed_ball a r !=set0 by apply/set0P.
  have [S [hS hxS]]:=(hA _).1 hxA.1 j.+1.
  have [T [hT hxT]]:=(hA _).1 hxA.2 j.+1.
  exists S,T;split=>//;split=>//;move=>y [hyA hyBall];split;first exact:hyA.
  have [U [hU hyU]]:=(hA _).1 hyA.1 j.+1.
  have [V [hV hyV]]:=(hA _).1 hyA.2 j.+1.
  have hDistance:mdist x y<= 2 * r.
    have hTriangle:=metric_triangle x a y.
    have hX:mdist x a<=r by rewrite metric_sym;exact:hxBall.
    have hY:mdist a y<=r:=hyBall.
    nra.
  have hFirst:U=S.
    case:(eqVneq U S)=>//hDifferent.
    have hSeparate:=@power_cantor_original_sharp_next_level_gap R c m J n H w j U S
      (euclidean_real_plane_first y) (euclidean_real_plane_first x)
      hc hm hm1 hn hJ hTree hWidths hU hS hDifferent hyU hxS.
    have hCoordinate:=(metric_product_first_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 y x Logic.I Logic.I.
    rewrite mul1r in hCoordinate.
    have hReverse:mdist y x<= 2 * r by rewrite metric_sym.
    have hImpossible:=lt_le_trans hGap (le_trans hSeparate (le_trans hCoordinate hReverse)).
    by rewrite ltxx in hImpossible.
  have hSecond:V=T.
    case:(eqVneq V T)=>//hDifferent.
    have hSeparate:=@power_cantor_original_sharp_next_level_gap R c m J n H w j V T
      (euclidean_real_plane_second y) (euclidean_real_plane_second x)
      hc hm hm1 hn hJ hTree hWidths hV hT hDifferent hyV hxT.
    have hCoordinate:=(metric_product_second_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 y x Logic.I Logic.I.
    rewrite mul1r in hCoordinate.
    have hReverse:mdist y x<= 2 * r by rewrite metric_sym.
    have hImpossible:=lt_le_trans hGap (le_trans hSeparate (le_trans hCoordinate hReverse)).
    by rewrite ltxx in hImpossible.
  by split;[rewrite -hFirst|rewrite -hSecond].
Qed.
