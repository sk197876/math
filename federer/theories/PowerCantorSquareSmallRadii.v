(** Federer (1969), 3.2.40, p. 276: the actual
    level-width tube estimate occurs at arbitrarily small
    positive real radii for every original power Cantor pair. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  EuclideanInnerProduct InnerMetric EuclideanCantorProduct EuclideanBallVolume
  PowerCantorPairUP PowerConcaveIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalTreeLaws EqualCostIntervalTreeSpecial EqualCostIntervalCommonWidth
  EqualCostIntervalTreeNonempty SpecialIntervalFamilyUP
  PowerCantorSquareLevelTube RealPower MinkowskiContents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_square_arbitrarily_small_level_bound]:
    supporting lower-content estimates in Federer 3.2.40, p. 276.
    Every small-radius request is met by an actual nonempty
    interval level, whose true common width is positive and
    tends to zero by the earlier tree laws. This assertion
    does not require a rapid subdivision schedule. *)
Lemma power_cantor_square_arbitrarily_small_level_bound (R:realType) (c m:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R) (d:R):
  (0<c)%R ->(0<m)%R ->(m<1)%R ->is_power_cantor_pair c m n A f ->(0<d)%R ->
  exists s:R,(0<s<d)%R /\
    minkowski_tube_quotient 1 (euclidean_cantor_product A A) s<=
      ((euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2)*real_power s (1-2 * m))%R%:E.
Proof.
move=>hc hm hm1 [J [H [hJ [hTree [hA hCumulative]]]]] hd.
have hg:=power_concave_interval_gauge hc hm hm1.
have hSpecial:=@equal_cost_interval_tree_special R _ hg J n H hTree.
have hHalf:(0<d/2)%R by rewrite divr_gt0 // ltr0n.
have [j hMesh]:=@special_tree_mesh R (fun t=>(c*real_power t m)%R) H hSpecial (d/2)%R hHalf.
have [S hS]:=equal_cost_interval_tree_level_nonempty hTree j.
pose s:=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)).
have hs:(0<s)%R:=@equal_cost_tree_member_positive R _ J n H hTree j S hS.
have hsd:(s<d)%R.
  have h:=hMesh j (leqnn j) S hS.
  have hHalfLt:(d/2<d)%R by lra.
  exact:le_lt_trans h hHalfLt.
have hWidth T:T \in H j ->fine (@extended_metric_diameter R
    [the metricType R of real_line_metric R] (val T))=s.
  move=>hT; exact:(@equal_cost_interval_tree_same_level_width R _ hg J n H hTree j T S hT hS).
exists s; split; first by apply/andP; split.
exact:(@power_cantor_square_level_tube_bound R c m J n H A j s
  hc hm hm1 hJ hTree hA hs hWidth).
Qed.
