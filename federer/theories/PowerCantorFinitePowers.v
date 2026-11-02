(** Federer (1969), 2.10.29, p. 195: every positive integer Cartesian power
    A(m,n)^q has finite degree-qm covering measure. Cover with same-level
    coordinate boxes and multiply the conserved level weights. The diameter
    bound q*r gives a finite constant; the printed paragraph does not
    require a sharp constant. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealPower MetricDiameterUP MetricDiameter MetricRealPowerCost MetricRealPowerMeasure
  CaratheodoryLimitUP CaratheodoryBorelRegular MetricScaleIndexedCover
  CompactIntervalGauge PowerConcaveIntervalGauge PowerCantorPairUP
  EqualCostIntervalTreeUP EqualCostIntervalTreeLaws EqualCostIntervalTreeSpecial EqualCostIntervalCommonWidth
  SpecialIntervalFamilyUP EuclideanSetPowers EuclideanIntervalBoxes PowerCantorLevelWeights
  PowerCoverDensityScalars FiniteFunctionPowerWeights NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_positive_cartesian_power_bound]: direct
    finite degree-qm bound for A(m,n)^q in
    2.10.29, p. 195. Here the positive
    integer q is represented by q0+1. With
    target coefficient b>=0, the explicit upper
    bound b*q^(qm) suffices for finiteness. *)
Theorem power_cantor_positive_cartesian_power_bound (R : realType) (c m b : R) n A f q0 :
  (0<c)%R -> (0<m)%R -> (m<1)%R -> (0<=b)%R ->
  is_power_cantor_pair c m n A f ->
  (@metric_real_power_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R q0.+1)]
    b (q0.+1%:R * m)%R (euclidean_set_power q0.+1 A)<=
      (b*real_power q0.+1%:R (q0.+1%:R * m))%R%:E)%E.
Proof.
move=> hc hm hm1 hb [J [H [hJ [ht [hA hf]]]]].
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have hspecial := @equal_cost_interval_tree_special R _ hg J n H ht.
have hq : (0<q0.+1%:R :> R)%R by rewrite ltr0n.
have hqne : (q0.+1%:R!=0 :> R)%R by rewrite gt_eqF.
have hpm : (0<=q0.+1%:R * m)%R := mulr_ge0 (ltW hq) (ltW hm).
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R q0.+1)].
pose C := (b*real_power q0.+1%:R (q0.+1%:R * m))%R.
have hC : (0<=C)%R := mulr_ge0 hb (real_power_nonnegative _ _).
apply: (caratheodory_limit_least (@metric_real_power_measure_specification R P b (q0.+1%:R * m)%R))=> delta nu hd hn.
have [i hcut] := reciprocal_metric_cutoffs_cofinal hd.
pose a := ((i.+1%:R : R)^-1)%R.
have ha : (0<a)%R by rewrite /a invr_gt0 ltr0n.
pose e := (a/q0.+1%:R)%R.
have he : (0<e)%R by rewrite /e divr_gt0.
have heq : (q0.+1%:R*e=a)%R by rewrite /e mulrC divfK.
have [N hmesh] := @special_tree_mesh R _ H hspecial e he.
pose W := (H N : finType).
pose F := [the finType of {ffun 'I_q0.+1 -> W}].
pose weight (S : W) := real_power
  (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val (val S)))) m.
have hw S : (0<=weight S)%R := real_power_nonnegative _ _.
have hsum : (\sum_(S : W) weight S= 1)%R.
  have hh := @power_cantor_level_weight_sum R c m J n H hc hm hm1 hJ ht N.
  by rewrite big_seq_fsetE in hh.
pose u (v : F) := @euclidean_interval_box_generator R q0.+1 (fun i=>val (v i)).
have hcost v : 0<=metric_real_diameter_cost b (q0.+1%:R * m)%R (val (u v)).
  exact: metric_real_power_cost_nonnegative hb.
have hsize v : extended_metric_diameter (val (u v))<=delta.
  have hbnd := @euclidean_interval_box_diameter_bound R q0.+1 (fun i=>val (v i)) e (ltW he)
    (fun i=>hmesh N (leqnn N) (val (v i)) (valP (v i))).
  rewrite heq in hbnd; exact: le_trans hbnd hcut.
have hcover : euclidean_set_power q0.+1 A `<=` \bigcup_(v in setT) val (u v).
  move=> x hx.
  have hex j : exists S : W, val (val S) (x j).
    have [S [hS hxS]] := (hA (x j)).1 (hx j) N.
    exists (Sub S hS); exact hxS.
  pose v : F := [ffun j=>projT1 (cid (hex j))].
  exists v; first exact Logic.I.
  move=> j; rewrite /v ffunE; exact: projT2 (cid (hex j)).
have hlocal v : metric_real_diameter_cost b (q0.+1%:R * m)%R (val (u v))<=
    (C*\prod_j weight (v j))%R%:E.
  pose S0 : compact_real_intervals R := val (v ord0).
  pose r := fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S0)).
  have hr : (0<r)%R := @equal_cost_tree_member_positive R _ J n H ht N S0 (valP (v ord0)).
  have hwidth j : fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val (val (v j))))=r.
    exact (@equal_cost_interval_tree_same_level_width R _ hg J n H ht N (val (v j)) S0 (valP (v j)) (valP (v ord0))).
  have hwidthle j : (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val (val (v j))))<=r)%R by rewrite hwidth.
  have hbox := @euclidean_interval_box_diameter_bound R q0.+1 (fun j=>val (v j)) r (ltW hr) hwidthle.
  have hbnd := @metric_real_power_cost_monotone R b (q0.+1%:R * m)%R _ _ hb hpm
    (metric_diameter_nonnegative (extended_metric_diameter_specification (val (u v)))) hbox.
  have hprod : (\prod_j weight (v j)=(real_power r m)^+q0.+1)%R.
    have heqprod : (\prod_j weight (v j)=\prod_(j : 'I_q0.+1) real_power r m)%R.
      apply: eq_bigr=> j _; by rewrite /weight hwidth.
    by rewrite heqprod prodr_const card_ord.
  apply: le_trans hbnd _.
  rewrite metric_real_power_cost_finite
    (@real_power_product R q0.+1%:R r (q0.+1%:R * m)%R (ltW hq) (ltW hr))
    (@real_power_positive_natural_multiple R r m hr hm q0.+1) hprod /C mulrA.
  exact: lexx.
have hbudget := @normalised_finite_function_cover_budget R [the finType of 'I_q0.+1] W weight C hC hw hsum.
have hcount : countable (@setT F) := finite_set_countable (@finite_finset F setT).
have hbound := @metric_scale_envelope_indexed_cover R P _ [the choiceType of (F : Type)] (fun S=>val S)
  (fun S=>metric_real_diameter_cost b (q0.+1%:R * m)%R (val S)) delta nu hn (euclidean_set_power q0.+1 A) setT u
  hcount (fun v _=>hcost v) (fun v _=>hsize v) hcover.
apply: le_trans hbound _; rewrite -hbudget.
apply: nonnegative_sum_mono=> v _; exact: hlocal.
Qed.
