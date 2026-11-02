(** Federer (1969), 2.10.29, p. 193: the self-product A(m,n)^2 has degree-2m
    measure at most b*2^m, with b the degree-2m normaliser. Cover by pairs
    of intervals from one common level. Equal level widths give the square
    cost, and the conserved m-power weights give its sum. The intervals
    shrink to zero through the proved tree laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealPower MetricDiameterUP MetricDiameter MetricRealPowerCost MetricRealPowerMeasure
  CaratheodoryLimitUP CaratheodoryBorelRegular MetricScaleEnvelopeUP MetricScaleIndexedCover
  CompactIntervalGauge EqualCostIntervalTreeUP EqualCostIntervalTreeLaws EqualCostIntervalTreeSpecial
  EqualCostIntervalCommonWidth SpecialIntervalFamilyUP PowerConcaveIntervalGauge PowerCantorPairUP
  PowerCantorLevelWeights PowerCantorSquareCost EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_self_product_bound]: direct
    finite self-product bound in 2.10.29,
    p. 193, for every actual power Cantor
    pair. The book substitutes b=alpha(2m)*2^(-2m)
    to obtain alpha(2m)*2^(-m); b is explicit
    here and may also be zero. *)
Theorem power_cantor_self_product_bound (R : realType) (c m b : R) n A f :
  (0<c)%R -> (0<m)%R -> (m<1)%R -> (0<=b)%R ->
  is_power_cantor_pair c m n A f ->
  (@metric_real_power_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    b (2 * m)%R (euclidean_cantor_product A A)<=(b*real_power 2 m)%R%:E)%E.
Proof.
move=> hc hm hm1 hb [J [H [hJ [ht [hA hf]]]]].
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have hspecial := @equal_cost_interval_tree_special R _ hg J n H ht.
have h2 : (0<2 :> R)%R by rewrite ltr0n.
have hs : (0<Num.sqrt (2 : R))%R by rewrite sqrtr_gt0.
have hsne : (Num.sqrt (2 : R)!=0)%R by rewrite gt_eqF.
have hpm : (0<=2 * m)%R := mulr_ge0 (ltW h2) (ltW hm).
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose I := compact_real_intervals R.
pose w (S : I) := (real_power (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))) m)%:E.
pose C := (b*real_power 2 m)%R.
have hC : 0<=C%:E by rewrite lee_fin /C; exact: mulr_ge0 hb (real_power_nonnegative _ _).
have hw S : 0<=w S by rewrite /w lee_fin; exact: real_power_nonnegative.
apply: (caratheodory_limit_least (@metric_real_power_measure_specification R P b (2 * m)%R))=> delta nu hd hn.
have [i hcut] := reciprocal_metric_cutoffs_cofinal hd.
pose a := ((i.+1%:R : R)^-1)%R.
have ha : (0<a)%R by rewrite /a invr_gt0 ltr0n.
pose e := (a/Num.sqrt 2)%R.
have he : (0<e)%R by rewrite /e divr_gt0.
have heq : (Num.sqrt 2*e=a)%R by rewrite /e mulrC divfK.
have [N hmesh] := @special_tree_mesh R _ H hspecial e he.
pose D := ([set S : I | S \in H N] `*` [set T : I | T \in H N]).
have hDeq : D=[set p : I*I | p \in (H N `*` H N)%fset].
  apply/seteqP; split=> p; rewrite /D /= in_fsetM; [by move=> [hS hT]; apply/andP | by move=> /andP].
have hDcount : countable D.
  rewrite hDeq; exact: finite_set_countable (finite_fset (H N `*` H N)%fset).
pose q (p : I*I) := euclidean_interval_rectangle_generator p.1 p.2.
have hcost p : 0<=metric_real_diameter_cost b (2 * m)%R (val (q p)).
  exact: metric_real_power_cost_nonnegative hb.
have hsize p : D p -> extended_metric_diameter (val (q p))<=delta.
  move=> [hp1 hp2].
  have h1 := hmesh N (leqnn N) p.1 hp1.
  have h2' := hmesh N (leqnn N) p.2 hp2.
  have hr := @euclidean_interval_rectangle_diameter_bound R p.1 p.2 e (ltW he) h1 h2'.
  rewrite heq in hr; exact: le_trans hr hcut.
have hcover : euclidean_cantor_product A A `<=` \bigcup_(p in D) val (q p).
  move=> p [hp1 hp2].
  have [S [hS hpS]] := (hA (euclidean_real_plane_first p)).1 hp1 N.
  have [T [hT hpT]] := (hA (euclidean_real_plane_second p)).1 hp2 N.
  exists (S,T); first by split.
  by split.
have hlocal p : D p -> metric_real_diameter_cost b (2 * m)%R (val (q p))<=C%:E*w p.1*w p.2.
  move=> [hp1 hp2].
  pose r := fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val p.1)).
  have hr : (0<r)%R := @equal_cost_tree_member_positive R _ J n H ht N p.1 hp1.
  have hwidth := @equal_cost_interval_tree_same_level_width R _ hg J n H ht N p.2 p.1 hp2 hp1.
  have hwidthle : (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val p.2))<=r)%R by rewrite hwidth.
  have hrect := @euclidean_interval_rectangle_diameter_bound R p.1 p.2 r (ltW hr) (lexx r) hwidthle.
  have hbnd := @metric_real_power_cost_monotone R b (2 * m)%R _ _ hb hpm
    (metric_diameter_nonnegative (extended_metric_diameter_specification (val (q p)))) hrect.
  apply: le_trans hbnd _.
  rewrite metric_real_power_cost_finite (@power_cantor_square_cost R b m r hm (ltW hr))
    /C /w hwidth -!EFinM lee_fin -/r expr2 !mulrA; exact: lexx.
have hbudget := @normalised_weights_product_budget R I I [set S : I | S \in H N] [set T : I | T \in H N]
  w w C%:E hC (fun S _=>hw S) (fun S _=>hw S)
  (@power_cantor_level_numerical_weight_sum R c m J n H hc hm hm1 hJ ht N)
  (@power_cantor_level_numerical_weight_sum R c m J n H hc hm hm1 hJ ht N).
have hbound := @metric_scale_envelope_indexed_cover R P _ [the choiceType of (I*I)%type] (fun S=>val S)
  (fun S=>metric_real_diameter_cost b (2 * m)%R (val S)) delta nu hn (euclidean_cantor_product A A) D q
  hDcount (fun p _=>hcost p) hsize hcover.
apply: le_trans hbound _; rewrite -hbudget.
exact: nonnegative_sum_mono hlocal.
Qed.
