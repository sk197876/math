(** Federer (1969), 2.10.28, p. 193: cumulative function of the recursively
    refined compact limit. Derive its increment bound, continuity, full
    range and derivative off A from the abstract tree and cumulative laws.
    Lebesgue almost-everywhere differentiation is reserved for the
    fractional-power case. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws
  ConcaveIntervalMeasure EqualCostIntervalTreeUP EqualCostIntervalTreeLaws EqualCostCantorMass
  SpecialIntervalFamilyUP SpecialIntervalLimitLaws MeasureUP MeasureBasic MeasureRestriction
  TopologicalBorel BorelRegularMeasureUP CountableOrderIntervals
  FiniteCumulativeFunctionUP FiniteCumulativeFunction FiniteCumulativeFunctionLaws
  ConcaveIntervalDistributionBounds RestrictedCumulativeLocality RestrictedCumulativeRange RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [concave_cantor_cumulative_exists]: supporting
    existence of the real f defined in
    2.10.28, p. 193, from the already
    proved finite mass and the opaque finite
    cumulative witness. No range or regularity
    conclusion is assumed to obtain f. *)
Theorem concave_cantor_cumulative_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H A :
  is_equal_cost_interval_tree h J n H -> is_special_interval_tree_limit H A ->
  exists f : R -> R, is_finite_cumulative_function (measure_restrict (concave_interval_measure h) A) f.
Proof.
move=> ht hA.
have [_ [_ [hmass _]]] := @equal_cost_interval_limit_mass R h hg J n H A ht hA.
have hm := concave_interval_measure_is_measure hg.
have hn := measure_restrict_is_measure hm A.
have hfin : (measure_restrict (concave_interval_measure h) A setT< +oo)%E.
  by rewrite /measure_restrict setIT hmass ltry.
exists (@finite_cumulative_function R _ hn hfin); exact: finite_cumulative_function_specification.
Qed.

(** Source for [concave_cantor_cumulative_properties]: direct
    increment, range and off-set derivative
    conclusions in 2.10.28, p. 193,
    for a general admitted concave gauge.
    The power gauge gives the printed Holder
    bound; nullity is proved separately there.
    Both A and f are used only through
    their abstract membership and value laws. *)
Theorem concave_cantor_cumulative_properties (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H A (f : R -> R) :
  is_equal_cost_interval_tree h J n H -> is_special_interval_tree_limit H A ->
  is_finite_cumulative_function (measure_restrict (concave_interval_measure h) A) f ->
  (forall a b, a<=b -> 0<=f b-f a /\ f b-f a<=h (b-a)) /\
  continuous (f : real_line_metric R -> real_line_metric R) /\
  f @` A=(`[0,concave_interval_cost h (val J)] : set R) /\
  f @` setT=(`[0,concave_interval_cost h (val J)] : set R) /\
  forall x, ~A x -> has_real_curve_derivative f x 0.
Proof.
move=> ht hA hf.
have [hcompact [hsub [hmass hbound]]] := @equal_cost_interval_limit_mass R h hg J n H A ht hA.
have hm := concave_interval_measure_is_measure hg.
have hinc := @concave_interval_distribution_increment_bound R h hg A f hf hbound.
have hcont := @concave_interval_distribution_continuous R h hg f hinc.
have hJmem : J \in H 0%N by rewrite (equal_cost_tree_root ht) in_fset1.
have hpos := @equal_cost_tree_member_positive R h J n H ht 0%N J hJmem.
have hMpos : 0<concave_interval_cost h (val J).
  have hh := @concave_interval_gauge_strictly_increasing R h hg 0 _ (lexx 0) hpos.
  by rewrite (interval_gauge_zero hg) in hh.
have hne : A !=set0.
  apply: contrapT=> hnone.
  have hempty : A=set0.
    apply/seteqP; split=> [x hx|x []]; apply: hnone; by exists x.
  rewrite hempty (measure_empty hm) in hmass.
  have hz : concave_interval_cost h (val J)=0 := EFin_inj (esym hmass).
  by rewrite hz ltxx in hMpos.
have hatom := @concave_interval_measure_singleton_zero R h hg.
have [hrangeA hrange] := @restricted_cumulative_full_range R _ hm A f hf _ hne hcompact hatom hmass hcont.
have hray x : measure_measurable (concave_interval_measure h) [set z : R | z<=x].
  apply: (@borel_regular_borel_measurable R (real_line_metric R) _ hm
    (@concave_interval_measure_borel_regular R h hg)).
  apply: closed_borel_set; exact: order_closed_lower_ray_closed.
split=> //; split=> //; split=> //; split=> //.
apply: (@restricted_cumulative_derivative_off_closed_set R _ hm A f hf hray).
exact: interval_tree_limit_closed hA.
Qed.
