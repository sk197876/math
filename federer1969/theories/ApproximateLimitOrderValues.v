(** Federer (1969), 3.1.3(2),(4), p. 213: an approximate limit
    equals both approximate order limits. This supporting implication
    expands the use of (2) in identifying the measurable good locus in (4).
    The corrected partial-domain definitions of 2.9.12 are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureDerivationContext
  MeasureSetDensity MeasureApproximateLimitUP MeasureApproximateOrderLimits
  ExtendedRealOrderTopology CountableOrderIntervals LocalZeroDensity ZeroDensityCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [disjoint_approximate_good_sets_impossible]: supporting
    uniqueness step in Federer 2.9.12, pp. 158–159, used for the
    upper/lower-limit characterization in 3.1.3(4), p. 213. Two disjoint
    inverse images cannot both have complements of density zero. *)
Lemma disjoint_approximate_good_sets_impossible (R : realType) (X : metricType R)
    (Y : Type) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) (U W : set Y) x :
  is_measure_derivation_context phi V ->
  (forall y, U y -> W y -> False) ->
  partial_function_graph (measure_set_density phi V (~` partial_function_preimage f U)) x 0 ->
  partial_function_graph (measure_set_density phi V (~` partial_function_preimage f W)) x 0 -> False.
Proof.
move=> hc hdis hU hW.
apply: zero_density_cover_impossible hc _ hU hW.
apply/seteqP; split=> z _; first exact Logic.I.
case: (pselect (partial_function_preimage f U z))=> [[u [hu hUu]]|hnU]; last by left.
right; move=> [w [hw hWw]].
have he := partial_function_single_valued hu hw.
rewrite -he in hWw; exact: hdis u hUu hWw.
Qed.

Section OrderValues.
Variable R : realType.
Variable X : metricType R.
Variable phi : set X -> \bar R.
Variable V : X -> set X -> Prop.
Hypothesis hc : is_measure_derivation_context phi V.
Variable f : partial_function X (extended_real_line R).
Variables x : X.
Variables c : extended_real_line R.
Hypothesis hl : is_measure_approximate_limit phi V f x c.

(** Source for [approximate_limit_upper_value]: the approximate upper
    limit equals the existing approximate limit, supporting the good-locus
    description in Federer 3.1.3(4), p. 213. Infinite values and proper
    domains are included. *)
Theorem approximate_limit_upper_value : measure_approximate_upper_limit phi V f x=c.
Proof.
symmetry; apply: measure_approximate_upper_limit_unique; split.
- move=> t ht; rewrite leNgt; apply/negP=> htc.
  have hn : nbhs c [set y : extended_real_line R | t<y].
    apply: open_nbhs_nbhs; split; first exact: order_strict_upper_ray_open.
    exact htc.
  have hz := hl hn.
  apply: (disjoint_approximate_good_sets_impossible hc _ ht hz).
  move=> y hyt hty; by have := lt_le_trans hty hyt; rewrite ltxx.
- move=> d hd; rewrite leNgt; apply/negP=> hcd.
  have [q [hcq hqd]] := @extended_rationals_order_dense R c d hcd.
  have hn : nbhs c [set y : extended_real_line R | y<(ratr q : R)%:E].
    apply: open_nbhs_nbhs; split; first exact: order_strict_lower_ray_open.
    exact hcq.
  have hz := hl hn.
  have ht : measure_approximate_upper_thresholds phi V f x (ratr q : R)%:E.
    apply: (@local_zero_density_mono R X phi V
      (~` partial_function_preimage f [set y | y<=(ratr q : R)%:E])
      (~` partial_function_preimage f [set y | y<(ratr q : R)%:E])
      setT x hc openT I _ hz).
    move=> z _ hbad [y [hy hyq]]; apply: hbad; exists y; split=> //; exact: ltW hyq.
  by have := lt_le_trans hqd (hd _ ht); rewrite ltxx.
Qed.

(** Source for [approximate_limit_lower_value]: the approximate lower
    limit equals the existing approximate limit, supporting Federer
    3.1.3(4), p. 213. This is the order-dual supporting argument. *)
Theorem approximate_limit_lower_value : measure_approximate_lower_limit phi V f x=c.
Proof.
symmetry; apply: measure_approximate_lower_limit_unique; split.
- move=> t ht; rewrite leNgt; apply/negP=> hct.
  have hn : nbhs c [set y : extended_real_line R | y<t].
    apply: open_nbhs_nbhs; split; first exact: order_strict_lower_ray_open.
    exact hct.
  have hz := hl hn.
  apply: (disjoint_approximate_good_sets_impossible hc _ ht hz).
  move=> y hty hyt; by have := lt_le_trans hyt hty; rewrite ltxx.
- move=> d hd; rewrite leNgt; apply/negP=> hdc.
  have [q [hdq hqc]] := @extended_rationals_order_dense R d c hdc.
  have hn : nbhs c [set y : extended_real_line R | (ratr q : R)%:E<y].
    apply: open_nbhs_nbhs; split; first exact: order_strict_upper_ray_open.
    exact hqc.
  have hz := hl hn.
  have ht : measure_approximate_lower_thresholds phi V f x (ratr q : R)%:E.
    apply: (@local_zero_density_mono R X phi V
      (~` partial_function_preimage f [set y | (ratr q : R)%:E<=y])
      (~` partial_function_preimage f [set y | (ratr q : R)%:E<y])
      setT x hc openT I _ hz).
    move=> z _ hbad [y [hy hqy]]; apply: hbad; exists y; split=> //; exact: ltW hqy.
  by have := lt_le_trans hdq (hd _ ht); rewrite ltxx.
Qed.
End OrderValues.
