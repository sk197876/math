(** Federer (1969), 2.10.22, p. 184: choose near-optimal countable compact
    covers inside F_(a,r+delta). Discard generators missing the target.
    Remove zero-cost generators through their proved final-measure nullity
    and enumerate the positive costs using the sealed interface. This
    explicitly handles finite covers without padding by positive-cost
    singletons. Source context and the cost-order proof route:
    CompactGeneratorCostUP.v and SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactMetricBounded CompactBallProfiles
  CompactGeneratorCostUP CompactZeroCostGenerators MetricClosedBalls MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleApproximation MetricScaleOptionalCover CaratheodoryLimitUP
  NonnegativeSum SummableCostEnumerationUP SummableCostEnumeration SummableCostEnumerationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_near_optimal_row]: supporting
    source row in 2.10.22, p. 184. The
    exceptional set has actual final measure zero;
    every active generator remains an original nonempty
    compact set with its original cost. *)
Theorem compact_cost_near_optimal_row (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (delta : R) (nu mu : set X -> \bar R) (A : set X) (a : X) (r s e : R) :
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E nu ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) mu ->
  (nu A<=s%:E)%E -> 0<e -> e<=1 -> A `<=` metric_closed_ball a r ->
  exists (Z : set X) (u : nat -> option (compact_metric_set X)),
    mu Z=0%E /\ A `\` Z `<=` \bigcup_k optional_generator_set (fun C=>val C) (u k) /\
    (forall k C, u k=Some C -> compact_sets_in_ball a (r+delta) C /\ compact_metric_diameter C<=delta) /\
    (nonnegative_sum setT (fun k=>(optional_generator_cost c (u k))%:E)<=(s+e)%:E)%E /\
    (forall k, k.+1%:R*optional_generator_cost c (u k)<=s+1).
Proof.
move=> hn hm hbound he he1 hA.
have hstrict : (nu A<(s+e)%:E)%E.
  apply: le_lt_trans hbound _; rewrite lte_fin; lra.
have [G [hG [hdiam [hcover hcost]]]] := metric_scale_envelope_approximation hn hstrict.
pose H : set (compact_metric_set X) := G `&` [set C | exists x, A x /\ val C x].
have hHG : H `<=` G by move=> C [hC _].
have hH : countable H := sub_countable (subset_card_le hHG) hG.
have hcovH : A `<=` \bigcup_(C in H) val C.
  move=> x hx; have [C hC hxC] := hcover x hx.
  exists C=> //; split=> //; exists x; by split.
have hcostH : (nonnegative_sum H (fun C=>(c C)%:E)<=(s+e)%:E)%E.
  exact: le_trans (nonnegative_sum_subset _ hHG) (ltW hcost).
have hcommon : (nonnegative_sum H (fun C=>(c C)%:E)<=(s+1)%:E)%E.
  apply: le_trans hcostH _; rewrite lee_fin; exact: lerD (lexx s) he1.
have h0 C : 0<=c C := compact_cost_nonnegative_law hc C.
pose u := @summable_cost_enumeration R (compact_metric_set X) H c (s+1) (fun C _=>h0 C) hcommon.
have hu := @summable_cost_enumeration_specification R (compact_metric_set X) H c (s+1)
  (fun C _=>h0 C) hcommon.
pose H0 : set (compact_metric_set X) := H `&` [set C | c C=0].
pose Z := \bigcup_(C in H0) val C.
have hZ : mu Z=0%E.
  apply: (@compact_countable_zero_cost_null R X c hc mu H0 hm).
  - apply: sub_countable hH; apply: subset_card_le=> C [hC _]; exact hC.
  - by move=> C [_ hz].
have hrowcover : A `\` Z `<=` \bigcup_k optional_generator_set (fun C=>val C) (u k).
  move=> x [hx hxZ]; have [C hC hxC] := hcovH x hx.
  have hpos : 0<c C.
    rewrite lt_neqAle h0 andbT; apply/eqP=> hz; apply: hxZ.
    exists C=> //; split=> //; exact: esym hz.
  have [k hk] := @cost_enumeration_covers_positive_law R (compact_metric_set X) H c (s+1) u hu C hC hpos.
  exists k=> //; by rewrite hk /optional_generator_set.
have hrowmem k C (hk : u k=Some C) :
    compact_sets_in_ball a (r+delta) C /\ compact_metric_diameter C<=delta.
  have [hC _] := @cost_enumeration_member_law R (compact_metric_set X) H c (s+1) u hu k C hk.
  have hd := hdiam C hC.1; rewrite compact_metric_diameter_finite_value lee_fin in hd.
  split=> // y hy; have [x [hx hxC]] := hC.2.
  have hax : mdist a x<=r := hA x hx.
  have hxy := metric_diameter_upper (extended_metric_diameter_specification (val C)) hxC hy.
  rewrite compact_metric_diameter_finite_value lee_fin in hxy.
  have ht := metric_triangle a x y.
  change (is_true (mdist a y<=r+delta)); lra.
exists Z,u; split=> //; split=> //; split=> //; split.
- exact: le_trans (cost_enumeration_sum_bound hu (fun C _=>h0 C)) hcostH.
- exact: cost_enumeration_uniform_bound_law hu.
Qed.
