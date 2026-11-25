(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting passage
    from weighted Borel cover costs to indicator functions. A Borel null
    hull transfers the pointwise cost bound to almost-everywhere covers. The
    Borel-partition formula 2.10.8, p. 175, and the proved restricted
    weighted measure then give the indicator equality. no identical weighted
    geometric theorem was located. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import WeightedBorelCoverCostUP WeightedMetricEnvelopeUP
  WeightedMetricEnvelopeLaws WeightedMetricEnvelope WeightedMetricLimitUP WeightedMetricLimit
  WeightedRestrictionMeasure WeightedRestrictionSeparation WeightedUpperIntegralBound
  BorelCoverCostUP BorelCaratheodoryMeasure BorelPartition BorelPartitionCoverBounds BorelPartitionCharacterization
  BorelRegularMeasureUP TopologicalBorel CaratheodoryLimitUP MeasureUP MeasureBasic MeasureCountableAdditivity
  MeasureAlmostUP MeasureAlmostBasic NonnegativeSum NonnegativeSumSupport NonnegativeSumBoolean
  ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_borel_cost_almost_cover_bound]: supporting
    null-exception step for the final paragraph of 2.10.24,
    p. 188. A Borel null hull has zero cost by
    the cost domination proved in 2.10.8, p. 175;
    remove it before applying the pointwise weighted law.
    The target is Borel and the original weights and
    generator index set are unchanged. *)
Theorem weighted_borel_cost_almost_cover_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hw : has_weighted_borel_cover_bound c) (J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (A : set X) :
  countable G -> (forall j, G j -> (0<=u j)%R) -> borel_set A ->
  (forall j, G j -> borel_set (S j)) ->
  measure_almost_everywhere (borel_caratheodory_measure c)
    [set x | weighted_function_restriction (fun _=>1) A x<=weighted_generator_sum S G u x] ->
  c A<=weighted_generator_cost (fun j=>c (S j)) G u.
Proof.
move=> hG hu hA hS hdom.
pose psi := borel_caratheodory_measure c.
have hm := borel_caratheodory_is_measure hc.
have hreg := borel_caratheodory_borel_regular hc.
pose N := ~` [set x | weighted_function_restriction (fun _=>1) A x<=weighted_generator_sum S G u x].
have hN : psi N=0 := hdom.
have [B [hNB [hB hval]]] := borel_regular_cover hreg N.
have hB0 : psi B=0 := eq_trans (esym hval) hN.
have hcB : c B=0.
  apply/eqP; rewrite eq_le (@borel_cover_cost_nonnegative R X c hc B hB) andbT.
  have hh : c B<=psi B := @borel_caratheodory_cost_bound R X c hc B hB.
  by rewrite hB0 in hh.
have hAB : borel_set (A `\` B) := borel_set_difference hA hB.
have hweighted : c (A `\` B)<=weighted_generator_cost (fun j=>c (S j)) G u.
  apply: (@hw J S G u (A `\` B) hG hu hAB hS)=> x [hxA hxB].
  have hxgood : weighted_function_restriction (fun _=>1) A x<=weighted_generator_sum S G u x.
    apply: contrapT=> hbad; apply: hxB; apply: hNB; exact hbad.
  by rewrite /weighted_function_restriction (mem_set hxA) in hxgood.
pose T b := if b then A `\` B else B.
have hcover : A `<=` \bigcup_(b in @setT bool) T b.
  move=> x hx; case: (pselect (B x))=> [hxB|hxB].
  - exists false=> //.
  - exists true=> //; by split.
have hT b : borel_set (T b) by case: b=> /=.
have hbound := @borel_cover_cost_cover R X c hc [the choiceType of (bool : Type)] setT T A
  (countableP _) hA (fun b _=>hT b) hcover.
rewrite nonnegative_sum_bool in hbound; last by case=> /=; exact: borel_cover_cost_nonnegative.
rewrite /T hcB adde0 in hbound; exact: le_trans hbound hweighted.
Qed.

(** Source for [weighted_borel_indicator_cost_bound]: supporting
    cost domination by the limiting indicator functional
    for the final paragraph of 2.10.24, p. 188.
    The lower bound holds already at any cutoff;
    cutoff one suffices to pass to the limit. *)
Theorem weighted_borel_indicator_cost_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hw : has_weighted_borel_cover_bound c) (A : set X) :
  borel_set A -> c A<=weighted_restriction_measure
    (fun j : @borel_metric_sets R X=>val j) (fun j=>c (val j))
    (borel_caratheodory_measure c) (fun _=>1) A.
Proof.
move=> hA.
rewrite weighted_restriction_measureE.
pose S := fun j : @borel_metric_sets R X=>val j.
pose d := fun j=>c (S j).
pose psi := borel_caratheodory_measure c.
pose lambda := weighted_metric_envelope S d psi 1.
have hl := weighted_metric_envelope_specification S d psi 1.
have hlow : c A<=lambda (weighted_function_restriction (fun _=>1) A).
  apply: (weighted_metric_envelope_greatest hl)=> G u hcover.
  exact: (@weighted_borel_cost_almost_cover_bound R X c hc hw _ S G u A
    (weighted_metric_cover_countable hcover) (weighted_metric_cover_nonnegative hcover) hA
    (fun j _=>set_valP j) (weighted_metric_cover_dominates hcover)).
apply: le_trans hlow _.
exact: (@weighted_metric_limit_upper R X _ S d psi _ (weighted_metric_limit_specification S d psi)
  _ 1 lambda (ltr01 : 0<1) hl).
Qed.

(** Source for [weighted_borel_indicator_measure_lower_bound]:
    supporting indicator conclusion of the final paragraph
    of 2.10.24, p. 188. Apply the exact Borel-partition
    supremum of 2.10.8, p. 175: each partition cost
    is bounded by the sum of restricted weighted
    measures, hence by their value on the target.
    Infinite measures and empty partitions are included. *)
Theorem weighted_borel_indicator_measure_lower_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hw : has_weighted_borel_cover_bound c) (D A : set X) :
  countable D -> dense D -> borel_set A -> borel_caratheodory_measure c A<=
    weighted_restriction_measure (fun j : @borel_metric_sets R X=>val j)
      (fun j=>c (val j)) (borel_caratheodory_measure c) (fun _=>1) A.
Proof.
move=> hD hden hA.
pose S := fun j : @borel_metric_sets R X=>val j.
pose d := fun j : @borel_metric_sets R X=>c (val j).
pose psi := borel_caratheodory_measure c.
pose nu := weighted_restriction_measure S d psi (fun _=>1).
have hc0 j : 0<=d j := @borel_cover_cost_nonnegative R X c hc (val j) (set_valP j).
have hnu := @weighted_restriction_is_measure R X _ S d psi (fun _=>1)
  (borel_caratheodory_specification c) hc0 (fun _=>ler01).
have hmeas B (hB : borel_set B) : measure_measurable nu B.
  exact: (@weighted_restriction_borel_measurable R X _ S d psi (fun _=>1)
    (borel_caratheodory_specification c) hc0 (fun _=>ler01) B hB).
have hs := @borel_partition_cost_supremum_all R X c hc D A hD hden hA.
apply: (extended_real_supremum_least hs)=> a [H [hH ->]].
have hdis B C (hB : H B) (hC : H C) (hne : B!=C) x (hxB : B x) (hxC : C x) : False.
  have hBC : B<>C by move=> he; apply: (negP hne); apply/eqP; exact he.
  have he := borel_partition_disjoint hH hB hC hBC.
  have hx : (B `&` C) x by split.
  by rewrite he in hx.
have hadd := @measure_countable_disjoint_additivity R X [the choiceType of set X] nu hnu H idfun
  (borel_partition_countable hH) (fun B hB=>hmeas B (borel_partition_members hH hB))
  hdis.
rewrite (borel_partition_union hH) in hadd.
change (is_true (borel_partition_cost c H<=nu A)).
rewrite hadd; apply: nonnegative_sum_mono=> B hB.
exact: (@weighted_borel_indicator_cost_bound R X c hc hw B (borel_partition_members hH hB)).
Qed.
