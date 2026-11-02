(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting passage
    from Borel indicators to arbitrary targets in the Borel-generator
    constructions. A fine weighted majorant has Borel closed superlevels.
    Its unit superlevel contains the target modulo a null set and has
    controlled weighted limit, so 2.10.8, p. 175, supplies the desired lower
    bound. the geometric conclusion is not attributed to that corollary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import WeightedBorelCoverCostUP WeightedBorelIndicatorBounds WeightedMeasurableMajorant
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedMetricLimit WeightedFunctionOrderAndScale
  WeightedRestrictionMeasure WeightedIndicatorOrdinaryBound BorelCoverCostUP BorelCaratheodoryMeasure
  BorelRegularMeasureUP TopologicalBorel MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_borel_indicator_lower_bound_all_sets]:
    supporting arbitrary-target indicator bound for the final
    paragraph of 2.10.24, p. 188. Borel majorant levels
    and the partition theorem 2.10.8, p. 175, remove
    the target measurability restriction. Both infinite
    target measures and zero limiting values are allowed. *)
Theorem weighted_borel_indicator_lower_bound_all_sets (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hw : has_weighted_borel_cover_bound c) (D A : set X) :
  countable D -> dense D -> borel_caratheodory_measure c A<=
    weighted_restriction_measure (fun j : @borel_metric_sets R X=>val j)
      (fun j=>c (val j)) (borel_caratheodory_measure c) (fun _=>1) A.
Proof.
move=> hD hden; rewrite weighted_restriction_measureE.
pose S := fun j : @borel_metric_sets R X=>val j.
pose d := fun j : @borel_metric_sets R X=>c (val j).
pose psi := borel_caratheodory_measure c.
pose f := @weighted_function_restriction R X (fun _=>1) A.
pose L := weighted_metric_limit S d psi.
have hL := weighted_metric_limit_specification S d psi.
have hm : is_measure psi := borel_caratheodory_is_measure hc.
have hreg := borel_caratheodory_borel_regular hc.
have hmeas B (hB : borel_set B) : measure_measurable psi B := borel_regular_borel_measurable hm hreg hB.
have hnon : 0<=L f := @weighted_metric_limit_nonnegative R X _ S d psi L hL f.
change (is_true (psi A<=L f)).
case hval: (L f)=> [M| |] in hnon *; [|exact: leey|by []].
apply: (@extended_upper_bound_from_scaled_errors R (psi A) M 1%R (@ler01 R))=> e he.
rewrite mul1r.
have [g [hg0 [hgmeas [hglevel [hfg hbudget]]]]] := @weighted_finite_limit_borel_majorant R X _
  S d psi f M e hm hmeas (fun j=>set_valP j) hval he.
pose B := [set x | 1<=g x].
have hB : borel_set B := hglevel 1%R.
have hAB0 : psi (A `\` B)=0.
  apply: (@measure_null_subset R X psi hm (A `\` B) (~` [set x | f x<=g x]) _ hfg).
  move=> x [hxA hxB] hx; apply: hxB.
  have hh : f x<=g x := hx.
  by rewrite /f /weighted_function_restriction (mem_set hxA) in hh.
have hpsiAB : psi A<=psi B.
  have hcover : A `<=` B `|` (A `\` B).
    move=> x hxA; case: (pselect (B x))=> [hxB|hxB]; [by left|right; by split].
  have hh := @measure_binary_cover R X psi hm A B (A `\` B) hcover.
  by rewrite hAB0 adde0 in hh.
have hBg : measure_almost_everywhere psi [set x | weighted_function_restriction (fun _=>1) B x<=g x].
  apply: (@measure_almost_everywhere_mono R X psi hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  change (is_true (@weighted_function_restriction R X (fun _=>1) B x<=g x)).
  rewrite /weighted_function_restriction; case hx: (x \in B); last exact: hg0.
  exact: set_mem hx.
have horder := @weighted_metric_limit_almost_order R X _ S d psi L
  (weighted_function_restriction (fun _=>1) B) g hm hL hBg.
have hpsiB : psi B<=L (weighted_function_restriction (fun _=>1) B).
  have hh := @weighted_borel_indicator_measure_lower_bound R X c hc hw D B hD hden hB.
  rewrite weighted_restriction_measureE in hh; exact hh.
exact: le_trans hpsiAB (le_trans hpsiB (le_trans horder hbudget)).
Qed.

(** Source for [weighted_borel_indicator_equality_all_sets]:
    supporting complete indicator case of the final paragraph
    of 2.10.24, p. 188. The lower bound uses
    Borel partitions; the upper bound uses ordinary
    covers with unit coefficients. Arbitrary nonmeasurable
    targets retain the original outer-measure value. *)
Theorem weighted_borel_indicator_equality_all_sets (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hw : has_weighted_borel_cover_bound c) (D A : set X) :
  countable D -> dense D ->
  weighted_restriction_measure (fun j : @borel_metric_sets R X=>val j)
    (fun j=>c (val j)) (borel_caratheodory_measure c) (fun _=>1) A=borel_caratheodory_measure c A.
Proof.
move=> hD hden; apply/eqP; rewrite eq_le
  (@weighted_borel_indicator_lower_bound_all_sets R X c hc hw D A hD hden) andbT.
rewrite weighted_restriction_measureE.
exact: (@weighted_indicator_limit_ordinary_bound R X _ (fun j : @borel_metric_sets R X=>val j)
  (fun j=>c (val j)) (borel_caratheodory_measure c) A (borel_caratheodory_specification c)
  (fun j=>@borel_cover_cost_nonnegative R X c hc (val j) (set_valP j))).
Qed.
