(** Off-set upper-density step supporting Federer (1969), 2.10.19(4), p.
    181. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryWeakEnlargementUP
  WeakCaratheodoryOffSetDensity WeakCaratheodoryDensityQuotient CaratheodoryZeroDensityLimit
  CaratheodoryDensityUpperBound CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weak_caratheodory_off_set_upper_density]: supporting
    off-set nullity for 2.10.19(4), p. 181,
    retaining finite measurable A. The auxiliary corrected
    covering limsup is at most zero almost everywhere;
    positive-radius density will supply its own nonnegative
    lower bound when transferring to the actual conclusion. *)
Theorem weak_caratheodory_off_set_upper_density (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (A : set X) :
  is_weak_caratheodory_enlargement F c E k -> is_measure mu -> is_borel_regular_measure mu ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  measure_measurable mu A -> mu A < +oo ->
  measure_almost_everywhere_on psi (~` A) [set x |
    covering_upper_limit (caratheodory_family_relation F)
      (caratheodory_measure_cost_ratio (measure_restrict mu A) c) x<=0].
Proof.
move=> hE hm hr hpsi hclosed hmeas hA hAf.
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: (@weak_enlargement_cost_nonnegative R X F c E k hE _ (set_valP j)).
have hpm := caratheodory_limit_is_measure hpsi hcost.
pose L x := covering_upper_limit (caratheodory_family_relation F)
  (caratheodory_measure_cost_ratio (measure_restrict mu A) c) x.
pose B n := [set x | ~ A x /\ (((n.+1)%:R : R)^-1)%:E<L x].
have hB n : psi (B n)=0.
  apply: (@weak_caratheodory_off_set_density_level_null R X F c mu psi E k A _ hE hm hr
    hpsi hclosed hmeas hA hAf).
  by rewrite invr_gt0 ltr0n.
have hN : psi (\bigcup_n B n)=0.
  exact: (@measure_null_countable_union R X [the choiceType of (nat : Type)] psi hpm
    setT B (countableP _) (fun n _ => hB n)).
apply: (@measure_null_subset R X psi hpm _ (\bigcup_n B n))=> // x [hnA hn].
have hp : 0<L x by rewrite ltNge; apply/negP.
have [n hsmall] := positive_extended_reciprocal_below hp.
exists n=> //; by split.
Qed.
