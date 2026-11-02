(** Federer (1969), 2.10.23, p. 186: the final measure of a Suslin set is
    the supremum of the masses of its compact subsets. The proof uses
    2.10.22 and the coordinate pruning of 2.2.12 exactly as explained in
    CompactCostSuslinApproximation.v, then radial exhaustion from 2.10.20.
    The working erratum has no correction to this corollary. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile CompactGeneratorCostUP CompactCostSuslinBounds
  LipschitzFunctionCompact SuslinSetUP CaratheodoryLimitUP CaratheodoryLimitMeasure
  MeasureUP MeasureBasic ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_subset_mass_values]: direct
    family on the right of the equality in
    2.10.23, p. 186. Compact subsets include
    the empty set even though the generating family
    consists only of nonempty compact sets. *)
Definition compact_subset_mass_values (R : realType) (X : topologicalType)
    (psi : set X -> \bar R) (S : set X) : set (\bar R) :=
  [set b | exists C, compact C /\ C `<=` S /\ b=psi C].

(** Source for [federer_2_10_23_supremum]: direct
    supremum laws for 2.10.23, p. 186.
    No finite mass, local finiteness or measurability
    premise is added to the printed hypotheses. *)
Theorem federer_2_10_23_supremum (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (psi : set X -> \bar R) (S : set X) :
  metric_boundedly_compact X ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) psi ->
  is_suslin_set R S -> is_extended_real_supremum (compact_subset_mass_values psi S) (psi S).
Proof.
move=> hX hpsi hS.
have hc0 C : 0<=(c C)%:E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := caratheodory_limit_is_measure hpsi hc0.
constructor.
- move=> b [C [hC [hCS ->]]]; exact: (@measure_mono R X psi hm C S hCS).
- move=> b hb; case: b hb=> [r| |] hb; [|exact: leey|].
  + apply: (@compact_cost_suslin_mass_bound R X c hc psi S r hX hpsi hS)=> C hC hCS.
    apply: hb; exists C; by split=> //; split.
  + have hzero : compact_subset_mass_values psi S 0.
      exists set0; split; first exact: compact0.
      split; first by move=> x [].
      exact: esym (measure_empty hm).
    have hh := hb 0 hzero.
    have hbad := lt_le_trans (ltNyr (0%R : R)) hh; by rewrite ltxx in hbad.
Qed.

(** Source for [federer_2_10_23]: direct displayed
    equality in 2.10.23, p. 186, using
    the project's sealed extended-real supremum. Empty
    Suslin sets and infinite final values are included. *)
Theorem federer_2_10_23 (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (psi : set X -> \bar R) (S : set X) :
  metric_boundedly_compact X ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) psi ->
  is_suslin_set R S -> psi S=extended_real_sup (compact_subset_mass_values psi S).
Proof.
move=> hX hpsi hS.
have hs := @federer_2_10_23_supremum R X c hc psi S hX hpsi hS.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (extended_real_supremum_least hs)=> b hb; exact: extended_real_sup_upper hb.
- apply: extended_real_sup_least=> b hb; exact: (@extended_real_supremum_upper R (compact_subset_mass_values psi S) (psi S) hs b hb).
Qed.
