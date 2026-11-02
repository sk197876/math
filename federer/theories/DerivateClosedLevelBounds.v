(** The endpoint bounds on geometric levels in Federer (1969), 2.9.7, p.
    156. Derive closed derivative-level comparisons from the strict
    corollary 2.9.4, p. 154, by applying it at t*c or c/t and letting t
    decrease to one. These supporting lemmas retain the original M and
    partial graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureDerivates PartialFunctionUP
  CoveringRelationLimits MeasureUP MeasureBasic AbsoluteContinuousPart AbsoluteContinuousPartBasic
  DerivationComparison ExtendedGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivate_closed_lower_level_bound]: supporting
    upper mass bound on geometric derivative levels in
    Federer 2.9.7, p. 156. If defined
    values on A are at most positive c, then
    psi_phi(A)<=c phi(A), including infinite masses. *)
Lemma derivate_closed_lower_level_bound (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A (c : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> (0<c)%R ->
  (forall x, A x -> exists y, partial_function_graph (measure_derivate psi phi V) x y /\ y<=c%:E) ->
  measure_continuous_part psi phi A<=c%:E*phi A.
Proof.
move=> hc hp hcp hA.
have hm := derivation_measure_law (derivation_context_measure hc).
apply: extended_geometric_squeeze.
- apply: mule_ge0; [by rewrite lee_fin; exact: ltW hcp|exact (@measure_nonnegative R X phi hm A)].
- move=> t ht.
  have ht0 : (0<t)%R := lt_trans (@ltr01 R) ht.
  have hct : (0<c*t)%R := mulr_gt0 hcp ht0.
  have hcct : (c<c*t)%R by rewrite -{1}[c]mulr1 ltr_pM2l.
  have hbound := @derivation_lower_comparison R X phi psi V A (c*t)%R hc hp hct.
  have hlevels x : A x -> covering_lower_limit V (measure_ratio_function psi phi) x<(c*t)%:E.
    move=> hx; have [y [[_ [_ hl]] hyc]] := hA x hx.
    rewrite hl; apply: le_lt_trans hyc _; by rewrite lte_fin.
  have hh := hbound hlevels.
  rewrite muleA -EFinM (mulrC t c); exact hh.
Qed.

(** Source for [derivate_closed_upper_level_bound]: supporting
    lower mass bound on geometric derivative levels in
    Federer 2.9.7, p. 156. If defined
    values on A are at least positive c, then
    c phi(A)<=psi_phi(A). The proof uses c/t<c
    before removing the multiplicative error. *)
Lemma derivate_closed_upper_level_bound (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A (c : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> (0<c)%R ->
  (forall x, A x -> exists y, partial_function_graph (measure_derivate psi phi V) x y /\ c%:E<=y) ->
  c%:E*phi A<=measure_continuous_part psi phi A.
Proof.
move=> hc hp hcp hA.
have hm := derivation_measure_law (derivation_context_measure hc).
apply: extended_geometric_squeeze.
- exact (@continuous_part_nonnegative R X phi psi _ (derivation_measure_law hp)
    (measure_continuous_part_specification psi phi) A).
- move=> t ht.
  have ht0 : (0<t)%R := lt_trans (@ltr01 R) ht.
  have hct : (0<c/t)%R by rewrite divr_gt0.
  have hctc : (c/t<c)%R by rewrite ltr_pdivrMr // -{1}[c]mulr1 ltr_pM2l.
  have hlevels x : A x -> (c/t)%R%:E<covering_upper_limit V (measure_ratio_function psi phi) x.
    move=> hx; have [y [[_ [hu _]] hcy]] := hA x hx.
    rewrite hu; apply: lt_le_trans _ hcy; by rewrite lte_fin.
  have hh := @derivation_upper_comparison R X phi psi V A (c/t)%R hc hp hct hlevels.
  have htE : 0<=t%:E by rewrite lee_fin; exact: ltW ht0.
  have hmul := @lee_wpmul2l R t%:E htE _ _ hh.
  have htc : (t*(c/t)=c)%R by rewrite mulrCA mulfV ?gt_eqF // mulr1.
  by rewrite muleA -EFinM htc in hmul.
Qed.
