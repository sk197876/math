(** Federer (1969), 2.10.24(2), p. 188: countable weak-level bound from
    finite disjoint layers and continuity below of the approximating
    measure. The finite budget form is enough for the ensuing finite-limit
    argument. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology ring.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP CaratheodoryWeakEnlargementUP
  IncreasingProjectionLoss NonnegativeSum WeightedMetricEnvelopeUP FiniteWeightedEnlargementBound CountableWeightedLevels.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_weighted_enlargement_bound]: supporting
    countable-family estimate in 2.10.24(2), p. 188.
    Continuity below is an input supplied by 2.10.22;
    the budget C and threshold t are finite real
    numbers with t>0. Zero weights are allowed. *)
Theorem countable_weighted_enlargement_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X) (k d : R)
    (nu : set X -> \bar R) (G : set (set_type F)) (u : set_type F -> R) (t C : R) :
  is_weak_caratheodory_enlargement F c E k ->
  (forall S, F S -> S<>set0) -> (forall j, G j -> c (val j)< +oo) ->
  is_metric_scale_envelope (fun j : set_type F=>val j) (fun j=>c (val j)) (k*d)%R%:E nu ->
  has_increasing_set_continuity nu -> countable G ->
  (forall j, G j -> extended_metric_diameter (val j)<=d%:E) ->
  (forall j, G j -> (0<=u j)%R) -> (0<t)%R ->
  weighted_generator_cost (fun j : set_type F=>c (val j)) G u<=C%:E ->
  nu [set x | t%:E<weighted_generator_sum (fun j : set_type F=>val j) G u x]<=(k*C/t)%R%:E.
Proof.
move=> hE hne hcf hn hcont hG hd hu ht hbudget.
pose J := [the choiceType of set_type F].
apply: (@countable_weighted_level_finite_reduction R X J (fun j=>val j) G u nu t%:E (k*C/t)%R%:E hcont hG hu)=> P hPG.
pose A := [set x | t%:E<weighted_generator_sum (fun j : J=>val j) [set` P] u x].
have hbound := @finite_weighted_enlargement_bound R X F c E k d nu P u A t hE hne (fun j hj=>hcf j (hPG j hj)) hn
  (fun j hj=>hd j (hPG j hj)) (fun j hj=>hu j (hPG j hj)) ht (fun x hx=>ltW hx).
have hsubset : weighted_generator_cost (fun j : J=>c (val j)) [set` P] u<=C%:E.
  apply: le_trans _ hbudget; exact: nonnegative_sum_subset hPG.
have hk0 : 0<=k%:E by rewrite lee_fin; exact: ltW (weak_enlargement_constant_positive hE).
have hh := le_trans hbound (lee_wpmul2l hk0 hsubset).
have htE : 0<t%:E by rewrite lte_fin.
have htf : t%:E \is a fin_num by rewrite fin_numE.
have htne : (t!=0)%R by rewrite gt_eqF.
have heq : (t*(k*C/t))%R=(k*C)%R by rewrite mulrC divfK.
rewrite -(@lee_pmul2l R t%:E htf htE) -EFinM heq EFinM; exact hh.
Qed.
