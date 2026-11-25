(** Federer (1969), 2.10.24(1), p. 187, with the literal strict enlargement
    hypotheses of 2.10.18, p. 180. The public theorem follows the proved
    weak-cost equality; this implication is separate so no printed
    hypothesis or arithmetic convention is silently changed. Source
    editions: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralBounds
  CaratheodoryLimitUP CaratheodoryEnlargementUP CaratheodoryEnlargementGrowth
  CaratheodoryWeakEnlargementUP DiameterEnlargements WeightedMetricLimit WeightedMetricLimitUP
  WeightedSigmaFiniteEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [strict_caratheodory_enlargement_is_weak]:
    supporting implication from the strict cost assumptions
    of 2.10.18, p. 180, to the containing-generator
    laws used for 2.10.24(1), p. 187.
    It only forgets positivity and cost finiteness. *)
Lemma strict_caratheodory_enlargement_is_weak (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X) (k : R) :
  is_caratheodory_enlargement F c E k -> is_weak_caratheodory_enlargement F c E k.
Proof.
move=> h; constructor.
- exact: caratheodory_enlargement_constant_positive h.
- move=> S hS; exact: ltW (caratheodory_enlargement_cost_positive h hS).
- exact: caratheodory_enlargement_member h.
- exact: caratheodory_enlargement_contains h.
- exact: caratheodory_enlargement_diameter h.
- exact: caratheodory_enlargement_cost h.
Qed.

(** Source for [federer_2_10_24_1]: direct first equality
    assertion of 2.10.24, p. 187. The printed
    strict growth and domain of the displayed enlargement
    are explicit, as in 2.10.18. Countably many
    finite-measure sets cover only the positive support;
    f itself may be nonmeasurable and infinite-valued. *)
Theorem federer_2_10_24_1 (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R) (eta : R)
    (f : X -> extended_real_line R) (A : nat -> set X) :
  (forall S, F S -> 0<=c S) ->
  (forall S, F S -> F (diameter_enlargement F S)) ->
  (forall S, F S -> c (diameter_enlargement F S)<eta%:E*c S /\ eta%:E*c S< +oo) ->
  (forall S, F S -> closed S) ->
  is_caratheodory_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi ->
  (forall x, 0<=f x) -> (forall n, psi (A n)< +oo) ->
  [set x | 0<f x] `<=` \bigcup_n A n ->
  weighted_metric_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi f=
    measure_upper_integral psi (partial_function_total f).
Proof.
move=> hc hF hg hclosed hp hf hAfin hcover.
have hE := strict_caratheodory_enlargement_is_weak (federer_caratheodory_enlargement_laws hc hF hg).
exact: (@weighted_metric_limit_sigma_finite_equality R X F c psi _ _ _ f A hE hp
  (weighted_metric_limit_specification _ _ _) hclosed hf hAfin hcover).
Qed.
