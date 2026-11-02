(** Federer (1969), 2.3.2, p. 74: real-valued numerical operations, using
    (5) to pair the inputs on their common domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionPair MeasureUP
  MeasurableFunctionUP CountableOrderIntervals OrderFamilyIntervalOpen MeasurablePairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [real_rationals_order_dense]: scalar order-density
    background supporting the numerical operations in Federer 2.3.2,
    p. 74, and the dense-ray criteria on p. 73. *)
Lemma real_rationals_order_dense (R : realType) :
  is_order_dense_family (fun q : rat => (ratr q : R)).
Proof.
move=> a b hab; have [q hq] := rat_in_itvoo hab.
exists q; by move: hq; rewrite interval.in_itv /= => /andP.
Qed.

(** Source for [measurable_real_function_pair]: supporting
    real-valued binary case of Federer 2.3.2(5), p. 73,
    used in the ordinary arithmetic assertions on p. 74. *)
Theorem measurable_real_function_pair (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_function_pair f g).
Proof.
move=> hf hg; pose d := fun q : rat => (ratr q : R).
refine (@measurable_partial_function_pair R X
  [the topologicalType of real_line_metric R] [the topologicalType of real_line_metric R]
  [the countType of ((option rat * option rat)%type : Type)]
  [the countType of ((option rat * option rat)%type : Type)] mu hm f g
  (@order_family_interval _ [the orderType _ of (R : Type)] rat d)
  (@order_family_interval _ [the orderType _ of (R : Type)] rat d) _ _ _ _ hf hg).
- move=> c; exact: (@order_family_interval_open _ [the orderTopologicalType _ of R^o] rat d c).
- exact: (@order_family_intervals_refine _ [the orderTopologicalType _ of R^o]
    rat d (@real_rationals_order_dense R)).
- move=> c; exact: (@order_family_interval_open _ [the orderTopologicalType _ of R^o] rat d c).
- exact: (@order_family_intervals_refine _ [the orderTopologicalType _ of R^o]
    rat d (@real_rationals_order_dense R)).
Qed.
