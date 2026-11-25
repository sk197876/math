(** Federer (1969), 2.3.2, p. 74: pairing extended- real measurable
    functions for the numerical operations. The countable bases come from
    rational interval endpoints, with unbounded intervals covering both
    infinities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPair MeasureUP MeasurableFunctionUP
  CountableOrderIntervals OrderFamilyIntervalOpen ExtendedRealOrderTopology MeasurablePairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measurable_extended_function_pair]: supporting extended-real
    pair for the numerical closure assertions in Federer 2.3.2, p. 74 The
    domain is the exact intersection. *)
Theorem measurable_extended_function_pair (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_function_pair f g).
Proof.
move=> hf hg.
pose d := fun q : rat => (ratr q : R)%:E.
apply: (@measurable_partial_function_pair R X (extended_real_line R) (extended_real_line R)
  [the countType of ((option rat * option rat)%type : Type)]
  [the countType of ((option rat * option rat)%type : Type)] mu hm f g
  (@order_family_interval _ [the orderType _ of \bar R] rat d)
  (@order_family_interval _ [the orderType _ of \bar R] rat d) _ _ _ _ hf hg).
- move=> c; exact: order_family_interval_open.
- exact: (@order_family_intervals_refine _ [the orderTopologicalType _ of order_topology (\bar R)]
    rat d (@extended_rationals_order_dense R)).
- move=> c; exact: order_family_interval_open.
- exact: (@order_family_intervals_refine _ [the orderTopologicalType _ of order_topology (\bar R)]
    rat d (@extended_rationals_order_dense R)).
Qed.
