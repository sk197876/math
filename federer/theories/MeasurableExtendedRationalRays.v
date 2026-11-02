(** Federer (1969), 2.3.2(2), p. 73: the four rational-ray tests for
    extended-real measurable functions. The scalar line includes both
    infinities and uses its order topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP
  MeasurableFunctionUP ExtendedRealOrderTopology MeasurableOrderRays MeasurableOrderRayVariants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_extended_rational_lower_rays_iff]: direct
    displayed rational strict lower-ray criterion following Federer
    2.3.2(2), p. 73. *)
Theorem measurable_extended_rational_lower_rays_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> forall q : rat,
    measure_measurable mu (partial_function_preimage f [set y | y < (ratr q : R)%:E])).
Proof.
move=> hd; exact: (@measurable_order_dense_rays_iff R X _
  [the orderTopologicalType _ of order_topology (\bar R)] [the countType of (rat : Type)] mu hm f _
  (@extended_rationals_order_dense R) hd).
Qed.

(** Source for [measurable_extended_rational_closed_lower_rays_iff]: direct
    replacement of the strict comparison by less-or-equal in Federer
    2.3.2(2), p. 73 *)
Theorem measurable_extended_rational_closed_lower_rays_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> forall q : rat,
    measure_measurable mu (partial_function_preimage f [set y | y <= (ratr q : R)%:E])).
Proof.
move=> hd; exact: (@measurable_order_dense_closed_lower_rays_iff R X _
  [the orderTopologicalType _ of order_topology (\bar R)] [the countType of (rat : Type)] mu hm f _
  (@extended_rationals_order_dense R) hd).
Qed.

(** Source for [measurable_extended_rational_upper_rays_iff]: direct strict
    upper-ray alternative in Federer 2.3.2(2), p. 73 *)
Theorem measurable_extended_rational_upper_rays_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> forall q : rat,
    measure_measurable mu (partial_function_preimage f [set y | (ratr q : R)%:E < y])).
Proof.
move=> hd; exact: (@measurable_order_dense_upper_rays_iff R X _
  [the orderTopologicalType _ of order_topology (\bar R)] [the countType of (rat : Type)] mu hm f _
  (@extended_rationals_order_dense R) hd).
Qed.

(** Source for [measurable_extended_rational_closed_upper_rays_iff]: direct
    greater-or-equal alternative in Federer 2.3.2(2), p. 73 *)
Theorem measurable_extended_rational_closed_upper_rays_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> forall q : rat,
    measure_measurable mu (partial_function_preimage f [set y | (ratr q : R)%:E <= y])).
Proof.
move=> hd; exact: (@measurable_order_dense_closed_upper_rays_iff R X _
  [the orderTopologicalType _ of order_topology (\bar R)] [the countType of (rat : Type)] mu hm f _
  (@extended_rationals_order_dense R) hd).
Qed.
