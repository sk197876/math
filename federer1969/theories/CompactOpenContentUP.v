(** Federer (1969), 2.5.14, p. 107, definition of alpha(V) as the supremum
    of lambda(f) for positive compactly supported continuous functions
    bounded by one and supported in V. The erratum p. 2, book p. 107 line
    24, corrects the measure symbol in the ensuing comparison with the
    associated measure; it does not change the supremum definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_compact_open_test_function]: the three constraints on f
    in the definition of alpha(V) in Federer 2.5.14, p. 107 The support is
    required to lie in V. *)
Definition is_compact_open_test_function (R : realType) (X : topologicalType)
    (V : set X) (f : X -> R) :=
  compactly_supported_continuous_functions f /\
  (forall x, (0 <= f x <= 1)%R) /\ real_function_support f `<=` V.

(** Source for [is_compact_open_content]: abstract supremum laws for alpha
    in Federer 2.5.14, p. 107 Only open sets are constrained, as in the
    book; no implementation is prescribed. *)
Definition is_compact_open_content (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R) :=
  forall V, open V -> is_extended_real_supremum
    [set c | exists f, is_compact_open_test_function V f /\ c=(A f)%:E] (a V).
