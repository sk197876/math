(** Federer (1969), 2.4.15, p. 89: the general normed-space equality
    condition for Minkowski's inequality. This specification states the
    printed global coefficients and the conull common domain explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [minkowski_norm_proportion_locus]: direct pointwise norm
    identities in Federer 2.4.15, p. 89 The same pair of scalar coefficients
    is used throughout the locus. *)
Definition minkowski_norm_proportion_locus (R : realType) (X : Type)
    (V : lmodType R) (N : V -> R) (a b : R) (f g : partial_function X V) :=
  [set x | exists u v, partial_function_graph f x u /\ partial_function_graph g x v /\
    N u=a*N (u+v) /\ N v=b*N (u+v)].

(** Source for [is_minkowski_equality_condition]: direct specification of
    the general equality criterion in Federer 2.4.15, p. 89 The coefficients
    are nonnegative and sum to one; this specifies a property, not an extra
    axiom. *)
Definition is_minkowski_equality_condition (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (mu : set X -> \bar R) (f g : partial_function X V) :=
  exists a b : R, 0 <= a /\ 0 <= b /\ a+b = 1 /\
    measure_almost_everywhere mu (minkowski_norm_proportion_locus N a b f g).
