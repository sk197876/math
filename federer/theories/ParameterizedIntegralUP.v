(** Federer (1969), 2.6.2(4), p. 115: the inner integral is a function of
    the remaining variable, defined exactly where that inner function is
    integrable. This specification retains the partial-domain convention of
    2.4.2, p. 81. its proof leaves (4) as an exercise on p. 239. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_parameterized_integral]: abstract graph
    specification of the inner integral in Federer 2.6.2(4),
    p. 115. There is a value exactly when the
    corresponding integrand has that actual integral; no default
    value is assigned to a nonintegrable section. *)
Definition is_parameterized_integral (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :=
  forall x a, partial_function_graph g x a <-> is_measure_integral mu (f x) a.

(** Source for [parameterized_integral_unique_graph]: supporting
    uniqueness of the inner-integral graph for Federer 2.6.2(4),
    p. 115, under the integral convention of 2.4.2, p. 81. *)
Lemma parameterized_integral_unique_graph (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  is_parameterized_integral mu f g -> is_parameterized_integral mu f h ->
  forall x a, partial_function_graph g x a <-> partial_function_graph h x a.
Proof. move=> hg hh x a; exact: iff_trans (hg x a) (iff_sym (hh x a)). Qed.
