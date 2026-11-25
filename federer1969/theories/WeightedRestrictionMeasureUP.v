(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting abstract
    cutoff-supremum specification for the measure associated with
    restricting a fixed input. Define its laws before proving existence and
    sealing a witness. This auxiliary object expands the use of 2.10.8, p.
    175, and is not separately stated in the book. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_function_restriction]: supporting total
    zero extension of a restricted nonnegative function,
    using the restriction convention of 2.4.3(1), p. 81,
    for the final-paragraph argument in 2.10.24, p. 188. *)
Definition weighted_function_restriction (R : realType) (X : choiceType)
    (f : X -> \bar R) (A : set X) x := if x \in A then f x else 0.

(** Source for [is_weighted_restriction_measure]: supporting
    abstract supremum laws for the restricted weighted
    functional used in 2.10.24, p. 188. Each target's
    value is the least upper bound of the actual
    positive-cutoff weighted infima for its restriction.
    Measure laws are consequences proved separately. *)
Record is_weighted_restriction_measure (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (nu : set X -> \bar R) : Prop := {
  (** Source for [weighted_restriction_upper]: supporting upper-bound
      law for the auxiliary restricted limit in 2.10.24,
      p. 188, from its positive-cutoff supremum convention. *)
  weighted_restriction_upper : forall A delta lambda, 0<delta ->
    is_weighted_metric_envelope S c psi delta lambda ->
    lambda (weighted_function_restriction f A)<=nu A;
  (** Source for [weighted_restriction_least]: supporting least-upper-
      bound law for the auxiliary restricted limit in
      2.10.24, p. 188. Infinite values are retained. *)
  weighted_restriction_least : forall A b,
    (forall delta lambda, 0<delta -> is_weighted_metric_envelope S c psi delta lambda ->
      lambda (weighted_function_restriction f A)<=b) -> nu A<=b
}.
