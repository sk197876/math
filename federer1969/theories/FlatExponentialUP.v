(** Federer (1969), 3.1.11, p. 223:
    the scalar function exp(-x^-2) for x>0
    and zero for x<= 0 is specified by
    those value laws. Existence and smoothness
    are proved before the implementation is sealed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_flat_exponential]:
    the displayed smooth-function example in
    Federer 3.1.11, p. 223. The
    two branch laws determine the function
    without exposing its implementation. *)
Record is_flat_exponential (R : realType) (f : R->R) : Prop := {
  (** Source for [flat_exponential_positive_value]:
      the positive branch is exp(-x^-2),
      Federer 3.1.11, p. 223. *)
  flat_exponential_positive_value : forall x, 0<x ->
    f x=RealExponential.exponential (-((x^-1)^+2));
  (** Source for [flat_exponential_nonpositive_value]:
      the function is zero on the
      nonpositive half-line, Federer 3.1.11, p. 223. *)
  flat_exponential_nonpositive_value : forall x, x<= 0 -> f x= 0
}.
