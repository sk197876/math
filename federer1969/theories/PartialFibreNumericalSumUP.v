(** Federer (1969), 3.2.3(2), p. 243: abstract graph laws for the signed sum over a fibre, with the exact original input domain and numerical summation convention of 2.1.1(4), p. 52. Undefined summands and undefined differences have no assigned values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_partial_fibre_numerical_sum]: the inner
    sum of Federer 3.2.3(2), p. 243, with summation as
    in 2.1.1(4), p. 52. Every point of the fibre must
    belong to the original function's domain; the signed
    sum must be defined. Neither condition receives a default. *)
Definition is_partial_fibre_numerical_sum (R:realType) (X:choiceType) (Y:Type)
    (p:X->Y) (u:partial_function X (extended_real_line R))
    (v:partial_function Y (extended_real_line R)):=
  forall y z,partial_function_graph v y z <-> exists w:X->\bar R,
    (forall x,p x=y -> partial_function_graph u x (w x)) /\
    numerical_sum [set x|p x=y] w=Some z.
