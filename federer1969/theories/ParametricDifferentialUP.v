(** Federer (1969), 3.1.22, p. 235, condition (3):
    the relative differential is the coordinate derivative transported
    by the inverse of the parametrisation derivative. *)
From mathcomp Require Import all_boot all_algebra.
From Federer Require Import Hom PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_parametric_differential_restriction]: condition (3)
    of Federer 3.1.22, p. 235, expressed by its exact
    graph. The displayed inverse of Dpsi is restricted to its
    tangent-space range: L(Jw)=Qw. No value is supplied outside
    that range, and no unproved invertibility is assumed here. *)
Definition is_parametric_differential_restriction (R:fieldType) (X Z Y:lmodType R)
    (J:Hom Z X) (Q:Hom Z Y) (L:partial_function X Y) :=
  forall v y,partial_function_graph L v y <->
    exists w,J w=v /\ Q w=y.
