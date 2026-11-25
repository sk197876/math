(** Finite scalar polynomial recovery supporting Federer
    (1969), 3.2.45, p. 279.
    The coefficient and root laws are those
    already proved for 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_finite_power_evaluation]: independent
    finite polynomial-value specification supporting the
    coefficient comparison in Federer 3.2.45,
    p. 279. The original finite coefficient
    list is evaluated at the distinct positive
    scalars 1,...,N+1. These laws precede
    both the linear witness and its inverse;
    no coefficient recovery is assumed. *)
Definition is_finite_power_evaluation (R : realType) N
    (E : {linear R_n R N.+1 -> R_n R N.+1}) : Prop :=
  forall c j, E c j=\sum_(i : 'I_N.+1) c i*((j.+1)%:R)^+i.
