(** Federer (1969), 2.4.17, p. 90: convexity of the logarithmic norm as a
    function of reciprocal exponent. The same ordinary convex-function
    specification supports Jensen's inequality in 2.4.19, p. 91. The
    specification is independent of coordinates, topology and any
    construction of the convex domain or function. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_real_convex_function_on]: the convex-function
    condition in Federer 2.4.17, p. 90, and 2.4.19, p. 91:
    a convex domain and the inequality on every convex combination. *)
Definition is_real_convex_function_on (R : realFieldType) (V : lmodType R)
    (C : set V) (F : V -> R) :=
  is_inner_convex C /\ forall x y, C x -> C y -> forall t : R,
    0 <= t -> t <= 1 -> F ((1-t) *: x + t *: y) <= (1-t) * F x+t * F y.
