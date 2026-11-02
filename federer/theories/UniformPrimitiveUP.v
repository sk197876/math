(** Supporting elementary-calculus step in Federer (1969), 2.6.3(2), pp.
    117–118, which refers to the fundamental theorem in 2.9.20. We state the
    finite-increment law sufficient for the Riemann-sum proof. This is
    supporting infrastructure, not a definition attributed to Federer or a
    new project axiom. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_uniform_primitive_on]: supporting abstract
    finite-increment specification for the elementary integral evaluations
    in Federer 2.6.3(2), pp. 117–118 On small intervals every tagged
    first-order increment approximates the primitive increment with error at
    most epsilon times the interval length. *)
Definition is_uniform_primitive_on (R : realType) (f F : R -> R) (a b : R) : Prop :=
  forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall s u t : R, a <= s -> s <= u -> u <= t -> t <= b -> t-s < d ->
      `|F t-F s-f u*(t-s)| <= e*(t-s).
