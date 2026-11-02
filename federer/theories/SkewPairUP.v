(** Federer (1969), 1.7.3, pp. 29-30: the nonnegative coefficient and
    oriented orthonormal pair for a two-dimensional invariant piece. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_skew_pair]: Federer 1.7.3, pp. 29-30,
    supporting two-dimensional normal form: an oriented orthonormal
    pair x,y with f(x)=lambda*y and f(y)=-lambda*x, where lambda
    is nonnegative. The specification allows lambda zero, as in Federer. *)
Record is_skew_pair (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (f : {linear V -> V}) (x y : V) (lambda : R) : Prop := {
  skew_pair_nonnegative : 0 <= lambda;
  skew_pair_first_unit : B x x = 1;
  skew_pair_second_unit : B y y = 1;
  skew_pair_orthogonal : B x y = 0;
  skew_pair_first_image : f x = lambda *: y;
  skew_pair_second_image : f y = (-lambda) *: x
}.
