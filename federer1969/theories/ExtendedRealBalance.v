(** Federer (1969), 2.1.1(4)-(7), pp. 52-53: arithmetic supporting
    subtraction of the positive and negative variations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_difference_balance]: Federer
    2.1.1(7), p. 53, supporting cancellation principle: if
    p+v=n+u, p<=u, n<=v, and u-v is defined, then p-n=u-v,
    with equality understood for the partial differences. *)
Lemma nonnegative_difference_balance (R : realType) (p n u v : \bar R) :
  0 <= p -> 0 <= n -> 0 <= u -> 0 <= v -> p <= u -> n <= v ->
  p + v = n + u -> (u < +oo) || (v < +oo) ->
  extended_subtract p n = extended_subtract u v.
Proof.
case: p=> [p| |]; case: n=> [n| |]; case: u=> [u| |]; case: v=> [v| |] //=
  hp hn hu hv hpu hnv he hd;
  rewrite /extended_subtract /extended_add /adde_def /= ?eqxx //.
congr (Some _); congr EFin.
have he' : (p + v = n + u)%R by move: he=> [he].
apply/eqP; rewrite subr_eq addrAC eq_sym subr_eq addrC.
exact/eqP/esym.
Qed.
