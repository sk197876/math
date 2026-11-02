(** Federer (1969), 2.1.5, p. 57: supporting covering argument for the three
    irregular-measure examples. Numerical summation uses 2.1.1(1),(3), p.
    52. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_two_term_bound]: Federer
    2.1.1(3), p. 52, finite-subsum bound for two distinct indices;
    supporting the covering proofs of the examples in 2.1.5, p. 57. *)
Lemma nonnegative_sum_two_term_bound (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) x y :
  A x -> A y -> x != y -> f x + f y <= nonnegative_sum A f.
Proof.
move=> hx hy hxy.
have hb := @nonnegative_sum_upper R I A f [fset x; y].
rewrite big_fsetU1 in hb; last by rewrite inE.
rewrite big_seq_fset1 in hb; apply: hb=> z.
by rewrite !inE=> /orP[/eqP->|/eqP->].
Qed.
