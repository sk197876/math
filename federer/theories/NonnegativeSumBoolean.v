(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_bool]: Federer 2.1.1(1),
    p. 52, finite summation; supporting two-set covering calculation
    for the measurability test in 2.1.2, p. 54. *)
Lemma nonnegative_sum_bool (R : realType) (f : bool -> \bar R) :
  (forall b, 0 <= f b) -> nonnegative_sum setT f = f true + f false.
Proof.
move=> hf.
have he : @setT bool = [set b | b \in [fset true; false]].
  by apply/seteqP; split=> [[] | b _] //=; rewrite !inE.
rewrite he nonnegative_sum_finite; last by move=> b _; exact: hf.
rewrite big_fsetU1; last by rewrite inE.
by rewrite big_seq_fset1.
Qed.
