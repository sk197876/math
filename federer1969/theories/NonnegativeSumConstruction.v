(** Federer (1969), 2.1.1, pp. 52-53: numerical sums over arbitrary sets.
    Finite sets and extended-real scalar arithmetic are background; the
    arbitrary summation operator and its laws are developed here. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSumUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_exists]: Federer 2.1.1(3), p. 52; existence
    by taking the supremum of the finite subsums. This witness remains
    private; downstream proofs use the laws. *)
Theorem nonnegative_sum_exists (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) : exists c, is_nonnegative_sum A f c.
Proof.
pose S : set (\bar R) := fun t => exists B : {fset I},
  (forall x, x \in B -> A x) /\ t = \sum_(x <- B) f x.
exists (extended_real_sup S); constructor.
- move=> B hB; apply: extended_real_sup_upper; exists B; by split.
- move=> d hd; apply: extended_real_sup_least => t [B [hB ->]].
  exact: hd.
Qed.
