(** Federer (1969), 1.10.5, p. 48: supporting continuity of
    finite-dimensional norm functions in the compactness argument. Source
    context and seminorm conventions: RealNormUP.v. These difference
    estimates follow from the supplied triangle inequality alone. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Difference.
Variable R : realFieldType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.

(** Source for [real_seminorm_difference_le]: Federer 1.10.5,
    p. 48, supporting consequence of the triangle inequality:
    the difference of two seminorm values is at most the seminorm
    of the difference of their arguments. *)
Lemma real_seminorm_difference_le x y : N x-N y <= N (x-y).
Proof.
rewrite lerBlDr; have hh := real_seminorm_triangle hN (x-y) y.
by rewrite subrK in hh.
Qed.

(** Source for [real_seminorm_absolute_difference]: Federer 1.10.5,
    p. 48, supporting Lipschitz estimate for a seminorm function.
    This supplies continuity once the seminorm has a Euclidean upper bound. *)
Lemma real_seminorm_absolute_difference x y : `|N x-N y| <= N (x-y).
Proof.
rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB (real_seminorm_subtract hN).
  exact: real_seminorm_difference_le.
- exact: real_seminorm_difference_le.
Qed.
End Difference.
