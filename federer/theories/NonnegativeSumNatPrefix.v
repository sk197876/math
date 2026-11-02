(** Federer (1969), 2.1.3(3), p. 55: supporting initial finite sums in the
    additivity proof. Summation is the abstract operator of 2.1.1(1)-(3), p.
    52. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_nat_prefix_zero]: Federer
    2.1.1, p. 52, empty-sum convention; supporting zero initial sum
    for the induction in 2.1.3(3), p. 55. *)
Lemma nonnegative_sum_nat_prefix_zero (R : realType) (f : nat -> \bar R) :
  nonnegative_sum [set k | (k < 0)%N] f = 0.
Proof.
have he : [set k | (k < 0)%N] = (@set0 nat).
  by apply/seteqP; split=> [k hk|k []]; rewrite /= ltn0 in hk.
by rewrite he nonnegative_sum_empty.
Qed.

(** Source for [nonnegative_sum_nat_prefix_succ]: Federer
    2.1.3(3), p. 55, finite-sum induction; add the next nonnegative
    summand to the preceding initial sum. *)
Lemma nonnegative_sum_nat_prefix_succ (R : realType) (f : nat -> \bar R) n :
  (forall k, 0 <= f k) ->
  nonnegative_sum [set k | (k < n.+1)%N] f =
    nonnegative_sum [set k | (k < n)%N] f + f n.
Proof.
move=> hf.
have hi : [set k | (k < n.+1)%N] `&` [set n] = [set n].
  apply/seteqP; split=> [k [_ he]|k he] //; split=> //.
  by rewrite /= -he ltnSn.
have hd : [set k | (k < n.+1)%N] `\` [set n] = [set k | (k < n)%N].
  apply/seteqP; split.
  - move=> k [hk hn].
    have hne : k != n by apply/eqP=> he; apply: hn; symmetry.
    by rewrite /= ltn_neqAle hne; move: hk; rewrite /= ltnS.
  - move=> k hk; split; first exact: ltn_trans hk (ltnSn n).
    move=> he; by move: hk; rewrite /= -he ltnn.
rewrite (@nonnegative_sum_split R _ [set k | (k < n.+1)%N] [set n] f) //.
by rewrite hi hd nonnegative_sum_singleton // addeC.
Qed.
