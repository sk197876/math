(** Federer (1969), 2.1.1(1)-(3), p. 52: elementary support properties of
    summation. Source context: NonnegativeSumUP.v. *)
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

(** Source for [nonnegative_sum_ext]: Federer 2.1.1(3),
    p. 52; supporting invariance under equality on the summation set. *)
Lemma nonnegative_sum_ext (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) :
  (forall x, A x -> f x = g x) -> nonnegative_sum A f = nonnegative_sum A g.
Proof.
move=> h; apply/eqP; rewrite eq_le; apply/andP; split;
  apply: nonnegative_sum_mono=> x hx; by rewrite (h x hx).
Qed.

(** Source for [nonnegative_sum_singleton]: Federer 2.1.1(1),
    p. 52; the sum over one point is its value. *)
Lemma nonnegative_sum_singleton (R : realType) (I : choiceType)
    (f : I -> \bar R) a : 0 <= f a -> nonnegative_sum [set a] f = f a.
Proof.
move=> ha.
have hs : [set a] = [set x | x \in [fset a]].
  apply/seteqP; split=> x; [move=> ->; exact: fset11|by move=> /fset1P->].
rewrite hs nonnegative_sum_finite ?big_seq_fset1 //.
by move=> x /fset1P->.
Qed.

(** Source for [nonnegative_sum_single_support]: Federer
    2.1.1(1), p. 52, and sentence after (4); the single-support
    rule remains true on an infinite summation set. *)
Lemma nonnegative_sum_single_support (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) a : A a -> 0 <= f a ->
  (forall x, A x -> x != a -> f x = 0) -> nonnegative_sum A f = f a.
Proof.
move=> ha h0 hz; apply/eqP; rewrite eq_le (nonnegative_sum_term _ ha) andbT.
apply: nonnegative_sum_least=> B hB; have [hab|hab] := boolP (a \in B).
- rewrite (big_fsetD1 _ hab) /=.
  have he : (\sum_(x <- (B `\ a)%fset) f x) = 0.
    rewrite big_seq; apply: big1=> x; rewrite !inE => /andP[hxa hx]; exact: hz (hB x hx) hxa.
  by rewrite he adde0.
- have he : (\sum_(x <- B) f x) = 0.
    rewrite big_seq; apply: big1=> x hx; apply: hz (hB x hx) _.
    apply/negP=> /eqP hxa; by rewrite hxa (negbTE hab) in hx.
  by rewrite he.
Qed.

(** Source for [nonnegative_sum_zero_iff]: Federer 2.1.1(3), p. 52,
    consequence. *)
Lemma nonnegative_sum_zero_iff (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  (forall x, A x -> 0 <= f x) ->
  (nonnegative_sum A f = 0 <-> forall x, A x -> f x = 0).
Proof.
move=> h0; split; last exact: nonnegative_sum_zero.
move=> hs x hx; apply/eqP; rewrite eq_le (h0 x hx) andbT.
by have := nonnegative_sum_term f hx; rewrite hs.
Qed.
