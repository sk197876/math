(** Federer (1969), 2.1.1, pp. 52-53: numerical sums over arbitrary sets.
    Finite sets and extended-real scalar arithmetic are background; the
    arbitrary summation operator and its laws are developed here. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSumUP NonnegativeSumSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum]: Federer 2.1.1(3), p. 52;
    public numerical sum, used on functions nonnegative on A. *)
Definition nonnegative_sum (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) := NonnegativeSum.value A f.

(** Source for [nonnegative_sum_upper]: Federer 2.1.1(3),
    p. 52; every finite subsum is at most the sum. *)
Lemma nonnegative_sum_upper (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) (B : {fset I}) :
  (forall x, x \in B -> A x) -> (\sum_(x <- B) f x) <= nonnegative_sum A f.
Proof. exact: (@nonnegative_sum_finite_upper R I A f _ (NonnegativeSum.laws A f) B). Qed.

(** Source for [nonnegative_sum_least]: Federer 2.1.1(3),
    p. 52; upper bounds on all finite subsums bound the sum. *)
Lemma nonnegative_sum_least (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) d :
  (forall (B : {fset I}), (forall x, x \in B -> A x) ->
    (\sum_(x <- B) f x) <= d) -> nonnegative_sum A f <= d.
Proof. exact: (@nonnegative_sum_finite_least R I A f _ (NonnegativeSum.laws A f) d). Qed.

(** Source for [nonnegative_sum_nonnegative]: Federer 2.1.1(3),
    p. 52, supporting nonnegativity since the empty subsum is zero. *)
Lemma nonnegative_sum_nonnegative (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) : 0 <= nonnegative_sum A f.
Proof.
have := @nonnegative_sum_upper R I A f fset0.
by rewrite big_seq_fset0; apply; move=> x; rewrite in_fset0.
Qed.

(** Source for [nonnegative_sum_empty]: Federer 2.1.1, p. 52,
    sentence before (1); the empty sum is zero. *)
Lemma nonnegative_sum_empty (R : realType) (I : choiceType) (f : I -> \bar R) :
  nonnegative_sum set0 f = 0.
Proof.
apply/eqP; rewrite eq_le nonnegative_sum_nonnegative andbT.
apply: nonnegative_sum_least => B hB.
have hB0 : B = fset0 by apply/fsetP=> x; rewrite in_fset0; apply/negP=> hx; exact: (hB x hx).
by rewrite hB0 big_seq_fset0.
Qed.

(** Source for [nonnegative_sum_term]: Federer 2.1.1(3),
    p. 52; supporting bound of each term by the sum. *)
Lemma nonnegative_sum_term (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) x : A x -> f x <= nonnegative_sum A f.
Proof.
move=> hx; have := @nonnegative_sum_upper R I A f [fset x].
rewrite big_seq_fset1; apply=> y /fset1P->; exact hx.
Qed.

(** Source for [nonnegative_sum_zero]: Federer 2.1.1(1)-(3),
    p. 52; the sum of a function vanishing on the summation set is zero. *)
Lemma nonnegative_sum_zero (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  (forall x, A x -> f x = 0) -> nonnegative_sum A f = 0.
Proof.
move=> hf; apply/eqP; rewrite eq_le nonnegative_sum_nonnegative andbT.
apply: nonnegative_sum_least=> B hB.
have hz : (\sum_(x <- B) f x) = 0.
  rewrite big_seq; apply: big1=> x hx; exact: hf (hB x hx).
by rewrite hz.
Qed.

(** Source for [nonnegative_sum_mono]: Federer 2.1.1(8),
    p. 53, nonnegative case; comparison follows on every finite set. *)
Lemma nonnegative_sum_mono (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) :
  (forall x, A x -> f x <= g x) -> nonnegative_sum A f <= nonnegative_sum A g.
Proof.
move=> h; apply: nonnegative_sum_least=> B hB.
apply: le_trans (@nonnegative_sum_upper R I A g B hB).
rewrite !big_seq; apply: lee_sum=> x hx; exact: h (hB x hx).
Qed.

(** Source for [nonnegative_sum_subset]: Federer 2.1.1(3),
    p. 52; supporting monotonicity in the summation set. *)
Lemma nonnegative_sum_subset (R : realType) (I : choiceType)
    (A B : set I) (f : I -> \bar R) :
  A `<=` B -> nonnegative_sum A f <= nonnegative_sum B f.
Proof.
move=> hAB; apply: nonnegative_sum_least=> C hC.
apply: nonnegative_sum_upper=> x hx; exact: hAB (hC x hx).
Qed.

(** Source for [nonnegative_sum_finite]: Federer 2.1.1(3), p. 52; the
    arbitrary-set sum agrees with finite summation when the terms are
    nonnegative. *)
Lemma nonnegative_sum_finite (R : realType) (I : choiceType)
    (B : {fset I}) (f : I -> \bar R) :
  (forall x, x \in B -> 0 <= f x) ->
  nonnegative_sum [set x | x \in B] f = \sum_(x <- B) f x.
Proof.
move=> h; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: nonnegative_sum_least=> C hC; apply: lee_sum_nneg_subfset.
  + exact hC.
  + move=> x; rewrite inE => /andP[_ hx] _; exact: h.
- by apply: nonnegative_sum_upper.
Qed.
