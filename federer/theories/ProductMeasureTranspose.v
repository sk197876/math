(** Federer (1969), 2.6.1, pp. 114–115: the rectangle-cover definition is
    unchanged by interchanging the factors. This supporting symmetry gives
    the second integration order in 2.6.2(3), p. 115. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP NonnegativeSum NonnegativeSumSupport
  ProductMeasure ProductMeasureSequenceInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_transpose]: supporting exchange of
    the two coordinates for the symmetric formulas in
    Federer 2.6.2(3), p. 115. *)
Definition product_transpose (X Y : Type) (S : set (X * Y)) : set (Y * X) :=
  [set p | S (p.2,p.1)].

(** Source for [product_transpose_involutive]: supporting
    fact that exchanging coordinates twice restores the set
    in the symmetry argument for Federer 2.6.2, p. 115. *)
Lemma product_transpose_involutive (X Y : Type) (S : set (X * Y)) :
  product_transpose (product_transpose S) = S.
Proof. apply: funext=> p; by case: p. Qed.

(** Source for [product_measure_transpose_bound]: supporting
    cover comparison from Federer 2.6.1, pp. 114–115:
    transpose each covering rectangle; its cost is unchanged. *)
Lemma product_measure_transpose_bound (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure hb ha (product_transpose S) <= product_measure ha hb S.
Proof.
apply: (product_measure_sequence_cover_greatest ha hb)=> A B hm hc.
have hswap n : measure_measurable beta (B n) /\ measure_measurable alpha (A n) by split; [exact: (hm n).2|exact: (hm n).1].
have hcover : product_transpose S `<=` \bigcup_n (B n `*` A n).
  move=> [y x] hp; have [n _ [hx hy]] := hc (x,y) hp.
  exists n=> //; by split.
have h := @product_measure_sequence_cover_bound R Y X beta alpha hb ha (product_transpose S) B A hswap hcover.
apply: le_trans h _; apply: nonnegative_sum_mono=> n _; by rewrite muleC.
Qed.

(** Source for [product_measure_transpose]: symmetry of the Cartesian
    product definition in Federer 2.6.1, pp. 114–115, used in 2.6.2(3), p.
    115 All subsets, including nonmeasurable ones, satisfy the measure
    identity. *)
Theorem product_measure_transpose (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure hb ha (product_transpose S) = product_measure ha hb S.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@product_measure_transpose_bound R X Y alpha beta ha hb S).
- have h := @product_measure_transpose_bound R Y X beta alpha hb ha (product_transpose S).
  by rewrite product_transpose_involutive in h.
Qed.
