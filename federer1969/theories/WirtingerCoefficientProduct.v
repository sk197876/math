(** Federer (1969), 1.8.2, p. 40: the scalar last step
    of Wirtinger's inequality. Nonnegative normal-form coefficients
    bounded by one have product at most one; equality requires every
    coefficient to be one and the orientation to be positive. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Product.
Variable R : realFieldType.
Variable I : finType.
Variable lambda : I -> R.
Hypotheses (h0 : forall i, 0 <= lambda i) (h1 : forall i, lambda i <= 1).

(** Source for [wirtinger_coefficient_product_nonnegative]: Federer
    1.8.2, p. 40, the normal-form coefficient product is nonnegative. *)
Lemma wirtinger_coefficient_product_nonnegative : 0 <= \prod_i lambda i.
Proof. apply: prodr_ge0 => i _; exact: h0. Qed.

(** Source for [wirtinger_coefficient_product_bound]: Federer 1.8.2,
    p. 40, the product of the coefficients is at most one. *)
Lemma wirtinger_coefficient_product_bound : \prod_i lambda i <= 1.
Proof. apply: prodr_ile1 => i _; by rewrite h0 h1. Qed.

(** Source for [wirtinger_product_le_factor]: Federer 1.8.2,
    p. 40, supporting fact for the equality criterion: the product
    is at most each individual coefficient. *)
Lemma wirtinger_product_le_factor i : \prod_j lambda j <= lambda i.
Proof.
rewrite (bigD1 i) //=.
apply: ler_piMr; first exact: h0.
apply: prodr_ile1 => j _; by rewrite h0 h1.
Qed.

(** Source for [wirtinger_coefficient_product_equality]: Federer
    1.8.2, p. 40, the coefficient product equals one exactly when
    every coefficient equals one, including the empty product. *)
Theorem wirtinger_coefficient_product_equality :
  (\prod_i lambda i = 1) <-> (forall i, lambda i = 1).
Proof.
split.
- move=> hp i; apply/eqP; rewrite eq_le h1 /=.
  by rewrite -hp wirtinger_product_le_factor.
- move=> hl; apply: big1 => i _; exact: hl.
Qed.

(** Source for [wirtinger_signed_product_bound]: Federer 1.8.2,
    p. 40, delta times the coefficient product is at most one.
    The book has delta=+1 or -1; the bound only needs delta<=1. *)
Theorem wirtinger_signed_product_bound delta : delta <= 1 ->
  delta * (\prod_i lambda i) <= 1.
Proof.
move=> hd; apply: le_trans wirtinger_coefficient_product_bound.
exact: ler_piMl wirtinger_coefficient_product_nonnegative hd.
Qed.

(** Source for [wirtinger_signed_product_equality]: Federer 1.8.2,
    p. 40, equality holds exactly for positive orientation and
    lambda_j=1 for every pair. *)
Theorem wirtinger_signed_product_equality delta : delta <= 1 ->
  (delta * (\prod_i lambda i) = 1 <-> delta = 1 /\ forall i, lambda i = 1).
Proof.
move=> hd; split.
- move=> he.
  have hle : 1 <= \prod_i lambda i.
    have hh := ler_piMl wirtinger_coefficient_product_nonnegative hd.
    by rewrite he in hh.
  have hp : \prod_i lambda i = 1.
    by apply/eqP; rewrite eq_le wirtinger_coefficient_product_bound hle.
  split; first by move: he; rewrite hp mulr1.
  exact: (proj1 wirtinger_coefficient_product_equality hp).
- move=> [-> hl]; rewrite mul1r; exact: (proj2 wirtinger_coefficient_product_equality hl).
Qed.
End Product.
