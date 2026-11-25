(** Federer (1969), 1.7.6, p. 33: the norm of a linear map is the supremum
    of image lengths on the closed unit ball. The abstract specification
    below uses the attained maximum, available in finite dimension; a
    separate theorem identifies it with the printed supremum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_operator_norm]: Federer 1.7.6, p. 33,
    defining formula for the operator norm. This specification
    asserts an upper bound on the unit ball and attainment there;
    it neither selects coordinates nor defines a supremum witness. *)
Record is_operator_norm (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (L : R) : Prop := {
  operator_norm_unit_bound : forall x, inner_norm hB x <= 1 -> inner_norm hC (f x) <= L;
  operator_norm_attained : exists x, inner_norm hB x <= 1 /\ inner_norm hC (f x) = L
}.

(** Source for [operator_norm_unique]: Federer 1.7.6, p. 33,
    supporting uniqueness of the number specified by the norm formula. *)
Theorem operator_norm_unique (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) L M :
  is_operator_norm hB hC f L -> is_operator_norm hB hC f M -> L = M.
Proof.
move=> hL hM; have [x [hx hfx]] := operator_norm_attained hL.
have [y [hy hfy]] := operator_norm_attained hM.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -hfx; exact: (@operator_norm_unit_bound R V U B C hB hC f M hM x hx).
- rewrite -hfy; exact: (@operator_norm_unit_bound R V U B C hB hC f L hL y hy).
Qed.

(** Source for [operator_norm_nonnegative]: Federer 1.7.6,
    p. 33, supporting nonnegativity, including maps from dimension zero. *)
Lemma operator_norm_nonnegative (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) L : is_operator_norm hB hC f L -> 0 <= L.
Proof.
move=> hL; have [x [_ <-]] := operator_norm_attained hL.
exact: inner_norm_nonnegative.
Qed.

(** Source for [operator_norm_vector_bound]: Federer 1.7.6,
    pp. 33-34, supporting homogeneous bound |f(x)| <= ||f|| |x|,
    obtained by normalising a nonzero x. *)
Theorem operator_norm_vector_bound (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) L : is_operator_norm hB hC f L ->
  forall x, inner_norm hC (f x) <= L * inner_norm hB x.
Proof.
move=> hL x; have [->|hx] := eqVneq x 0.
- by rewrite linear0 !inner_norm0 mulr0.
have hn : inner_norm hB (inner_normalize hB x) <= 1.
  by rewrite inner_normalize_norm.
have hh := (@operator_norm_unit_bound R V U B C hB hC f L hL (inner_normalize hB x) hn).
have he : f x = inner_norm hB x *: f (inner_normalize hB x).
  by rewrite -linearZ inner_normalizeK.
rewrite he inner_normZ ger0_norm ?inner_norm_nonnegative // mulrC.
apply: ler_wpM2r; first exact: inner_norm_nonnegative.
exact hh.
Qed.
