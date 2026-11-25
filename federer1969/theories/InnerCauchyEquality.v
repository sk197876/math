(** Federer (1969), 1.7.5, p. 33: equality in the pairing bound exactly for
    dependent vectors. Supporting full equality criterion for an inner
    product, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm
  InnerNormInequalities IndependentPair DependentPair Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_cauchy_equality_dependent]: Federer
    1.7.5, p. 33, supporting equality criterion for Cauchy's
    absolute-value bound, with zero vectors included. *)
Theorem inner_cauchy_equality_dependent (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (x y : V) :
  `|B x y| = inner_norm hB x * inner_norm hB y <-> ~ independent_pair x y.
Proof.
split.
- move=> he hi; have hh := @inner_cauchy_strict R V B hB x y hi.
  by rewrite he ltxx in hh.
- move/(proj1 (dependent_pair_cases x y))=> [->|[a ->]].
  + by rewrite (bil0r (inner_bilinear hB)) normr0 inner_norm0 mulr0.
  + rewrite (bilZl (inner_bilinear hB)) inner_normZ.
    change (`|a * B y y| = (`|a| * inner_norm hB y) * inner_norm hB y).
    by rewrite normrM (ger0_norm (inner_nonnegative hB y)) -mulrA -expr2 inner_norm_sqr.
Qed.
