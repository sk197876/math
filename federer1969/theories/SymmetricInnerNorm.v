(** Federer (1969), 1.10.5, p. 47: norms induced by the symmetric inner
    products. The norm uses only the previously sealed
    nonnegative-square-root specification from 1.7.1. It is distinct from
    the mass norm subsequently defined on arbitrary normed spaces. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  RealNormUP SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds
  SymmetricNormalizedMonomials OrthonormalFamilies InnerSymmetric
  InnerSymmetricBasis InnerSymmetricPositivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Norm.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [symmetric_inner_norm]: Federer 1.10.5,
    p. 47, the norm from the induced symmetric inner product,
    specified by the nonnegative-square-root laws of 1.7.1. *)
Definition symmetric_inner_norm m := inner_norm (@symmetric_inner_productP R V B hB m).

(** Source for [symmetric_inner_norm_square]: Federer 1.10.5,
    p. 47, the square of the norm is the induced inner product
    of the vector with itself. *)
Lemma symmetric_inner_norm_square m (x : symmetric_power V m) :
  symmetric_inner_norm x ^+ 2 = symmetric_inner_form hB x x.
Proof. exact: inner_norm_sqr. Qed.

(** Source for [symmetric_inner_norm_nonnegative]: Federer 1.10.5,
    p. 47, supporting nonnegativity of the induced norm. *)
Lemma symmetric_inner_norm_nonnegative m (x : symmetric_power V m) :
  0 <= symmetric_inner_norm x.
Proof. exact: inner_norm_nonnegative. Qed.

(** Source for [symmetric_inner_norm_zero]: Federer 1.10.5,
    p. 47, the zero vector has norm zero in every degree. *)
Lemma symmetric_inner_norm_zero m : symmetric_inner_norm (0 : symmetric_power V m)=0.
Proof. exact: inner_norm0. Qed.

(** Source for [symmetric_inner_norm_eq0]: Federer 1.10.5,
    p. 47, positive definiteness: norm zero is equivalent to vector zero. *)
Lemma symmetric_inner_norm_eq0 m (x : symmetric_power V m) :
  (symmetric_inner_norm x == 0) = (x == 0).
Proof. exact: inner_norm_eq0. Qed.

(** Source for [symmetric_inner_norm_scale]: Federer 1.10.5,
    p. 47, absolute homogeneity of the induced norm, inherited
    from the general inner-product norm laws proved in 1.7.1. *)
Lemma symmetric_inner_norm_scale m (x : symmetric_power V m) c :
  symmetric_inner_norm (c *: x) = `|c| * symmetric_inner_norm x.
Proof. exact: inner_normZ. Qed.

(** Source for [symmetric_inner_norm_triangle]: Federer 1.10.5,
    p. 47, the induced norm satisfies the triangle inequality
    by the inner-product argument of 1.7.1. *)
Lemma symmetric_inner_norm_triangle m (x y : symmetric_power V m) :
  symmetric_inner_norm (x+y) <= symmetric_inner_norm x + symmetric_inner_norm y.
Proof. exact: inner_norm_triangle. Qed.

(** Source for [symmetric_inner_normP]: Federer 1.10.5,
    pp. 47-48, supporting compatibility with the arbitrary normed-space
    specification used in the subsequent mass and operator-norm discussion. *)
Theorem symmetric_inner_normP m : is_real_norm (@symmetric_inner_norm m).
Proof.
split.
- constructor.
  + exact: symmetric_inner_norm_nonnegative.
  + move=> a x; exact: symmetric_inner_norm_scale.
  + exact: symmetric_inner_norm_triangle.
- move=> x /eqP; by rewrite symmetric_inner_norm_eq0=> /eqP.
Qed.

(** Source for [symmetric_orthonormal_monomial_norm]: Federer 1.10.5,
    p. 47, each displayed normalized monomial has norm one,
    including the empty product in degree zero. *)
Lemma symmetric_orthonormal_monomial_norm n (e : 'I_n -> V)
    (ho : orthonormal_family B e) m (a : symmetric_indices n m) :
  symmetric_inner_norm (symmetric_normalized_monomial e a) = 1.
Proof.
apply: inner_norm_value; first exact: ler01.
have h := @symmetric_orthonormal_family R V B hB n e ho m a a.
by rewrite eqxx in h; rewrite expr1n; symmetry.
Qed.
End Norm.
