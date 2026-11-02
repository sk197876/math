(** Federer (1969), 1.7.3, pp. 29-30: a one-dimensional invariant summand
    contributes zero to the alternating two-form. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP SymmetricEndomorphisms
  OrthonormalFamilies OrthonormalSingleCoordinate GramSchmidt
  OrthonormalisationUP LinearBasis TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [skew_one_dimensional_zero]: Federer 1.7.3,
    pp. 29-30, supporting low-dimensional case: a skewsymmetric
    endomorphism of a one-dimensional real inner-product space is zero. *)
Theorem skew_one_dimensional_zero (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) (hf : is_skewsymmetric_endomorphism B f)
    (b : 'I_1 -> V) (hb : is_basis b) : forall x, f x = 0.
Proof.
have [e [he hgs]] := @orthonormal_basis_exists R V B hB 1 b hb.
have ho := orthonormalisation_orthonormal hgs.
apply: (basis_induction he) => [|x y hx hy|a x hx|i].
- exact: linear0.
- by rewrite linearD hx hy addr0.
- rewrite linearZ hx; change (a *: (0 : V) = 0); exact: scaler0.
have hx := @orthonormal_single_coordinate R V B hB 1 e he ho (f (e i)) i.
have hc : f (e i) = B (f (e i)) (e i) *: e i.
  apply: hx => j hj.
  have hji : j = i by rewrite (ord1 j) (ord1 i).
  by move: hj; rewrite hji eqxx.
rewrite hc (@skewsymmetric_diagonal_zero R V B hB f hf) scale0r.
by [].
Qed.
