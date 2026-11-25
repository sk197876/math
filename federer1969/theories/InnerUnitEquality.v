(** Federer (1969), 1.8.2, p. 40: unit vectors attain equality in the upper
    Cauchy bound exactly when they coincide. This supports both the first
    paired step and the equality of unit exterior vectors in the normal-form
    computation. Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [inner_unit_pair_equality]: Federer 1.8.2,
    p. 40, equality in the unit-vector Cauchy bound. The proof
    expands the square of the difference, with no dimension hypothesis. *)
Theorem inner_unit_pair_equality (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (x y : V)
    (hx : inner_norm hB x = 1) (hy : inner_norm hB y = 1) :
  B x y = 1 <-> x = y.
Proof.
have hxx : B x x = 1 by rewrite -(inner_norm_sqr hB x) hx expr1n.
have hyy : B y y = 1 by rewrite -(inner_norm_sqr hB y) hy expr1n.
split; last by move=> ->.
move=> hxy; apply/eqP; rewrite -subr_eq0 -(inner_self_eq0 hB).
by rewrite (bilBl (inner_bilinear hB)) !(bilBr (inner_bilinear hB))
  (inner_symmetric hB y x) hxx hyy hxy !subrr.
Qed.
