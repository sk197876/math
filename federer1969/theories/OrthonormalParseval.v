(** Federer (1969), 1.7.5, p. 32: the coordinate square formula, with
    coefficients expressed by inner products. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies OrthonormalBilinearCoordinates
  LinearBasis FiniteDualDimension Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Parseval.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : orthonormal_family B e.
Hypothesis hb : is_basis e.

(** Source for [orthonormal_basis_inner_coordinate]: Federer
    1.7.5, p. 32, a coefficient in an orthonormal basis
    is the inner product with that basis vector. This supporting
    formulation allows any finite index set, including Lambda(n,m). *)
Lemma orthonormal_basis_inner_coordinate i x : dual_basis hb i x = B x (e i).
Proof.
have hh := @orthonormal_coefficient R V B hB I e he (fun j => dual_basis hb j x) i.
rewrite -(@orthonormal_basis_vector_expansion R V I e hb x) inner_coordinateE in hh.
exact: esym hh.
Qed.

(** Source for [orthonormal_parseval]: Federer 1.7.5,
    p. 32, the self inner product is the sum of squares
    of the inner products with an orthonormal basis. *)
Theorem orthonormal_parseval x : B x x = \sum_i (B x (e i))^+2.
Proof.
rewrite (@orthonormal_basis_bilinear_coordinates R V B (inner_bilinear hB) I e he hb x x).
apply: eq_bigr => i _; by rewrite orthonormal_basis_inner_coordinate expr2.
Qed.
End Parseval.
