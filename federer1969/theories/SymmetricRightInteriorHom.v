(** Federer (1969), 1.10.3, p. 45: symmetric interior multiplications,
    defined by the characteristic pairings as in 1.5.1. Scalars may be any
    field here. No finite-dimensional hypothesis is used. surjectivity is
    neither asserted nor used. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP Bilinear Graded GradedComponents
  TensorProduct AlgebraTensor TensorGrading Hom HomogeneousHom
  HomogeneousSum Convolution ConvolutionAssociativity GradedConvolution
  SymmetricAlgebra SymmetricGrading SymmetricDirectSum SymmetricDiagonal
  SymmetricCoassociativity SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFormProduct SymmetricPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricRightInteriorHom.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation E := (symmetric_space V).

(** Source for [symmetric_right_multiplication]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Right multiplication by a symmetric vector is a linear map on the symmetric algebra. *)
Definition symmetric_right_multiplication (eta : E) (xi : E) := symmetric_product xi eta.

(** Source for [symmetric_right_multiplication_linear]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Supporting linearity of multiplication in its first argument. *)
Lemma symmetric_right_multiplication_linear eta : linear (symmetric_right_multiplication eta).
Proof. exact: (proj1 (symmetric_product_bilinear V)). Qed.
HB.instance Definition _ eta := GRing.isLinear.Build K E E *:%R
  (symmetric_right_multiplication eta) (symmetric_right_multiplication_linear eta).

(** Source for [symmetric_right_interior_hom]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Precompose the linear map of a form with right symmetric multiplication. *)
Definition symmetric_right_interior_hom (eta : E) (phi : Hom E W) : Hom E W :=
  hom_comp phi (hom_of_linear (GRing.Linear.clone _ _ _ _ (symmetric_right_multiplication eta) _)).

(** Source for [symmetric_right_interior_homE]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The resulting functional evaluates at xi as the original functional evaluated at xi times eta. *)
Lemma symmetric_right_interior_homE eta phi xi : symmetric_right_interior_hom eta phi xi = phi (symmetric_product xi eta).
Proof. by []. Qed.

(** Source for [symmetric_right_interior_hom_bilinear]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: This precomposition is bilinear in the symmetric vector and the functional. *)
Lemma symmetric_right_interior_hom_bilinear : bilinear symmetric_right_interior_hom.
Proof.
split.
- move=> phi c eta theta; apply: hom_ext => xi.
  by rewrite !symmetric_right_interior_homE hom_addE hom_scaleE (proj2 (symmetric_product_bilinear V)) linearP.
- move=> eta c phi psi; apply: hom_ext => xi.
  by rewrite !symmetric_right_interior_homE !hom_addE !hom_scaleE.
Qed.

(** Source for [symmetric_right_interior_hom_associative]: Federer 1.10.3,
    p. 45, opening paragraph. In words: Supporting composition identity *)
Theorem symmetric_right_interior_hom_associative xi eta phi :
  symmetric_right_interior_hom (symmetric_product xi eta) phi =
    symmetric_right_interior_hom xi (symmetric_right_interior_hom eta phi).
Proof. apply: hom_ext => zeta; by rewrite !symmetric_right_interior_homE symmetric_product_assoc. Qed.
End SymmetricRightInteriorHom.
