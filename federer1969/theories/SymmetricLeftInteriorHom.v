(** Federer (1969), 1.10.3, p. 45: symmetric interior multiplications,
    defined by the characteristic pairings as in 1.5.1. Scalars may be any
    field here. No finite-dimensional hypothesis is used. surjectivity is
    neither asserted nor used. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import ScalarCoefficients TensorUP Bilinear Graded GradedComponents
  TensorProduct AlgebraTensor TensorGrading Hom HomogeneousHom
  HomogeneousSum Convolution ConvolutionAssociativity GradedConvolution
  SymmetricAlgebra SymmetricGrading SymmetricDirectSum SymmetricDiagonal
  SymmetricCoassociativity SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFormProduct SymmetricPairing.
From Federer Require Import PairingSeparation ScalarTensorContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricLeftInteriorHom.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_space V).
Local Notation D := (symmetric_diagonal V).

(** Source for [symmetric_left_interior_hom]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Compose the symmetric diagonal with evaluation in the first tensor factor and scalar multiplication in the second factor. *)
Definition symmetric_left_interior_hom (zeta : E) (h : Hom E K^o) : E := @contract_tensor K E E h (D zeta).

(** Source for [symmetric_left_interior_composite]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The contraction is precisely the diagonal, then h tensor identity, then scalar multiplication. *)
Lemma symmetric_left_interior_composite zeta h : symmetric_left_interior_hom zeta h =
  scalar_tensor E (tensor_map (hom_as_linear h) (linear_id E) (D zeta)).
Proof. by []. Qed.

(** Source for [symmetric_left_interior_hom_bilinear]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The diagonal contraction is bilinear in its vector and covector inputs. *)
Lemma symmetric_left_interior_hom_bilinear : bilinear symmetric_left_interior_hom.
Proof.
split.
- move=> h a x y; by rewrite /symmetric_left_interior_hom !linearP.
- move=> zeta; exact: (@contract_tensor_parameter_linear K E E).
Qed.

(** Source for [symmetric_left_interior_diagram]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Evaluation after contraction equals the convolution of the two scalar functionals evaluated before contraction. *)
Theorem symmetric_left_interior_diagram zeta h (k : Hom E K^o) :
  k (symmetric_left_interior_hom zeta h) = convolution (scalar_bilinear K) D h k zeta.
Proof. exact: contract_tensor_pairing. Qed.

(** Source for [symmetric_left_interior_hom_unique]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Evaluation by all linear functionals uniquely determines the contracted symmetric vector. *)
Theorem symmetric_left_interior_hom_unique zeta h y :
  (forall k : Hom E K^o, k y = convolution (scalar_bilinear K) D h k zeta) ->
  y = symmetric_left_interior_hom zeta h.
Proof. move=> hy; apply: linear_functionals_separate => k; by rewrite hy symmetric_left_interior_diagram. Qed.

(** Source for [symmetric_left_interior_hom_associative]: Federer 1.10.3, p.
    45, opening paragraph. In words: Supporting composition identity *)
Theorem symmetric_left_interior_hom_associative zeta a b :
  symmetric_left_interior_hom zeta (convolution (scalar_bilinear K) D a b) =
    symmetric_left_interior_hom (symmetric_left_interior_hom zeta a) b.
Proof.
apply: linear_functionals_separate => k.
have hass := @convolution_associative K E K^o (fun x y : K^o => x*y)
  (scalar_bilinear K) (@mulrA K) D (@symmetric_forms_diagonal_coassociative K V) a b k.
apply: eq_trans (@symmetric_left_interior_diagram zeta (convolution (scalar_bilinear K) D a b) k) _.
apply: eq_trans (congr1 (fun f : Hom E K^o => f zeta) (esym hass)) _.
apply: eq_trans (esym (@symmetric_left_interior_diagram zeta a (convolution (scalar_bilinear K) D b k))) _.
exact: esym (@symmetric_left_interior_diagram (symmetric_left_interior_hom zeta a) b k).
Qed.
End SymmetricLeftInteriorHom.
