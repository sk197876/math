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

From Federer Require Import PairingSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
(** Source for [symmetric_pairing_vectors_separate]: Federer 1.10.3, p. 45,
    the uniqueness implicit in the definition by 1.5.1. In words: Pairings
    against all scalar symmetric forms separate symmetric vectors, including
    in arbitrary dimension. *)
Theorem symmetric_pairing_vectors_separate (K : fieldType) (V : lmodType K) m
    (x y : symmetric_power V m) :
  (forall phi : S_m V K^o m, symmetric_pairing x phi = symmetric_pairing y phi) -> x = y.
Proof.
move=> h; apply: linear_functionals_separate=> f.
move: (h (hom_to_sform f)).
by rewrite /symmetric_pairing !hom_to_sformK.
Qed.
