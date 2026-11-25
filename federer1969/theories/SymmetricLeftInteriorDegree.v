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

From Federer Require Import LeftInteriorDegree SymmetricLeftInteriorHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
(** Source for [symmetric_left_interior_degree]: Federer 1.10.3,
    p. 45, the degree of the second interior product. In words:
    Contraction of a q-vector by a p-form lies in degree q-p.
    The generic tensor-degree lemma proved for 1.5.1 applies unchanged;
    no alternating-algebra law or characteristic restriction is used. *)
Theorem symmetric_left_interior_degree (K : fieldType) (V : lmodType K) p q
    (zeta : symmetric_power V q) (a : S_m V K^o p) :
  homogeneous (symmetric_grading V) (q-p)
    (symmetric_left_interior_hom (component_val zeta) (sform_homogeneous a)).
Proof.
apply: contract_tensor_degree.
exact: symmetric_diagonal_graded (component_homogeneous zeta).
Qed.
