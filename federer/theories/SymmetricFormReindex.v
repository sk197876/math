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
Section Reindex.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [sform_reindex]: Federer 1.10.3, p. 45, the second
    characteristic pairing as in 1.5.1. Supporting transport between
    equal natural-number degrees; it leaves the homogeneous map unchanged. *)
Definition sform_reindex m n (e : m=n) (f : S_m V W m) : S_m V W n :=
  match e with erefl => f end.
(** Source for [sform_reindexE]: Federer 1.10.3, p. 45, the second
    characteristic pairing. Supporting fact: degree transport does not
    change evaluation on the full symmetric algebra. *)
Lemma sform_reindexE m n (e : m=n) (f : S_m V W m) x :
  sform_homogeneous (sform_reindex e f) x = sform_homogeneous f x.
Proof. by case: n / e. Qed.
End Reindex.
