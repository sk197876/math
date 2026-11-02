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
From Federer Require Import SymmetricFormReindex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CharacteristicConditions.
Variable K : fieldType.
Variables V W : lmodType K.
Variables p q : nat.

(** Source for [is_symmetric_right_interior]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Abstract specification: bilinearity and the characteristic pairing obtained by multiplication inside the original form. *)
Definition is_symmetric_right_interior
  (i : symmetric_power V p -> S_m V W q -> S_m V W (q-p)) : Prop :=
  bilinear i /\ forall eta phi xi,
    symmetric_pairing xi (i eta phi) =
      sform_homogeneous phi (symmetric_product (component_val xi) (component_val eta)).
Variable hpq : (p <= q)%N.

(** Source for [is_symmetric_left_interior]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Abstract specification: bilinearity and the characteristic pairing obtained by multiplying the two covectors. *)
Definition is_symmetric_left_interior
  (i : symmetric_power V q -> S_m V K^o p -> symmetric_power V (q-p)) : Prop :=
  bilinear i /\ forall zeta a b,
    symmetric_pairing (i zeta a) b =
      symmetric_pairing zeta (sform_reindex (subnKC hpq) (sform_product (scalar_bilinear K) a b)).
End CharacteristicConditions.
