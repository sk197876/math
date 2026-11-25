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
From Federer Require Import SymmetricInteriorUP SymmetricRightInteriorHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SymmetricRightInterior.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation E := (symmetric_space V).
Local Notation G := (symmetric_grading V).
Variables p q : nat.

(** Source for [symmetric_right_interior_degree]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Multiplication by a degree-p vector lowers the supported degree of a q-homogeneous functional to q-p. *)
Lemma symmetric_right_interior_degree (eta : symmetric_power V p) (phi : Hom_m W G q) :
  hom_degree G (q-p) (symmetric_right_interior_hom (component_val eta) phi).
Proof.
move=> n xi hn hxi; rewrite symmetric_right_interior_homE.
apply: hom_m_degree (symmetric_product_graded hxi (component_homogeneous eta)).
apply/eqP=> he; move: hn; rewrite -he addnK eqxx; by [].
Qed.

(** Source for [symmetric_right_interior_homogeneous]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Package the multiplication composite with its proved q-p degree support. *)
Definition symmetric_right_interior_homogeneous (eta : symmetric_power V p) (phi : S_m V W q) : Hom_m W G (q-p) :=
  @HomogeneousHom K E W G (q-p)
    (symmetric_right_interior_hom (component_val eta) (sform_homogeneous phi))
    (introT (asboolP _) (symmetric_right_interior_degree eta (sform_homogeneous phi))).

(** Source for [symmetric_right_interior]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Transport the multiplication composite through the proved form-Hom isomorphism to define the right interior form. *)
Definition symmetric_right_interior (_ : (p <= q)%N) (eta : symmetric_power V p) (phi : S_m V W q) : S_m V W (q-p) :=
  homogeneous_sform (symmetric_right_interior_homogeneous eta phi).
Variable hpq : (p <= q)%N.

(** Source for [symmetric_right_interior_homogeneousE]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The linear map of the right interior form is exactly precomposition with multiplication by the contracted vector. *)
Lemma symmetric_right_interior_homogeneousE eta phi xi :
  sform_homogeneous (symmetric_right_interior hpq eta phi) xi =
    sform_homogeneous phi (symmetric_product xi (component_val eta)).
Proof. by rewrite /symmetric_right_interior homogeneous_sformK. Qed.

(** Source for [symmetric_right_interior_characteristic]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The bracket against xi equals the bracket of the original form against xi times eta. *)
Theorem symmetric_right_interior_characteristic eta phi (xi : symmetric_power V (q-p)) :
  symmetric_pairing xi (symmetric_right_interior hpq eta phi) =
    sform_homogeneous phi (symmetric_product (component_val xi) (component_val eta)).
Proof. exact: symmetric_right_interior_homogeneousE. Qed.

(** Source for [symmetric_right_interior_unique]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: These brackets uniquely determine the right interior form. *)
Theorem symmetric_right_interior_unique eta phi (psi : S_m V W (q-p)) :
  (forall xi : symmetric_power V (q-p), symmetric_pairing xi psi =
    sform_homogeneous phi (symmetric_product (component_val xi) (component_val eta))) ->
  psi = symmetric_right_interior hpq eta phi.
Proof. move=> h; apply: symmetric_pairing_ext => xi; by rewrite h symmetric_right_interior_characteristic. Qed.

(** Source for [symmetric_right_interior_bilinear]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: Right interior multiplication is linear separately in the vector and the form. *)
Lemma symmetric_right_interior_bilinear : bilinear (symmetric_right_interior hpq).
Proof.
split.
- move=> phi c eta theta; apply: symmetric_pairing_ext => xi.
  rewrite (proj2 (@symmetric_pairing_bilinear K V W (q-p))).
  rewrite !symmetric_right_interior_characteristic (linearP (@component_val K E G p))
    (proj2 (symmetric_product_bilinear V)) linearP; by [].
- move=> eta c phi psi; apply: symmetric_pairing_ext => xi.
  rewrite (proj2 (@symmetric_pairing_bilinear K V W (q-p))).
  rewrite !symmetric_right_interior_characteristic (linearP (@sform_homogeneous K V W q))
    hom_m_addE hom_m_scaleE; by [].
Qed.

(** Source for [symmetric_right_interior_exists]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: The constructed operation satisfies the stated abstract bilinearity and characteristic-pairing specification. *)
Theorem symmetric_right_interior_exists : @is_symmetric_right_interior K V W p q (symmetric_right_interior hpq).
Proof. split; [exact: symmetric_right_interior_bilinear | exact: symmetric_right_interior_characteristic]. Qed.

(** Source for [symmetric_right_interior_universal]: Federer 1.10.3, p. 45,
    opening paragraph, referring to the characteristic conditions of
    1.5.1. In words: There exists exactly one bilinear operation satisfying the right characteristic pairing. *)
Theorem symmetric_right_interior_universal : exists i : symmetric_power V p -> S_m V W q -> S_m V W (q-p),
  is_symmetric_right_interior i /\ forall j, is_symmetric_right_interior j -> forall eta phi, j eta phi = i eta phi.
Proof.
exists (symmetric_right_interior hpq); split; first exact: symmetric_right_interior_exists.
move=> j [hj hc] eta phi; apply: symmetric_right_interior_unique => xi; exact: hc.
Qed.
End SymmetricRightInterior.
