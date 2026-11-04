(** Federer (1969), 3.2.46, p. 281: the discriminant depends on
    the actual bilinear form, not on a proof that it is positive.
    Prove this through the unique representative laws of 1.7.10,
    p. 35, without adding a proof-irrelevance axiom. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP EuclideanLinearMaps
  BilinearInvariants BilinearRepresentativeUP PositiveNormFactorDiscriminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_inner_form_discriminant_proof_independent]:
    the intrinsic discr(g(a)) in Federer 3.2.46, p. 281, by the
    characterizing equation of 1.7.10, p. 35. Two proofs of the
    same inner-product laws give the same actual discriminant. *)
Lemma euclidean_inner_form_discriminant_proof_independent (R : realType) n
    (B : R_n R n -> R_n R n -> R) (h1 h2 : is_inner_product B) :
  euclidean_inner_form_discriminant h1 = euclidean_inner_form_discriminant h2.
Proof.
pose hE := @euclidean_inner_productP R n.
pose hb := @coordinate_basisP R n.
pose F := bilinear_representative hE (inner_bilinear h2) hb.
have hF := bilinear_representativeP hE (inner_bilinear h2) hb.
exact: (@bilinear_discriminant_characterisation R (euclidean_two_nonzero R)
  (R_n R n) (@euclidean_inner_product R n) B hE (inner_bilinear h1)
  n (@coordinate_basis R n) hb F hF).
Qed.
