(** Federer (1969), 3.2.46, p. 281, using the
    discriminant of 1.7.10, p. 35: the actual intrinsic
    discriminant equals the finite signed coordinate polynomial.
    This is a calculation through public representative laws,
    not a replacement definition of the discriminant. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  fingroup perm.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates TensorUP
  EuclideanInnerProduct InnerProductUP InnerProductLaws EuclideanCoordinateTopology CoordinateProjection
  EuclideanLinearMaps ExteriorLeibniz InversionCount BilinearRepresentativeUP BilinearInvariants
  PositiveSymmetricNormFactor PositiveNormFactorDiscriminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_inner_discriminant_polynomial]:
    the actual discr B is the signed sum of products of the
    coefficients B(e_i,e_j), from 1.3.4, p. 16, and 1.7.10,
    p. 35, supporting continuity in 3.2.46, p. 281. *)
Lemma euclidean_inner_discriminant_polynomial (R : realType) n
    (B : R_n R n -> R_n R n -> R) (hB : is_inner_product B) :
  euclidean_inner_form_discriminant hB =
    \sum_(sigma : 'S_n) FedererPermutation.index R sigma *
      \prod_(i < n) B (@coordinate_basis R n i) (@coordinate_basis R n (sigma i)).
Proof.
pose F := @bilinear_representative R (R_n R n) (@euclidean_inner_product R n) B
  (@euclidean_inner_productP R n) (inner_bilinear hB) n
  (@coordinate_basis R n) (@coordinate_basisP R n).
have hCoeff i j : (F (@coordinate_basis R n i)) j = B (@coordinate_basis R n i) (@coordinate_basis R n j).
  have h := @bilinear_representativeP R (R_n R n) (@euclidean_inner_product R n) B
    (@euclidean_inner_productP R n) (inner_bilinear hB) n
    (@coordinate_basis R n) (@coordinate_basisP R n)
    (@coordinate_basis R n i) (@coordinate_basis R n j).
  by rewrite euclidean_inner_basis in h.
have hExpansion i : F (@coordinate_basis R n i) =
    \sum_(j < n) B (@coordinate_basis R n i) (@coordinate_basis R n j) *: (@coordinate_basis R n j).
  rewrite -(euclidean_coordinate_expansion (F (@coordinate_basis R n i))).
  apply: eq_bigr=> j _; by rewrite hCoeff.
rewrite /euclidean_inner_form_discriminant /bilinear_discriminant.
exact (@det_formula R (euclidean_two_nonzero R) n (R_n R n)
  (@coordinate_basis R n) (@coordinate_basisP R n) F
  (fun i j=>B (@coordinate_basis R n i) (@coordinate_basis R n j)) hExpansion).
Qed.

(** Source for [euclidean_inner_discriminant_positive]: the
    printed density has strictly positive squared value, supporting
    3.2.46, p. 281. The actual local positive factor proves this,
    including the empty-product discriminant one in dimension zero. *)
Lemma euclidean_inner_discriminant_positive (R : realType) n
    (B : R_n R n -> R_n R n -> R) (hB : is_inner_product B) :
  0 < euclidean_inner_form_discriminant hB.
Proof.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have hDet := positive_norm_factor_det_positive hL.
have hEq := positive_norm_factor_discriminant hL.
by rewrite -sqrtr_gt0 -hEq.
Qed.
