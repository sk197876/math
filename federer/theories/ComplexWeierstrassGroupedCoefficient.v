(** Federer (1969), 3.4.12, p. 339: the grouped complex
    germ retains every original double coefficient. Reuse the
    finite line coefficient comparison over characteristic zero;
    no interchange of infinite sums is required. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexScalarCharacteristicZero ComplexNormUP
  SymmetricForms HomogeneousPolynomialFunctions HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassCoefficientUP ComplexWeierstrassGroupedUP
  ComplexWeierstrassTransverseUP ComplexWeierstrassTransverseLaws WeierstrassFieldSplitFormExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_grouped_original_coefficients]:
    the exact double sequence of the original complex germ,
    extending 3.4.6, p. 323, as required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_grouped_original_coefficients (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (q:nat->nat->K->ComplexScalars.C R)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X)):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  is_complex_weierstrass_grouped_germ hNX xi projection q alpha ->
  forall i j,is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j (q i j).
Proof.
move=>hSplit hGrouped i j F hF z.
have hForm:F=@HolomorphicGermForms.value R X NX hNX 0 (i+j)%N alpha.
  apply:sform_ext=>t.
  by rewrite hF (@HolomorphicGermForms.laws R X NX hNX 0 (i+j)%N alpha t).
have hPolynomial x:(\sum_(s<(i+j).+1) (xi x)^+s*q s (i+j-s)%N (projection x))=
    sform_polynomial_value F x by rewrite hGrouped hForm.
have hValues (t:ComplexScalars.C R):sform_polynomial_value F (t*:v+inclusion z)=
    \sum_(s<(i+j).+1) t^+s*q s (i+j-s)%N z.
  rewrite -(hPolynomial (t*:v+inclusion z));apply:eq_bigr=>s _.
  by rewrite (complex_weierstrass_line_functional_coordinate hSplit)
    (complex_weierstrass_line_transverse_coordinate hSplit).
have hi:(i<=i+j)%N by rewrite leq_addr.
have hCoefficient:=@weierstrass_field_split_form_coefficient_unique (ComplexScalars.C R)
  (@complex_scalar_characteristic_zero R) X (i+j)%N F v (inclusion z)
  (fun s=>q s (i+j-s)%N z) hValues i hi.
have hDegree:(i+j-i)%N=j by rewrite addnC addnK.
by rewrite hDegree in hCoefficient.
Qed.
