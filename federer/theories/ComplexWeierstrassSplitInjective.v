(** Federer (1969), 3.4.12, p. 339: every original mixed
    coefficient determines the actual holomorphic germ uniquely.
    Reuse the finite complex line expansion, polarization and
    actual Taylor injectivity, without a formal-series replacement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarCharacteristicZero
  ComplexNormUP ComplexModulus ComplexScalarNorm SymmetricForms PolynomialTaylorTerms HomogeneousPolynomialFunctions
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermJetsSealed
  HolomorphicGermFormsUP HolomorphicGermFormsSealed HolomorphicGermTaylorInjective
  ComplexWeierstrassCoefficientUP ComplexWeierstrassTransverseUP WeierstrassFieldSplitFormExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_split_coefficients_injective]: the
    uniqueness of the double-sequence representation in the complex
    extension of 3.4.6, p. 323, required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_split_coefficients_injective (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (alpha beta:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (C D:nat->nat->K->ComplexScalars.C R):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j (C i j)) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX beta v inclusion i j (D i j)) ->
  (forall i j z,C i j z=D i j z) ->alpha=beta.
Proof.
move=>hSplit hC hD hEqual.
pose F m:=@HolomorphicGermForms.value R X NX hNX 0 m alpha.
pose G m:=@HolomorphicGermForms.value R X NX hNX 0 m beta.
have hF m:=@HolomorphicGermForms.laws R X NX hNX 0 m alpha.
have hG m:=@HolomorphicGermForms.laws R X NX hNX 0 m beta.
have hCoefficient i j z:
    sform_polynomial_value (symmetric_taylor_term j (F (i+j)%N) v) (inclusion z)=
    sform_polynomial_value (symmetric_taylor_term j (G (i+j)%N) v) (inclusion z).
  by rewrite -(hC i j (F (i+j)%N) (hF (i+j)%N) z)
    -(hD i j (G (i+j)%N) (hG (i+j)%N) z) hEqual.
have hForms m:F m=G m.
  apply:(@sform_polynomial_injective (ComplexScalars.C R) X (ComplexScalars.C R)^o m
    (@complex_scalar_characteristic_zero R));apply:funext=>x.
  have hDecompose:x=(xi x)*:v+inclusion (projection x).
    by rewrite (complex_weierstrass_transverse_projection_equation hSplit) addrC subrK.
  rewrite hDecompose !(weierstrass_field_split_form_line_expansion (@complex_scalar_characteristic_zero R)).
  apply:eq_bigr=>i _.
  have hi:(i<=m)%N by have:=ltn_ord i;rewrite ltnS.
  have hSame:=hCoefficient i (m-i)%N (projection x).
  rewrite (subnKC hi) in hSame;by rewrite hSame.
apply:(@holomorphic_germ_jets_injective R X NX (complex_norm_real hNX) 0 alpha beta)=>m.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R m
  (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX
  (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)))=>u.
have hTuple:[ffun s=>tnth [tuple u j | j<m] s]=u.
  by apply/ffunP=>s;rewrite ffunE tnth_mktuple.
have hFirst:=hF m [tuple u j | j<m].
have hSecond:=hG m [tuple u j | j<m].
rewrite hTuple in hFirst;rewrite hTuple in hSecond.
have hValues:=congr1 (fun H:S_m X (ComplexScalars.C R)^o m=>H [tuple u j | j<m]) (hForms m).
have hActual:=etrans hValues hSecond.
exact:etrans (esym hFirst) hActual.
Qed.
