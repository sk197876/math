(** Federer (1969), 3.4.12, p. 339: original complex
    preparation follows by division of xi^k. Reuse the proved
    complex division theorem, actual monic coefficients and finite
    remainder; retain every original functional xi(v)=1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormLinearDomainLaws NormOpenDomainLaws NormBoundedLinearTopology
  HolomorphicUP HolomorphicOpenDomain HolomorphicLinear HolomorphicNegation HolomorphicFiniteCalculus
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP
  HolomorphicGermOperationsUP HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing
  ComplexWeierstrassRegularUP ComplexWeierstrassDivisionUP ComplexWeierstrassDivisionWithTransverse
  ComplexWeierstrassTransverseUP ComplexWeierstrassCoefficientUP ComplexWeierstrassCoefficientExistence
  ComplexWeierstrassFunctionalPower ComplexWeierstrassPolynomialHighCoefficients
  ComplexWeierstrassFiniteRemainderRepresentation ComplexWeierstrassPreparationCoefficientValues
  ComplexWeierstrassZerothCoefficient ComplexWeierstrassPreparationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Preparation.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation KR:=(restricted_space (ComplexScalars.embed R) K).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNKR:=(complex_norm_real hNK).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation G:=(@holomorphic_germ_ring R X NX hNXR 0).
Local Notation H:=(@holomorphic_germ_ring R K NK hNKR 0).

(** Source for [complex_weierstrass_preparation_with_transverse_exists]: the
    original monic polynomial and nonzero multiplier exist, with
    holomorphic transverse coefficients vanishing at zero, extending
    3.4.6(2), p. 322, under 3.4.12, p. 339. No prepared
    factor, multiplier value or vanishing conclusion is supplied. *)
Theorem complex_weierstrass_preparation_with_transverse_exists v (xi:Hom X C^o)
    (inclusion:Hom K X) (projection:Hom X K) k (Phi:G):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R XR CR NX N (complex_hom_real xi) ->
  is_complex_weierstrass_regular_germ hNX Phi k v ->
  exists Q W:G,exists Wi:'I_k->H,
    @is_complex_weierstrass_preparation R X K NX NK hNXR hNKR xi projection k Phi Q W Wi.
Proof.
move=>hSplit hXi hRegular.
have [power [hPowerValues hPower]]:=@complex_weierstrass_functional_power_representative R X NX hNX xi k hXi.
pose Psi:G:=holomorphic_germ power.
have [Q [T [hDivision _]]]:=@complex_weierstrass_division_with_transverse R X K NX NK hNX hNK
  v xi inclusion projection k Phi Psi hSplit hXi hRegular.
have [phi hPhi]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Phi v inclusion.
have [psi hPsi]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Psi v inclusion.
have [q hQ]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Q v inclusion.
have [r hR]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX T v inclusion.
have hMonic:=@complex_weierstrass_functional_power_coefficients R X NX hNX K NK v xi inclusion projection k
  power psi hSplit hPowerValues hPower.1 hPsi.
have [hLow hQNonzero]:=@complex_weierstrass_preparation_coefficient_values R X K NX hNX v inclusion k
  Phi Psi Q T phi psi q r hRegular hDivision hPhi hPsi hQ hR hMonic.
have hHigh:=@complex_weierstrass_polynomial_high_coefficients R X K NX hNX k v inclusion T r
  (complex_weierstrass_division_polynomial_remainder hDivision) hR.
have [remainder [hRepR [U [haU [D [hD [hDZero hRValues]]]]]]]:=
  @complex_weierstrass_finite_remainder_representation R X K NX NK hNX v xi inclusion projection
    k T r hSplit hXi hR hHigh.
pose V:=fun z:K=>U (inclusion z).
have hU x (hx:U x):@norm_domain_interior R XR NX U x.
  exact:holomorphic_domain_interior (hD 0%N) x hx.
have hV z (hz:V z):@norm_domain_interior R KR NK V z.
  exact:(norm_bounded_linear_preimage_interior hNKR
    (complex_weierstrass_transverse_inclusion_bounded hSplit) (hU (inclusion z) hz)).
have haV:V 0 by rewrite /V linear0.
have hInclusion:=@holomorphic_bounded_linear R K X NK NX hNKR hNXR V inclusion hV
  (complex_weierstrass_transverse_inclusion_bounded hSplit).
have hEach (i:'I_k):exists c:@holomorphic_representative_type R K NK hNKR 0,
    holomorphic_representative_value c=(fun z=>-D i (inclusion z)).
  have hNegate:=holomorphic_negate (hD i).
  have hComposite:=@holomorphic_compose_on R K X C^o NK NX N hNKR hNXR hN
    V U inclusion (fun x=>-D i x) (fun z hz=>hz) hInclusion hNegate.
  exact:(@holomorphic_representative_from_domain R K NK hNKR 0 V
    (fun z=>-D i (inclusion z)) haV hComposite).
have [coefficients hCoefficients]:=choice hEach.
pose Wi (i:'I_k):H:=holomorphic_germ (coefficients i).
pose W:G:=Psi-T.
pose w:=@holomorphic_add_representatives R X NX hNXR 0 power
  (@holomorphic_negate_representative R X NX hNXR 0 remainder).
have hRepW:holomorphic_germ w=W.
  rewrite /W /Psi -hRepR.
  change (holomorphic_germ w=@HolomorphicGerms.add R X NX hNXR 0 (holomorphic_germ power)
    (@HolomorphicGerms.opp R X NX hNXR 0 (holomorphic_germ remainder))).
  by rewrite (@holomorphic_germ_negate_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNXR 0))
    (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNXR 0)).
exists Q,W,Wi;constructor.
- rewrite /W (complex_weierstrass_division_identity hDivision) addrK;reflexivity.
- have [quotient hRepQ]:=@holomorphic_germ_has_representative R X NX hNXR 0 Q.
  exists quotient;split;first exact:hRepQ.
  rewrite -(@complex_weierstrass_zeroth_coefficient_value R X K NX hNX Q v inclusion (q 0%N 0%N)
    quotient (hQ 0%N 0%N) hRepQ (0:K)).
  exact:hQNonzero 0.
- exists w;split;first exact:hRepW.
  exists coefficients;split;first by move=>i.
  split.
  + move=>i;rewrite (hCoefficients i) /= linear0 hDZero (hLow i (ltn_ord i) 0) oppr0.
    reflexivity.
  + have [A [haA hw]]:=holomorphic_representative_holomorphic w.
    exists A;split;first exact:haA.
    split;first exact:hw.
    move=>x hx.
    change (holomorphic_representative_value power x+ -holomorphic_representative_value remainder x=
      (xi x)^+k+\sum_(i<k) (xi x)^+i*holomorphic_representative_value (coefficients i) (projection x)).
    rewrite hPowerValues hRValues;congr ((xi x)^+k+_).
    rewrite -sumrN;apply:eq_bigr=>i _;by rewrite (hCoefficients i) /= mulrN.
Qed.
End Preparation.
