(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 334:
    every original B_j witness supplies an
    actual prepared W_j equation in I_g.
    The original positive degree, vanishing lower
    coefficient values and holomorphic prefix domain
    are proved internally from the earlier preparation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct NormFiniteLinearBound HolomorphicUP OrthogonalGroupTopology HolomorphicGermUP
  HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicCoordinateGermsSealed FieldPrefixCoordinatesSealed
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicRotatedGermIdeal HolomorphicReductionActual
  CommutativeIdealUP CommutativePolynomialEvaluationUP CommutativePolynomialSealed CommutativePolynomialEvaluationSealed
  HolomorphicPrefixPreparedPolynomial DistinguishedHolomorphicPolynomialActualMonic PointedHolomorphicFunctionalGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PreparedEquation.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Variable I:set G.
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable j:'I_n.
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) j).
Local Notation NY:=(@holomorphic_coordinate_norm R j).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R j)).
Local Notation P:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (j:nat) hJN).

(** Source for [holomorphic_reduction_prepared_equation]:
    the original Weierstrass W_j and M_ij
    chosen in 3.4.8(11), p. 334,
    derived from actual B_j membership. No
    polynomial, equation or coefficient smallness is
    an extra hypothesis of this construction. *)
Theorem holomorphic_reduction_prepared_equation:
  is_commutative_ideal I ->~I 1 ->
  @holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g ->
  exists k,exists (U:set Y) (b:'I_k->@holomorphic_representative_type R Y NY hNY 0)
    (f:@holomorphic_representative_type R X NX hNXR 0),
    (0<k)%N /\ U 0 /\@open (real_norm_metric_space hNY) U /\
    (forall i,@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R)
      U (holomorphic_representative_value (b i))) /\
    (forall i,holomorphic_representative_value (b i) 0 = 0) /\
    @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (holomorphic_germ f) /\
    forall x,holomorphic_representative_value f x =
      (omega j x)^+k+\sum_(i<k) holomorphic_representative_value (b i) (P x)*(omega j x)^+(i:nat).
Proof.
move=>hI hProper hBj.
pose A:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
pose Poly:=CommutativePolynomial.space A.
pose embed:=CommutativePolynomial.embed A.
pose variable:=CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hPoly:=CommutativePolynomial.laws A.
pose E:=@holomorphic_prefix_germ_map R X NX hNXR n e he omega j hJN.
pose Gamma:=@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j.
pose J:=@CommutativePolynomialEvaluation.map A Poly G embed variable coefficient hPoly E Gamma.
have hJ:=@CommutativePolynomialEvaluation.laws A Poly G embed variable coefficient hPoly E Gamma.
have [_ [W [k [hK [hDistinguished hMember]]]]]:=
  @holomorphic_prefix_distinguished_ideal_polynomial R X Herm hHerm n e he omega hDual I g j
    Poly embed variable coefficient hPoly J hJ hI hProper hBj.
have hXiBound:=@norm_finite_linear_bounded R XR (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNXR
  (@complex_modulus_real_norm R) (n+n) eR heR (complex_hom_real (omega j)).
have [fXi hXiShift]:=@pointed_holomorphic_functional_representative_exists R X NX hNX 0 (omega j) hXiBound.
have hXi x:holomorphic_representative_value fXi x=omega j x by rewrite hXiShift subr0.
have hGamma:(holomorphic_germ fXi:G) = Gamma.
  exact:(@HolomorphicCoordinateGerms.laws R X NX hNX n e he omega j fXi hXi).
have hJActual:is_commutative_polynomial_evaluation embed variable E (holomorphic_germ fXi) J.
  by rewrite hGamma.
have [U [b [f [hU0 [hOpen [hHolomorphic [hZero [hGerm hValues]]]]]]]]:=
  @distinguished_holomorphic_polynomial_actual_monic R X Y NX NY hNXR hNY P E (omega j) fXi
    Poly embed variable coefficient hPoly J W k
    (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega j hJN) hXi hJActual hDistinguished.
exists k,U,b,f;split;first exact:hK.
split;first exact:hU0.
split;first exact:hOpen.
split;first exact:hHolomorphic.
split;first exact:hZero.
split;last exact:hValues.
by rewrite hGerm.
Qed.
End PreparedEquation.
