(** Federer (1969), 3.4.12, p. 339:
    geometrically bounded original complex homogeneous coefficients
    define an actual holomorphic germ. Apply the existing
    real polarization bound to the exact scalar restrictions,
    then the proved complex normal-series connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm SymmetricForms HomogeneousPolynomialFunctions PolynomialNorm PolynomialPolarizationNorm
  FactorialExponentialBound SymmetricOperatorNorm ContinuousSymmetricFormAdapter
  ComplexSymmetricFormRestriction ComplexSymmetricPolynomialRestriction
  AnalyticJetMajorant HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsSealed
  HolomorphicFormSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Realisation.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).

(** Source for [holomorphic_homogeneous_germ_realisation]: the
    actual complex analytic sum needed for 3.4.6,
    p. 323, in its extension of 3.4.12,
    p. 339. Original homogeneous functions and
    their geometric bounds are the only coefficient premises;
    the output has every original complex Taylor coefficient. *)
Theorem holomorphic_homogeneous_germ_realisation (P:nat->X->C) (A B:R):
  0<A ->0<B ->
  (forall m,@is_homogeneous_polynomial C X C^o m (P m)) ->
  (forall m v,NX v<=1 ->NC (P m v)<=A*B^+m) ->
  exists alpha:holomorphic_germ_space hNXR (0:X),forall m x,
    P m x=sform_polynomial_value (@HolomorphicGermForms.value R X NX hNX 0 m alpha) x.
Proof.
move=>hA hB hP hBound.
pose F m:=projT1 (cid (hP m)).
have hF m:=projT2 (cid (hP m)).
have hRestriction m:=@complex_symmetric_form_real_exists R X C^o m (F m).
pose G m:=projT1 (cid (hRestriction m)).
have hG m:=projT2 (cid (hRestriction m)).
have hFunction m x:P m x=sform_polynomial_value (G m) x.
  rewrite (hF m x);exact:esym (complex_symmetric_polynomial_real_value (hG m) x).
have hNorm m:(@symmetric_operator_norm R XR CR NX hNXR.1 NC m (G m)<=
    (A*(4*B)^+m*(m`!)%:R)%:E)%E.
  have hPolynomial:(@polynomial_norm R XR CR NX hNXR.1 NC (sform_polynomial_value (G m))<=
      (A*B^+m)%:E)%E.
    apply:(@polynomial_norm_bound R XR CR NX hNXR.1 NC (sform_polynomial_value (G m)) _).2=>v hv.
    rewrite -(hFunction m v);exact:hBound m v hv.
  have hPolar:=@polynomial_polarization_finite_norm_bound R XR CR NX NC hNXR hNC.1
    m (G m) (A*B^+m) hPolynomial.
  have hExp:=ler_wpM2r (mulr_ge0 (ltW hA) (exprn_ge0 m (ltW hB)))
    (@factorial_exponential_bound R m).
  have hRight:(4:R)^+m*(m`!)%:R*(A*B^+m)=A*(4*B)^+m*(m`!)%:R.
    by rewrite exprMn;ring.
  rewrite hRight in hExp;exact:le_trans hPolar (lee_tofin hExp).
have hGBound m:@norm_bounded_symmetric_form R m XR CR NX NC (G m).
  exact:(@finite_operator_norm_sform_bounded R m XR CR NX NC hNXR hNC (G m)
    (A*(4*B)^+m*(m`!)%:R) (hNorm m)).
pose c:=(A+1)*(4*B+1).
have hc:0<c.
  apply:mulr_gt0;first exact:addr_gt0 hA ltr01.
  have hFour:0<4*B by rewrite mulr_gt0 // ltr0n.
  exact:addr_gt0 hFour ltr01.
have hGrowth m (hm:(1<=m)%N):
    (@symmetric_operator_norm R XR CR NX hNXR.1 NC m (G m)<=(c^+m*(m`!)%:R)%:E)%E.
  apply:le_trans (hNorm m) _;rewrite lee_fin.
  exact:(@analytic_factorial_growth_majorant R A (4*B) m (ltW hA)
    (mulr_ge0 (ler0n R 4) (ltW hB)) hm).
have [alpha hJets]:=@holomorphic_form_series_realisation R X NX hNX F G 0 c
  hG hc hGBound hGrowth.
exists alpha=>m x.
have hForm:@HolomorphicGermForms.value R X NX hNX 0 m alpha=F m.
  apply:sform_ext=>t.
  rewrite (@HolomorphicGermForms.laws R X NX hNX 0 m alpha t);exact:hJets m t.
by rewrite hForm hF.
Qed.
End Realisation.
