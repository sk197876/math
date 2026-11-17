(** Federer (1969), 3.4.12, p. 339: the original
    neighbourhood remainder condition forces all high mixed rows
    to vanish. Reuse actual divided coefficient fields and the
    vector-valued real Taylor comparison on the same original lines. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormRegularity NormHigherDifferentialUP
  NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal NormAnalyticHigherJet NormTaylorLineValues
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermRepresentatives
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine ComplexWeierstrassDivisionUP
  ComplexWeierstrassCoefficientUP ComplexWeierstrassIteratedGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficients.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNXR hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNXR hN).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNXR hN).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m XR CR NX N hNXR hN).

(** Source for [complex_weierstrass_polynomial_high_coefficients]: every
    actual complex division candidate has zero mixed rows of
    distinguished degree at least k, extending 3.4.6(1), p. 322,
    under 3.4.12, p. 339. No coefficient vanishing premise
    is added to the original division theorem. *)
Theorem complex_weierstrass_polynomial_high_coefficients k v (inclusion:Hom K X)
    (rho:holomorphic_germ_space hNXR (0:X)) (r:nat->nat->K->C):
  @is_complex_directional_polynomial_germ R X NX hNXR k v rho ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX rho v inclusion i j (r i j)) ->
  forall i,(k<=i)%N ->forall j z,r i j z=0.
Proof.
move=>[f [hRep [U [ha [hf hVanish]]]]] hR i hi j z.
pose F:=holomorphic_representative_value f.
have hOpen x (hx:U x):@norm_domain_interior R XR NX U x:=
  ((norm_analytic_class_all_orders hf.1 0%N).1 x hx).1.
have [D [hD hAnalyticD]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN U F i v hf.1.
have [E [hE _]]:=@norm_analytic_higher_jet_exists R XR CR NX N hNXR hN i U F hf.1.
have hZero x (hx:U x):D x=0.
  have hFull:=(@norm_higher_differential_open_restriction R XR CR NX N hNXR hN Z ev ZN hZ
    i setT U F (fun x _=>Logic.I) hOpen x hx (E x)).2 (hE x hx).
  have hValue:=hVanish i hi x hx (E x) hFull.
  by rewrite (hD x hx (E x) (hE x hx)) hValue scaler0.
have [P [hP _]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN U D j (inclusion z) hAnalyticD.
have hOriginal:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX rho f U v inclusion
  i j (r i j) D P z hRep ha hf.1 (hR i j) hD hP.
have [delta [hDelta hBall]]:=hOpen 0 ha.
have [radius [hRadius hSmall]]:=@norm_scalar_line_small_increments R XR NX hNXR (inclusion z) delta hDelta.
have hLine (t:R) (ht:`|t|<radius):D ((0:XR)+t*:(inclusion z:XR))=\sum_(m<0) t^+m*:(0:CR).
  rewrite big_ord0;apply:hZero;exact:hBall _ (hSmall t ht).
have hFinite:=@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN
  U D j (inclusion z) 0 P 0%N (fun _=>0) radius ha hAnalyticD hP hRadius hLine.
by rewrite hOriginal ltn0 in hFinite *.
Qed.
End Coefficients.
