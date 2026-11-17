(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    pp. 324–325: a nonzero holomorphic germ with zero value
    has an actual positive finite directional order. Reuse the
    first nonzero jet, opaque complex forms and polarization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ComplexScalarCharacteristicZero SymmetricForms SymmetricFormWords
  SymmetricFormExtension HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermOperationsUP
  HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  HolomorphicGermFirstNonzeroJet ComplexWeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_regular_direction_exists]: the
    original direction used in complex finite generation and
    factorization, extending 3.4.7, p. 325. The source
    need not be finite dimensional or complete. *)
Theorem holomorphic_germ_regular_direction_exists (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X)):
  alpha<>@holomorphic_germ_zero R X NX (complex_norm_real hNX) 0 ->
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 0%N alpha=0 ->
  exists k,exists v:X,is_complex_weierstrass_regular_germ hNX alpha k v.
Proof.
move=>hAlpha hZeroth.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose hNXR:=complex_norm_real hNX.
pose hN:=@complex_modulus_real_norm R.
pose N:=@complex_modulus R.
pose ev i:=@ContinuousMultilinear.evaluation R i XR CR NX N hNXR hN.
pose jet:=@HolomorphicGermJets.value R X NX hNXR 0.
pose F i:=@HolomorphicGermForms.value R X NX hNX 0 i alpha.
have hF i:=@HolomorphicGermForms.laws R X NX hNX 0 i alpha.
have [k [hk hLower]]:=holomorphic_germ_first_nonzero_jet hAlpha.
have hPositive:(0<k)%N.
  case:k hk hLower=>[|k] hk hLower;last by [].
  exfalso;apply:hk;exact:hZeroth.
have hForm:F k<>0.
  move=>hZero;apply:hk.
  apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R k XR CR NX N hNXR hN))=>u.
  have hTuple:[ffun j=>tnth [tuple u i|i<k] j]=u.
    by apply/ffunP=>j;rewrite ffunE tnth_mktuple.
  have hh:=hF k [tuple u i|i<k].
  rewrite /F in hZero.
  rewrite hZero sform_zeroE hTuple in hh.
  by rewrite linear0;exact:esym hh.
have hNonzero:exists v:X,sform_polynomial_value (F k) v<>0.
  apply:contrapT=>hNo;apply:hForm.
  apply:(@sform_polynomial_zero_iff (ComplexScalars.C R) X (ComplexScalars.C R)^o k
    (@complex_scalar_characteristic_zero R) (F k)).1=>v.
  apply:contrapT=>h;apply:hNo;by exists v.
have [v hv]:=hNonzero.
exists k,v;split;first exact:hPositive.
split.
- move=>i hi;by rewrite (@HolomorphicGermForms.laws R X NX hNX 0 i alpha) (hLower i hi) linear0.
- move=>hZero;apply:hv.
  by rewrite sform_polynomial_diagonal_value /F hZero scaler0.
Qed.
