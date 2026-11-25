(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 324: the
    diagonal polynomial of a nonzero actual derivative
    is nonzero. Actual jet symmetry and the proved
    polarization theorem supply a nonzero value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm Hom RealNormUP SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermJetsSealed
  HolomorphicGermRealCoefficientForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_nonzero_jet_diagonal]:
    the nonzero homogeneous derivative polynomial used
    in 3.4.7, p. 324. Every original
    centre and derivative order remain, without finite
    dimension or completeness. *)
Theorem holomorphic_germ_nonzero_jet_diagonal (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a k (alpha:holomorphic_germ_space hNX a):
  @HolomorphicGermJets.value R X NX hNX a k alpha<>0 ->
  exists v:X,@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
    hNX (@complex_modulus_real_norm R) [ffun _:'I_k=>v]
    (@HolomorphicGermJets.value R X NX hNX a k alpha)<>0.
Proof.
move=>hJet.
have [F [hF _]]:=@holomorphic_germ_coefficient_forms_exists R X NX hNX a alpha.
have hForm:F k<>0.
  move=>hZero;apply:hJet.
  apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R k (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX
    (@complex_modulus R) hNX (@complex_modulus_real_norm R)))=>u.
  have hTuple:[ffun j=>tnth [tuple u i|i<k] j] = u.
    by apply/ffunP=>j;rewrite ffunE tnth_mktuple.
  have hh:=hF k [tuple u i|i<k].
  rewrite hZero sform_zeroE hTuple in hh.
  by rewrite linear0;exact:esym hh.
have hNonzero:exists v:X,sform_polynomial_value (F k) v<>0.
  apply:contrapT=>hNo;apply:hForm.
  apply:(@sform_polynomial_zero_iff R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) k (@pchar_num R) (F k)).1=>v.
  apply:contrapT=>h;apply:hNo;by exists v.
have [v hv]:=hNonzero;exists v=>hZero;apply:hv.
rewrite sform_polynomial_diagonal_value.
have hh:=hF k [tuple v|_<k].
have hTuple:[ffun j:'I_k=>tnth [tuple v|_<k] j] = [ffun _:'I_k=>v].
  by apply/ffunP=>j;rewrite !ffunE tnth_mktuple.
by rewrite hh hTuple hZero scaler0.
Qed.
