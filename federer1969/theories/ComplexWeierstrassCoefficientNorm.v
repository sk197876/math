(** Federer (1969), 3.4.12, p. 339: transfer the original
    mixed factorial bound of 3.4.6, p. 323, through exact
    scalar restriction. The established real contraction estimate
    applies to the same complex-valued form and modulus norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms PolynomialTaylorTerms PolynomialDiagonalNorm
  HomogeneousPolynomialFunctions SymmetricOperatorNorm SymmetricOperatorTupleBound WhitneyPolynomialDifferenceBound
  ComplexSymmetricFormRestriction ComplexSymmetricTaylorRestriction ComplexSymmetricPolynomialRestriction
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ContinuousMultilinearUP ContinuousMultilinearSealed ComplexWeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).

(** Source for [complex_weierstrass_split_coefficient_norm_bound]:
    the original norm bound for the complex mixed coefficient,
    retaining both factorials and the norm of the original
    distinguished direction, 3.4.12, p. 339. *)
Theorem complex_weierstrass_split_coefficient_norm_bound
    (alpha:holomorphic_germ_space hNXR (0:X)) (v:X) (inclusion:Hom K X)
    i j (Cij:K->C) (F:S_m X C^o (i+j)) (G:S_m XR CR (i+j)) (L:R):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j Cij ->
  (forall t,F t=@HolomorphicGermForms.value R X NX hNX 0 (i+j)%N alpha t) ->
  (forall t,G t=F t) ->(forall z,NX (inclusion z)=NK z) ->
  (@symmetric_operator_norm R XR CR NX hNXR.1 NC (i+j)%N G<=L%:E)%E ->
  forall z,NC (Cij z)<=L*NX v^+i*NK z^+j/((i`!)%:R*(j`!)%:R).
Proof.
move=>hC hF hG hNorm hBound z.
have hDerivative t:F t=@ContinuousMultilinear.evaluation R (i+j)%N XR CR NX NC
    hNXR hNC [ffun s=>tnth t s]
    (@HolomorphicGermJets.value R X NX hNXR 0 (i+j)%N alpha).
  by rewrite hF (@HolomorphicGermForms.laws R X NX hNX 0 (i+j)%N alpha t).
have hDegree:(j<=i+j)%N by rewrite leq_addl.
have hContraction:=@symmetric_taylor_term_operator_bound R XR CR NX NC hNXR hNC
  (i+j)%N j hDegree G v L hBound.
rewrite addnK in hContraction.
have hEvaluation:=@symmetric_operator_finite_tuple_bound R XR CR NX NC hNXR hNC.1
  j (symmetric_taylor_term j G v) (L*(NX v^+i/(i`!)%:R)) hContraction
  [tuple inclusion z | s<j].
have hProduct:(\prod_(s<j) NX (tnth [tuple inclusion z | t<j] s))=NK z^+j.
  under eq_bigr do rewrite tnth_mktuple hNorm.
  by rewrite prodr_const card_ord.
rewrite hProduct in hEvaluation.
have hTaylor t:symmetric_taylor_term j G v t=symmetric_taylor_term j F v t.
  exact:(@complex_symmetric_taylor_restriction R X C^o (i+j)%N F G hG j v t).
have hPolynomial:=@complex_symmetric_polynomial_real_value R X C^o j
  (symmetric_taylor_term j F v) (symmetric_taylor_term j G v) hTaylor (inclusion z).
rewrite (hC F hDerivative z) -hPolynomial sform_polynomial_diagonal_value.
have hInvNonnegative:0<=((j`!)%:R:R)^-1 by rewrite invr_ge0 ler0n.
have hBoundFinal:=ler_wpM2l hInvNonnegative hEvaluation.
rewrite (real_seminorm_scale hNC.1) normfV normr_nat.
have hRight:((j`!)%:R:R)^-1*(L*(NX v^+i/(i`!)%:R)*NK z^+j)=
    L*NX v^+i*NK z^+j/((i`!)%:R*(j`!)%:R).
  rewrite invfM;ring.
by rewrite hRight in hBoundFinal.
Qed.
End Bounds.
