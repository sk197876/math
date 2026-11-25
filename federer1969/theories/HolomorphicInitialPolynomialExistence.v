(** Federer (1969), 3.4.12, p. 339: the original nonzero
    vanishing holomorphic germ has a first nonzero homogeneous Taylor
    polynomial. Select the least actual nonzero jet, then reuse
    the original normalized complex polynomial theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm HilbertFormCompactness
  LinearBasis PolynomialFunctions HomogeneousPolynomialFunctions HolomorphicUP HolomorphicGermUP
  HolomorphicGermRing HolomorphicGermJetsSealed HolomorphicGermFirstNonzeroJet HolomorphicGermValueSealed
  HolomorphicGermValueZerothJet HolomorphicInitialPolynomialUP HolomorphicNormalizedJetPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_initial_polynomial_exists]: the original
    least positive order and its globally holomorphic polynomial in
    3.4.11, p. 338, extended by 3.4.12, p. 339.
    No derivative order, regular direction or polynomial is assumed. *)
Theorem holomorphic_initial_polynomial_exists (R:realType)
    (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
    (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
    (alpha:@holomorphic_germ_ring R X (inner_norm (hermitian_real_inner_product hH))
      (complex_norm_real (hermitian_complex_norm hH)) 0):
  alpha<>0 ->@HolomorphicGermValue.map R X (inner_norm (hermitian_real_inner_product hH))
    (complex_norm_real (hermitian_complex_norm hH)) 0 alpha=0 ->
  exists k (P:PolynomialFunction X (ComplexScalars.C R)^o),
    is_initial_holomorphic_germ_polynomial alpha k P /\
    @is_homogeneous_polynomial (ComplexScalars.C R) X (ComplexScalars.C R)^o k P /\
    @is_holomorphic R X (ComplexScalars.C R)^o (inner_norm (hermitian_real_inner_product hH))
      (@complex_modulus R) (complex_norm_real (hermitian_complex_norm hH))
      (@complex_modulus_real_norm R) setT P.
Proof.
move=>hNonzero hValue.
have hZero:=(@holomorphic_germ_value_zeroth_jet R X (inner_norm (hermitian_real_inner_product hH))
  (complex_norm_real (hermitian_complex_norm hH)) 0 alpha).1 hValue.
have [k [hTop hLower]]:=@holomorphic_germ_first_nonzero_jet R X
  (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH))
  0 alpha hNonzero.
have hPositive:(0<k)%N.
  case:k hTop hLower=>[|k] hTop hLower;last by [].
  exfalso;exact:hTop hZero.
have [P [hPolynomial [hHolomorphic hFormula]]]:=
  @holomorphic_normalized_jet_polynomial_exists R X H hH n e he k alpha.
exists k,P;split;last by split.
by split;last split;last split.
Qed.
