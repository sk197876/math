(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(14), p. 336:
    multiply the actual directional witnesses from the
    irreducible components. Existing least-order selection,
    original germ coefficient convolution and the initial
    coefficient identity prove a positive nonzero derivative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import PolynomialDiagonalNorm ScalarRestriction ComplexScalarSealed ComplexNormUP SymmetricForms HolomorphicGermFormsSealed Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermJetsSealed HolomorphicReductionLociUP
  ComplexWeierstrassRegularUP ComplexWeierstrassRegularCoefficients HolomorphicDirectionalRegularOrder
  HolomorphicGermDirectionalCoefficient HolomorphicGermDirectionalProduct NaturalConvolution
  NaturalConvolutionInitialCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_directional_product_nonzero]: the
    original product Phi in 3.4.8(14), p. 336,
    has a positive nonzero derivative in the same
    direction as its factors. Vanishing centre values
    are essential and follow from proper ideal membership. *)
Theorem holomorphic_directional_product_nonzero (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX)
    (alpha beta:[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)]) v:
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 0%N alpha=0 ->
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 0%N beta=0 ->
  has_nonzero_holomorphic_directional_jet hNX alpha v ->
  has_nonzero_holomorphic_directional_jet hNX beta v ->
  has_nonzero_holomorphic_directional_jet hNX (alpha*beta) v.
Proof.
move=>hA0 hB0 hA hB.
have [k hK]:=holomorphic_directional_regular_order_exists hA0 hA.
have [l hL]:=holomorphic_directional_regular_order_exists hB0 hB.
pose a i:=@holomorphic_germ_directional_coefficient R X NX hNX 0 i alpha v.
pose b i:=@holomorphic_germ_directional_coefficient R X NX hNX 0 i beta v.
have hLowA i (hi:(i<k)%N):a i=0.
  by rewrite /a /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value (hK.2.1 i hi) scaler0.
have hLowB i (hi:(i<l)%N):b i=0.
  by rewrite /b /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value (hL.2.1 i hi) scaler0.
have hANonzero:a k<>0.
  rewrite /a /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value.
  exact:complex_weierstrass_regular_leading_nonzero hK.
have hBNonzero:b l<>0.
  rewrite /b /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value.
  exact:complex_weierstrass_regular_leading_nonzero hL.
have hCoefficient:@holomorphic_germ_directional_coefficient R X NX hNX 0 (k+l)%N (alpha*beta) v=a k*b l.
  rewrite holomorphic_germ_directional_coefficient_product.
  have hSum:(\sum_(j<(k+l).+1) a (k+l-j)%N*b j)=
      natural_coefficient_convolution b a (l+k)%N.
    rewrite [(l+k)%N]addnC /natural_coefficient_convolution big_mkord.
    apply:eq_bigr=>j _;exact:mulrC.
  rewrite hSum (natural_convolution_initial_coefficient hLowB hLowA);exact:mulrC.
exists (k+l)%N;split.
- have hKLe:(k<=k+l)%N by rewrite leq_addr.
  exact:leq_trans hK.1 hKLe.
- move=>hZero.
  have hProductZero:a k*b l=0.
    rewrite -hCoefficient /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value hZero scaler0;reflexivity.
  have /orP [hAZero|hBZero]:(a k==0)||(b l==0).
    by rewrite -mulf_eq0 hProductZero eqxx.
  + exact:hANonzero (elimT eqP hAZero).
  + exact:hBNonzero (elimT eqP hBZero).
Qed.
