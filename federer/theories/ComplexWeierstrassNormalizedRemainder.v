(** Federer (1969), 3.4.12, p. 339, extending 3.4.6, pp. 323–324: the
    normalized original recursion gives actual analytic quotient
    and remainder germs with every required high coefficient zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus HolomorphicLinear HolomorphicGermUP HolomorphicGermSealed
  SymmetricForms HolomorphicGermFormsUP HolomorphicGermFormsSealed ComplexWeierstrassRegularUP
  ComplexWeierstrassRegularCoefficients ComplexWeierstrassCoefficientUP ComplexWeierstrassCoefficientExistence
  ComplexWeierstrassCoefficientProduct ComplexWeierstrassCoefficientDifference ComplexWeierstrassTransverseUP
  ComplexWeierstrassActualRecursion WeierstrassRingRecursionConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_normalized_remainder_exists]:
    in the auxiliary normalized case, actual analytic
    Q,R satisfy the original germ division equation and
    R_(i,j)=0 for every i>=k, 3.4.6,
    pp. 323–324. The original all-nearby-point
    directional derivative condition is proved separately;
    it is not assumed here. *)
Theorem complex_weierstrass_normalized_remainder_exists (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (Phi Psi:holomorphic_germ_space (complex_norm_real hNX) (0:X)) k:
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->is_complex_weierstrass_regular_germ hNX Phi k v ->
  ((((k`!)%:R)^-1:ComplexScalars.C R)*
    @HolomorphicGermForms.value R X NX hNX 0 k Phi [tuple v | j<k])= 1 ->
  exists Q T:holomorphic_germ_space (complex_norm_real hNX) (0:X),exists t:nat->nat->K->ComplexScalars.C R,
    T=@HolomorphicGerms.add R X NX (complex_norm_real hNX) 0 Psi
      (@HolomorphicGerms.opp R X NX (complex_norm_real hNX) 0 (@HolomorphicGerms.mul R X NX (complex_norm_real hNX) 0 Phi Q)) /\
    (forall i j,is_complex_weierstrass_split_coefficient hNX T v inclusion i j (t i j)) /\
    forall i,(k<=i)%N ->forall j z,t i j z=0.
Proof.
move=>hSplit hXi hRegular hUnit.
have [phi hPhi]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Phi v inclusion.
have [psi hPsi]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Psi v inclusion.
have [Q [q [hQ hRec]]]:=@complex_weierstrass_actual_recursive_germ_exists R X K NX NK hNX hNK
  v xi inclusion projection Phi Psi phi psi k hSplit hXi hPhi hPsi.
pose M:=@HolomorphicGerms.mul R X NX (complex_norm_real hNX) 0 Phi Q.
pose T:=@HolomorphicGerms.add R X NX (complex_norm_real hNX) 0 Psi (@HolomorphicGerms.opp R X NX (complex_norm_real hNX) 0 M).
have [p hP]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX M v inclusion.
have [t hT]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX T v inclusion.
have hLow:=@complex_weierstrass_regular_low_coefficients R X K NX hNX Phi k v inclusion phi hRegular hPhi.
have hLeading:=@complex_weierstrass_normalized_leading_coefficient R X K NX hNX Phi k v inclusion
  (phi k 0%N) (hPhi k 0%N) hUnit.
have hConvolution:=@weierstrass_ring_recursion_convolution (ComplexScalars.C R) K phi psi q k hLow hLeading hRec.
have hProduct:=@complex_weierstrass_split_coefficient_product R X K NX hNX Phi Q v inclusion phi q p hPhi hQ hP.
exists Q,T,t;split;first reflexivity.
split;first exact:hT.
move=>i hi j z.
have hIndex:(i-k+k)%N = i:=subnK hi.
have hActual:p i j z=psi i j z.
  have hAt:=hConvolution (i-k)%N j z.
  rewrite hIndex in hAt.
  rewrite hProduct hAt.
  apply:eq_bigr=>mu _;apply:eq_bigr=>nu _.
  exact:mulrC.
have hDifference:=@complex_weierstrass_split_coefficient_difference R X K NX hNX Psi M v inclusion i j
  (psi i j) (p i j) (t i j) (hPsi i j) (hP i j) (hT i j) z.
by rewrite hDifference hActual subrr.
Qed.
