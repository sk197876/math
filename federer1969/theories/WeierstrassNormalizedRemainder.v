(** Federer (1969), 3.4.6, pp. 323–324: the
    normalized original recursion gives actual analytic quotient
    and remainder germs with every required high coefficient zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermSealed AnalyticGermJetsSealed WeierstrassRegularUP
  WeierstrassRegularCoefficients WeierstrassCoefficientUP WeierstrassCoefficientExistence
  WeierstrassCoefficientProduct WeierstrassCoefficientDifference WeierstrassTransverseUP
  WeierstrassActualRecursion WeierstrassRecursionConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_normalized_remainder_exists]:
    in the auxiliary normalized case, actual analytic
    Q,R satisfy the original germ division equation and
    R_(i,j)=0 for every i>=k, 3.4.6,
    pp. 323–324. The original all-nearby-point
    directional derivative condition is proved separately;
    it is not assumed here. *)
Theorem weierstrass_normalized_remainder_exists (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (Phi Psi:analytic_germ_space hNX (0:X)) k:
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  norm_bounded_linear NX (fun r:R^o=>`|r|) xi ->is_weierstrass_regular_germ Phi k v ->
  ((k`!)%:R)^-1*@ContinuousMultilinear.evaluation R k X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
    (@AnalyticGermJets.value R X NX hNX 0 k Phi)= 1 ->
  exists Q T:analytic_germ_space hNX (0:X),exists t:nat->nat->K->R,
    T=@AnalyticGerms.add R X NX hNX 0 Psi
      (@AnalyticGerms.opp R X NX hNX 0 (@AnalyticGerms.mul R X NX hNX 0 Phi Q)) /\
    (forall i j,is_weierstrass_split_coefficient T v inclusion i j (t i j)) /\
    forall i,(k<=i)%N ->forall j z,t i j z=0.
Proof.
move=>hSplit hXi hRegular hUnit.
have [phi hPhi]:=@weierstrass_split_coefficients_exist R X K NX hNX Phi v inclusion.
have [psi hPsi]:=@weierstrass_split_coefficients_exist R X K NX hNX Psi v inclusion.
have [Q [q [hQ hRec]]]:=@weierstrass_actual_recursive_germ_exists R X K NX NK hNX hNK
  v xi inclusion projection Phi Psi phi psi k hSplit hXi hPhi hPsi.
pose M:=@AnalyticGerms.mul R X NX hNX 0 Phi Q.
pose T:=@AnalyticGerms.add R X NX hNX 0 Psi (@AnalyticGerms.opp R X NX hNX 0 M).
have [p hP]:=@weierstrass_split_coefficients_exist R X K NX hNX M v inclusion.
have [t hT]:=@weierstrass_split_coefficients_exist R X K NX hNX T v inclusion.
have hLow:=@weierstrass_regular_low_coefficients R X K NX hNX Phi k v inclusion phi hRegular hPhi.
have hLeading:=@weierstrass_normalized_leading_coefficient R X K NX hNX Phi k v inclusion
  (phi k 0%N) (hPhi k 0%N) hUnit.
have hConvolution:=@weierstrass_recursion_convolution R K phi psi q k hLow hLeading hRec.
have hProduct:=@weierstrass_split_coefficient_product R X K NX hNX Phi Q v inclusion phi q p hPhi hQ hP.
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
have hDifference:=@weierstrass_split_coefficient_difference R X K NX hNX Psi M v inclusion i j
  (psi i j) (p i j) (t i j) (hPsi i j) (hP i j) (hT i j) z.
by rewrite hDifference hActual subrr.
Qed.
