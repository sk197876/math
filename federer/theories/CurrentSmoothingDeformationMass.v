(** Federer (1969), 4.1.18, p. 375: the
    original smoothing deformation satisfies
    M(H_epsilon T)<=epsilon M(T). The proof uses
    the literal scalar average and each fixed-z
    identity-spatial-derivative estimate, preserving the
    sharp coefficient one.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentMassBasic CurrentGlobalComassSealed
  ExtendedSupremumUP CurrentTranslationChain CurrentTranslationChainMass
  CurrentSmoothingDeformationUP SmoothingKernelUP SmoothingDilationUP
  SmoothingReflectedWeight EuclideanLebesgueDimensions SummableRealFunctionUP
  SummableRealArithmetic MeasureIntegralUP MeasureIntegralComparison
  RealTotalCharacteristicBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingDeformationMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation mu:=(@euclidean_lebesgue_measure R n).
Local Notation hm:=(euclidean_lebesgue_is_measure R n).
Variable T:@current_space R h2 n Full hFull m.
Variable Q:@current_space R h2 n Full hFull (1+m)%N.
Hypothesis hQ:@is_current_smoothing_deformation R h2 n m family epsilon T Q.
Local Notation M:=(@CurrentMass.value R h2 n m Full hFull T).
Local Notation MQ:=(@CurrentMass.value R h2 n (1+m)%N Full hFull Q).
Local Notation action:=(@current_value R h2 n Full hFull (1+m)%N).

(** Source for [current_smoothing_deformation_finite_mass]:
    the original epsilon mass estimate, 4.1.18,
    p. 375, for an arbitrary actual finite-mass
    input, with no normality or compactness premise. *)
Theorem current_smoothing_deformation_finite_mass (b:R):
  M=b%:E ->(MQ<=(epsilon*b)%R%:E)%E.
Proof.
move=>hMass.
have hb:0<=b.
  have h:=@current_mass_nonnegative R h2 n m Full hFull T.
  by rewrite hMass lee_fin in h.
have hWeight:=@smoothing_reflected_weight_integral_one R n phi family
  hPhi hFamily epsilon hEpsilon.
have hBound:=@real_total_integral_scale R X mu hm w 1 (epsilon*b) hWeight.
rewrite mulr1 in hBound.
apply:(extended_supremum_least (@CurrentMass.laws R h2 n (1+m)%N Full hFull Q))=>a
  [omega [hUnit <-]].
apply:(@measure_integral_monotone R X mu hm _ _ _ _ (hQ omega) hBound).
apply:(@real_total_pointwise_order_almost R X mu hm)=>z.
case:(leP (NX z) epsilon)=>hz.
- have hUnitBound:=@current_mass_unit_test_upper R h2 n (1+m)%N Full hFull
    (@current_translation_chain R h2 n m z T) omega hUnit.
  have hFibre:=@current_translation_chain_finite_mass R h2 n m z T b hMass.
  have hValue:action (@current_translation_chain R h2 n m z T) omega<=NX z*b.
    have h:=le_trans hUnitBound hFibre.
    by rewrite lee_fin in h.
  have hValueBound:=le_trans hValue (ler_wpM2r hb hz).
  have hPositive:=@smoothing_reflected_weight_nonnegative R n phi family
    hPhi hFamily epsilon hEpsilon z.
  change (is_true (w z*action (@current_translation_chain R h2 n m z T) omega<=
    (epsilon*b)*w z)).
  rewrite [(epsilon*b)*w z]mulrC.
  exact:(@ler_wpM2l R (w z) hPositive
    (action (@current_translation_chain R h2 n m z T) omega) (epsilon*b) hValueBound).
- have hZero:family epsilon (-z)=0:=@smoothing_reflected_weight_off R n phi family
    hPhi hFamily epsilon hEpsilon z hz.
  by rewrite hZero !mul0r mulr0.
Qed.

(** Source for [current_smoothing_deformation_mass]: the
    full original M(H_epsilon T)<=epsilon M(T)
    assertion, Federer 4.1.18, p. 375,
    including infinite mass and every natural degree. *)
Theorem current_smoothing_deformation_mass:(MQ<=epsilon%:E*M)%E.
Proof.
case:(ltP M (+oo)%E)=>hFinite.
- have[b [_ hMass]]:=@current_finite_mass_value R h2 n m Full hFull T hFinite.
  rewrite hMass -EFinM.
  exact:current_smoothing_deformation_finite_mass hMass.
- have hInfinity:M=(+oo)%E by apply/eqP;rewrite eq_le hFinite leey.
  by rewrite hInfinity gt0_muley ?lte_fin // leey.
Qed.
End CurrentSmoothingDeformationMass.
