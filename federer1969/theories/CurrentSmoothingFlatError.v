(** Federer (1969), 4.1.18, p. 375: the
    actual original smoothing satisfies
    F_C(T_epsilon−T)<=epsilon N(T) on any compact
    C containing the closed support tube. Reuse
    the original probability average and fixed-z
    homotopy estimate, including infinite N and
    degree zero.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentNormalMass NormalCurrentsUP CurrentFlatNorm
  CurrentProbabilityAverageFlatBound CurrentTranslationFlatBound CurrentTranslations
  CurrentSmoothingOperators CurrentSmoothingTranslationAverage EuclideanClosedSupportTube
  SmoothCompactSet SmoothingKernelUP SmoothingDilationUP SmoothingReflectedWeight
  EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingFlatError.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Variable T:@current_space R h2 n Full hFull m.
Local Notation N:=(@current_normal_mass R h2 n Full hFull m T).
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily T epsilon).
Variable K:smooth_compact_set hNX Full.
Hypothesis hTube:@euclidean_closed_support_tube R n
  (@current_support R h2 n Full hFull m T) epsilon `<=` smooth_compact_carrier K.

(** Source for [current_smoothing_flat_error]: the
    displayed smoothing flat error of Federer
    4.1.18, p. 375. Finite N supplies its
    real value internally; infinite N retains
    the original extended inequality. *)
Theorem current_smoothing_flat_error:
  (@current_flat_norm R h2 n m Full hFull K (Smooth-T)<=epsilon%:E*N)%E.
Proof.
case:(ltP N (+oo)%E)=>hFinite.
- have hNonnegative:=@current_normal_mass_nonnegative R h2 n Full hFull m T.
  have hNumber:N \is a fin_num by rewrite (ge0_fin_numE hNonnegative).
  pose c:=fine N.
  have hN:N=c%:E by rewrite /c fineK.
  have hc:0<=c by have h:=hNonnegative;rewrite hN lee_fin in h.
  rewrite hN -EFinM.
  apply:(@current_probability_average_flat_bound R h2 n m Full hFull K X
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (fun z=>family epsilon (-z))
    (@smoothing_reflected_weight_nonnegative R n phi family hPhi hFamily epsilon hEpsilon)
    (@smoothing_reflected_weight_integral_one R n phi family hPhi hFamily epsilon hEpsilon)
    (fun z=>@current_translation_pushforward R h2 n m z T) Smooth T
    (@current_smoothing_translation_average R h2 n m phi family hPhi hFamily epsilon hEpsilon T)
    (epsilon*c)).
  move=>z hz.
  have hRadius:NX z<=epsilon.
    case:(leP (NX z) epsilon)=>// hFar.
    exfalso;apply:hz.
    exact:(@smoothing_reflected_weight_off R n phi family hPhi hFamily epsilon hEpsilon z hFar).
  have hShift:=@current_translation_flat_bound R h2 n K epsilon z hRadius m T hFinite hTube.
  rewrite hN -EFinM in hShift.
  apply:(le_trans hShift).
  rewrite lee_fin;exact:(@ler_wpM2r R c hc (NX z) epsilon hRadius).
- have hInfinity:N=(+oo)%E by apply/eqP;rewrite eq_le hFinite leey.
  by rewrite hInfinity gt0_muley ?lte_fin // leey.
Qed.
End CurrentSmoothingFlatError.
