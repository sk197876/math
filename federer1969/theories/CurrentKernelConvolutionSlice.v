(** Federer (1969), 4.1.18, p. 374: the
    actual compact-test convolution is a genuine
    compact-kernel Cartesian slice of one compact
    addition-pullback replacement. This retains every
    original spatial point.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanAdditiveGroup EuclideanBlockCoordinates Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing PairingLinear CurrentSpaces
  CurrentCoefficientNorms CurrentDiracDensity EuclideanCartesianMap CurrentCartesianDomain CurrentCartesianVectorProduct
  CurrentCartesianSliceSealed CurrentKernelAverageUP CurrentKernelAverageSealed
  CurrentKernelAverageSliceIntegral CurrentAdditionZeroFactorPullback CompactKernelTranslationTests
  CurrentTranslations CurrentSmoothingOperators CurrentTestSmoothingTranslationIntegral
  CurrentFormVectorIntegralPairing CurrentTranslationParameterHomotopy
  SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackSealed
  SmoothingKernelUP SmoothingDilationUP SmoothingReflectedWeight
  EuclideanLebesgueDimensions MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentKernelConvolutionSlice.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation E:=(@current_smooth_space R h2 n Full hFull j).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull j).
Local Notation DT:=(@current_test_space R h2 n Full hFull j).
Local Notation value:=(@current_test_value R h2 n Full hFull j).
Local Notation DC:=(@current_test_space R h2 (n+n)%N AB hAB j).
Local Notation tv:=(@current_test_value R h2 (n+n)%N AB hAB j).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation hS:=(@CurrentKernelAverage.laws R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation Slice:=(@CartesianSlice.value R h2 n n 0%N j Full Full hFull hFull S).
Local Notation Q:=(@current_test_smoothing R h2 n j phi family hPhi hFamily epsilon).

(** Source for [current_kernel_convolution_slice]: one
    compact product test realises both the original
    test convolution and every kernel-strip translated
    coefficient in Federer 4.1.18, p. 374. *)
Theorem current_kernel_convolution_slice (omega:DT):
  exists theta:DC,Slice theta=Q omega /\
    forall z,NX z<=epsilon ->forall x eta,
      pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
        (tv theta (@euclidean_block_join R n n (z,x)))=
      pairing eta (value (@current_translation_test R h2 n j z omega) x).
Proof.
have [K hK]:=smooth_test_support_bound hE omega.
have [Replace hReplace]:=@compact_kernel_translation_tests R h2 n j epsilon K.
pose theta:=Replace (smooth_test_inclusion hE omega).
have hPoint z:NX z<=epsilon ->forall x eta,
    pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
      (tv theta (euclidean_block_join (z,x)))=
    pairing eta (value (@current_translation_test R h2 n j z omega) x).
  move=>hz x eta.
  rewrite (@hReplace (smooth_test_inclusion hE omega) hK z x hz)
    (@current_addition_zero_factor_pullback R h2 n j
      (smooth_test_inclusion hE omega) z x eta)
    current_translation_test_values /euclidean_translation addrC.
  reflexivity.
exists theta;split;last exact:hPoint.
apply:(smooth_test_values_extensional hE)=>x _;apply:pairing_ext=>eta.
have hSlice:=@current_kernel_average_slice_integral R h2 n n j Full hFull
  w S hS theta x Logic.I eta.
have hVector:=@current_test_smoothing_translation_integral R h2 n j phi family hPhi hFamily
  epsilon hEpsilon omega x.
have hScalar:=@current_form_vector_integral_pairing R h2 n j X
  (@euclidean_lebesgue_measure R n)
  (fun z=>w z*:value (@current_translation_test R h2 n j z omega) x)
  (value (Q omega) x) eta hVector.
have hFunction:(fun z=>w z*
    pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
      (tv theta (euclidean_block_join (z,x))))=
    (fun z=>pairing eta (w z*:value (@current_translation_test R h2 n j z omega) x)).
  apply:funext=>z.
  change (w z*pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
      (tv theta (euclidean_block_join (z,x)))=
    pairing_right eta (w z*:value (@current_translation_test R h2 n j z omega) x)).
  rewrite linearZ_LR pairing_rightE.
  case:(leP (NX z) epsilon)=>[hz|hz].
  - by rewrite (hPoint z hz x eta).
  - have hZero:family epsilon (-z)=0:=@smoothing_reflected_weight_off R n phi family
      hPhi hFamily epsilon hEpsilon z hz.
    by rewrite hZero !mul0r scale0r.
rewrite hFunction in hSlice.
have hEqual:=measure_integral_unique hSlice hScalar.
by injection hEqual.
Qed.
End CurrentKernelConvolutionSlice.
