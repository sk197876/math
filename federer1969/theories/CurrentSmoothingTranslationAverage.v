(** Federer (1969), 4.1.18, p. 374: the
    original T_epsilon is the literal reflected-kernel
    average of tau_z#T on every actual compact
    test. The scalar integral follows from the
    old all-test Cartesian interchange, for arbitrary
    T.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import EuclideanCartesianMap Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentSpaces CurrentEvaluation
  CurrentDiracDensity CurrentDegreeTransport CurrentCartesianDomain CurrentCartesianVectorProduct
  CurrentCartesianProductSealed CurrentCartesianProductAction CurrentCartesianSwapTests
  CurrentCartesianZeroSwapSlice CurrentCartesianSliceSealed CurrentCartesianSliceTestSealed
  CurrentKernelAverageUP CurrentKernelAverageSealed CurrentKernelAverageFubini
  CurrentKernelConvolutionSlice CurrentTranslations CurrentSmoothingOperators
  SmoothTestSpaces SmoothTestEvaluation SmoothingKernelUP SmoothingDilationUP
  SmoothingReflectedWeight EuclideanLebesgueDimensions SummableRealFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingTranslationAverage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation C:=(@current_space R h2 n Full hFull j).
Local Notation DT:=(@current_test_space R h2 n Full hFull j).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull j).
Local Notation action:=(@current_value R h2 n Full hFull j).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation hS:=(@CurrentKernelAverage.laws R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation Smooth:=(@current_smoothing R h2 n j phi family hPhi hFamily).

(** Source for [current_smoothing_translation_average]: the
    exact scalar action of the displayed integral
    T_epsilon=integral Phi_epsilon(-z) tau_z#T dz,
    Federer 4.1.18, p. 374. Compact support,
    finite mass and representability of T are
    not added as hypotheses. *)
Theorem current_smoothing_translation_average (T:C) (omega:DT):
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z=>w z*
      action (@current_translation_pushforward R h2 n j z T) omega))
    (action (Smooth T epsilon) omega)%:E.
Proof.
have [theta [hConvolution hPoint]]:=@current_kernel_convolution_slice R h2 n j
  phi family hPhi hFamily epsilon hEpsilon omega.
pose Reverse:=@current_cartesian_swap_tests R h2 n n (j+0)%N Full Full hFull hFull
  (@current_test_degree_transport R h2 (n+n)%N AB hAB j (j+0)%N
    (esym (addnC j 0%N)) theta).
pose beta z:=@CartesianSliceTest.value R h2 n n Full Full hFull hFull j 0%N
  z Logic.I unit Reverse.
have hBeta z:NX z<=epsilon ->beta z=@current_translation_test R h2 n j z omega.
  move=>hz;apply:(smooth_test_values_extensional hE)=>x _.
  apply:pairing_ext=>eta.
  rewrite (@current_cartesian_zero_swap_slice_pairing R h2 n j theta z x eta).
  exact:hPoint z hz x eta.
have hAverage:=@current_kernel_average_cartesian_integral R h2 n j w S hS T theta.
have hFunction:(fun z=>w z*action T (beta z))=
    (fun z=>w z*action (@current_translation_pushforward R h2 n j z T) omega).
  apply:funext=>z.
  case:(leP (NX z) epsilon)=>[hz|hz].
  - by rewrite (hBeta z hz) current_translation_pushforward_action.
  - have hZero:family epsilon (-z)=0:=@smoothing_reflected_weight_off R n phi family
      hPhi hFamily epsilon hEpsilon z hz.
    by rewrite hZero !mul0r.
change (is_measure_integral (@euclidean_lebesgue_measure R n)
  (real_total_integrand (fun z=>w z*action T (beta z)))
  (@current_value R h2 (n+n)%N AB hAB j
    (@CartesianCurrentProduct.value R h2 n n 0%N j Full Full hFull hFull S T) theta)%:E)
  in hAverage.
rewrite hFunction current_cartesian_product_action hConvolution in hAverage.
rewrite (@current_smoothing_action R h2 n j phi family hPhi hFamily
  T epsilon hEpsilon omega).
exact:hAverage.
Qed.
End CurrentSmoothingTranslationAverage.
