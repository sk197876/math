(** Federer (1969), 4.1.18, p. 374: existence
    of the original smoothing deformation. The
    preceding continuous parameter-product chain realises
    the independent literal fixed-z integral law.
    Compact transgression representatives and the old
    Cartesian interchange handle arbitrary currents. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading AlternatingForms AlternatingPairing CurrentSpaces CurrentDegreeTransport
  CurrentDiracDensity CurrentEqualDomainTests SmoothTestSpaces SmoothTestEvaluation
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianSwapTests
  CurrentCartesianSliceTestSealed CurrentCartesianZeroSwapSlice CurrentKernelAverageUP
  CurrentKernelAverageSealed CurrentKernelAverageFubini CurrentKernelParameterTest
  CurrentKernelSmoothingChainWitness CurrentKernelSmoothingWitnessAction
  CurrentKernelTransgressionCompactTests CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTransgressionSealed CurrentTranslationParameterHomotopy
  CurrentTranslationHomotopy CurrentTranslationTransgressionFibre
  CurrentTranslationChain CurrentTranslationChainTestAction CurrentTranslations EuclideanAdditiveGroup
  CurrentSmoothingDeformationUP SmoothingKernelUP SmoothingDilationUP
  SmoothingReflectedWeight EuclideanLebesgueDimensions SummableRealFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingDeformationExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun d:nat=>fun _:R_n R d=>True).
Local Notation N d:=(inner_norm (@euclidean_inner_productP R d)).
Local Notation hFull:=(fun (d:nat) (x:R_n R d) (_:True)=>norm_full_domain_interior (N d) x).
Local Notation AB:=(@euclidean_cartesian_set R n n (Full n) (Full n)).
Local Notation hAB:=(@current_cartesian_domain_open R n n (Full n) (Full n) (hFull n) (hFull n)).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation End:=(@current_translation_parameter_end R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).
Local Notation hSource:=(@current_homotopy_source_open R (n+n)%N n
  (fun _=>True) (Full (n+n)%N) (Full n) q End H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R (n+n)%N n
  (fun _=>True) (Full (n+n)%N) (Full n) q End H hH.1).
Local Notation TargetTest:=(@current_test_space R h2 n (Full n) (hFull n) (1+m)%N).
Local Notation hTargetSpace:=(@current_smooth_space_laws R h2 n (Full n) hTarget (1+m)%N).
Local Notation Inc:=(smooth_test_inclusion hTargetSpace).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Local Notation action:=(@current_value R h2 n (Full n) (hFull n) m).
Local Notation nextAction:=(@current_value R h2 n (Full n) (hFull n) (1+m)%N).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation hS:=(@CurrentKernelAverage.laws R h2 n phi family hPhi hFamily epsilon hEpsilon).
Variable T:@current_space R h2 n (Full n) (hFull n) m.

(** Source for [current_smoothing_deformation_exists]:
    an actual continuous current satisfies every
    compact-test instance of the original defining
    integral, Federer 4.1.18, p. 374. No
    compactness, representation, finite mass or
    kernel symmetry premise is added. *)
Theorem current_smoothing_deformation_exists:
  exists Q:@current_space R h2 n (Full n) (hFull n) (1+m)%N,
    @is_current_smoothing_deformation R h2 n m family epsilon T Q.
Proof.
exists (@current_kernel_smoothing_chain_witness R h2 n m phi family hPhi hFamily
  epsilon hEpsilon T)=>omega.
pose omegaRaw:=@current_test_equal_domain R h2 n (1+m)%N
  (Full n) (Full n) (hFull n) hTarget (erefl _) omega.
have [K hK]:=smooth_test_support_bound hTargetSpace omegaRaw.
have [Q [W [hW [hStrip hQ]]]]:=@current_kernel_transgression_compact_tests R h2 n m epsilon K.
pose beta:=Q (Inc omegaRaw).
pose theta:=@current_kernel_parameter_test R h2 n m beta.
pose Reverse:=@current_cartesian_swap_tests R h2 n n (m+0)%N
  (Full n) (Full n) (hFull n) (hFull n)
  (@current_test_degree_transport R h2 (n+n)%N AB hAB m (m+0)%N
    (esym (addnC m 0%N)) theta).
pose betaZ z:=@CartesianSliceTest.value R h2 n n (Full n) (Full n)
  (hFull n) (hFull n) m 0%N z Logic.I unit Reverse.
have hFibre z:NX z<=epsilon ->
    action T (betaZ z)=nextAction (@current_translation_chain R h2 n m z T) omega.
  move=>hz.
  pose Hz:=@current_translation_homotopy R n z.
  pose hHz:=@current_translation_homotopy_laws R n z.
  pose tau:=@euclidean_translation R n z.
  pose hSourceZ:=@current_homotopy_source_open R n n (fun _=>True)
    (Full n) (Full n) (fun x:X=>x) tau Hz hHz.1.
  pose hTargetZ:=@current_homotopy_target_open R n n (fun _=>True)
    (Full n) (Full n) (fun x:X=>x) tau Hz hHz.1.
  pose omegaZ:=@current_test_equal_domain R h2 n (1+m)%N
    (Full n) (Full n) (hFull n) hTargetZ (erefl _) omega.
  pose IncZ:=smooth_test_inclusion (@current_smooth_space_laws R h2 n (Full n) hTargetZ (1+m)%N).
  pose Kz:=@CurrentHomotopyTransgression.value R h2 n n m
    (fun _=>True) (Full n) (Full n) (fun x:X=>x) tau Hz hHz.
  have hTargetMatch y:
      @current_smooth_value R h2 n (Full n) hTarget (1+m)%N (Inc omegaRaw) y=
      @current_smooth_value R h2 n (Full n) hTargetZ (1+m)%N (IncZ omegaZ) y.
    change (@current_test_value R h2 n (Full n) hTarget (1+m)%N omegaRaw y=
      @current_test_value R h2 n (Full n) hTargetZ (1+m)%N omegaZ y).
    by rewrite /omegaRaw /omegaZ !current_test_equal_domain_values.
  have hValues x:@current_test_value R h2 n (Full n) (hFull n) m (betaZ z) x=
      @current_smooth_value R h2 n (Full n) hSourceZ m (Kz (IncZ omegaZ)) x.
    apply:pairing_ext=>eta.
    rewrite (@current_cartesian_zero_swap_slice_pairing R h2 n m theta z x eta)
      /theta current_kernel_parameter_test_values.
    have hJoined:[set a:Z|NX (@euclidean_first_block_map R n n a)<=epsilon]
        (euclidean_block_join (z,x)).
      change (NX ((@euclidean_block_split R n n (euclidean_block_join (z,x))).1)<=epsilon).
      by rewrite euclidean_block_joinK.
    rewrite (@hQ (Inc omegaRaw) hK (euclidean_block_join (z,x)) (hStrip _ hJoined)).
    exact:(@current_translation_transgression_fibre R h2 n m z
      (Inc omegaRaw) (IncZ omegaZ) hTargetMatch x eta).
  apply:esym.
  exact:(@current_translation_chain_test_action R h2 n m z T omega (betaZ z)
    (Full n) (@openT (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))) (fun _ _=>Logic.I)
    (fun x _=>hValues x)).
have hAverage:=@current_kernel_average_cartesian_integral R h2 n m w S hS T theta.
have hFunction:(fun z=>w z*action T (betaZ z))=
    (fun z=>w z*nextAction (@current_translation_chain R h2 n m z T) omega).
  apply:funext=>z;case:(leP (NX z) epsilon)=>[hz|hz].
  - by rewrite (hFibre z hz).
  - have hZero:family epsilon (-z)=0:=@smoothing_reflected_weight_off R n phi family
      hPhi hFamily epsilon hEpsilon z hz.
    by rewrite hZero !mul0r.
have hWitness:=@current_kernel_smoothing_witness_action R h2 n m phi family hPhi hFamily
  epsilon hEpsilon T omega beta W hW hStrip (@hQ (Inc omegaRaw) hK).
change (is_measure_integral (@euclidean_lebesgue_measure R n)
  (real_total_integrand (fun z=>w z*action T (betaZ z)))
  (@current_value R h2 (n+n)%N AB hAB m
    (@CartesianCurrentProduct.value R h2 n n 0%N m
      (Full n) (Full n) (hFull n) (hFull n) S T) theta)%:E) in hAverage.
by rewrite hFunction -hWitness in hAverage.
Qed.
End CurrentSmoothingDeformationExistence.
