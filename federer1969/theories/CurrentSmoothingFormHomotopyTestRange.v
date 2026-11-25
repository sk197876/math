(** Federer (1969), 4.1.18, p. 375: the
    original form homotopy sends actual compact
    tests to actual compact tests. A single
    compact representative on the whole kernel
    strip supplies the witness; no action on a
    noncompact test is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import SmoothFunctionSpaceLaws Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentAmbientCartesianProduct
  CurrentEqualDomainTests CurrentEqualDomainSmooth SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTransgressionSealed
  CurrentTranslationParameterHomotopy CurrentKernelTransgressionCompactTests
  CurrentKernelParameterTest CurrentKernelAverageUP CurrentKernelAverageSealed CurrentKernelAverageBounds
  CurrentCartesianSliceSealed CurrentCompactKernelFormAverageUP
  CurrentCompactKernelFormAverageReplacement CurrentCompactSmoothingFormAverage
  CurrentSmoothingFormHomotopySealed CurrentSmoothingFormParameterLaw
  SmoothCompactSet SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingFormHomotopyTestRange.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation FullZ:=(fun _:Z=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation End:=(@current_translation_parameter_end R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).
Local Notation hSource:=(@current_homotopy_source_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation ToTarget:=(@current_smooth_equal_domain R h2 n (1+m)%N
  Full Full hFull hTarget (erefl _)).
Local Notation ToProduct:=(@current_smooth_equal_domain R h2 (n+n)%N m
  FullZ AB hSource hAB (esym (@current_cartesian_full_domain R n n))).
Local Notation KH:=(@CurrentHomotopyTransgression.value R h2 (n+n)%N n m
  (fun _=>True) FullZ Full q End H hH).
Local Notation Inc:=(fun d=>smooth_test_inclusion (@current_smooth_space_laws R h2 n Full hFull d)).
Local Notation IncRaw:=(smooth_test_inclusion (@current_smooth_space_laws R h2 n Full hTarget (1+m)%N)).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation hS:=(@CurrentKernelAverage.laws R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation Ball:=(@current_kernel_average_index R n epsilon).
Local Notation hOff:=(@current_compact_smoothing_form_average_off R n phi family
  hPhi hFamily epsilon hEpsilon).
Local Notation A:=(@current_compact_smoothing_form_average R h2 n
  phi family hPhi hFamily epsilon hEpsilon m).
Local Notation K:=(@CurrentSmoothingFormHomotopy.value R h2 n m
  phi family hPhi hFamily epsilon hEpsilon).

(** Source for [current_smoothing_form_homotopy_test_range]:
    every original compact input form has a
    genuine compact homotopy form, supporting the
    corresponding test identities of 4.1.18,
    p. 375. No auxiliary choice is caller data. *)
Theorem current_smoothing_form_homotopy_test_range
    (omega:@current_test_space R h2 n Full hFull (1+m)%N):
  exists beta:@current_test_space R h2 n Full hFull m,
    Inc m beta= K (Inc (1+m)%N omega).
Proof.
pose omegaRaw:=@current_test_equal_domain R h2 n (1+m)%N
  Full Full hFull hTarget (erefl _) omega.
have [L hL]:=smooth_test_support_bound
  (@current_smooth_space_laws R h2 n Full hTarget (1+m)%N) omegaRaw.
have [Q [W [hW [hStrip hQ]]]]:=@current_kernel_transgression_compact_tests R h2 n m epsilon L.
pose rawBeta:=Q (IncRaw omegaRaw).
pose theta:=@current_kernel_parameter_test R h2 n m rawBeta.
pose beta:=@CartesianSlice.value R h2 n n 0%N m Full Full hFull hFull S theta.
exists beta.
rewrite (@CurrentSmoothingFormHomotopy.parameter_average R h2 n m
  phi family hPhi hFamily epsilon hEpsilon (Inc (1+m)%N omega)).
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n Full hFull m))=>x _.
apply:esym.
apply:(@current_compact_kernel_form_average_replacement R h2 n n m Full hFull
  w S hS Ball hOff A
  (@current_compact_smoothing_form_average_laws R h2 n phi family hPhi hFamily epsilon hEpsilon m)
  (ToProduct (KH (ToTarget (Inc (1+m)%N omega)))) theta x Logic.I).
move=>z hz.
have hRadius:NX z<=epsilon.
  have hKernel:smooth_compact_carrier Ball z:=hz.
  by rewrite current_kernel_average_index_carrier in hKernel.
have hJoined:[set a:Z|NX (@euclidean_first_block_map R n n a)<=epsilon]
    (euclidean_block_join (z,x)).
  change (NX ((@euclidean_block_split R n n (euclidean_block_join (z,x))).1)<=epsilon).
  by rewrite euclidean_block_joinK.
rewrite /theta current_kernel_parameter_test_values
  (@hQ (IncRaw omegaRaw) hL (euclidean_block_join (z,x)) (hStrip _ hJoined))
  current_smooth_equal_domain_values current_smooth_equal_domain_test_inclusion.
reflexivity.
Qed.
End CurrentSmoothingFormHomotopyTestRange.
