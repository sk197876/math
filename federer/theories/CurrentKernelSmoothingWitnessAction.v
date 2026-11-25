(** Federer (1969), 4.1.18, p. 374: compute
    the parameter-product smoothing witness using a
    genuine compact transgression test near the
    entire kernel strip. The input T is arbitrary.
    This is an existence-proof adapter, not a
    consumer definition.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces CurrentEqualDomainTests
  CurrentCartesianDomain CurrentCartesianProductSealed SmoothTestSpaces SmoothTestEvaluation
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTransgressionSealed
  CurrentHomotopyTestReplacementUP CurrentDeformationChainTestAction
  CurrentTranslationParameterHomotopy CurrentKernelParameterInput CurrentKernelParameterTest
  CurrentKernelSmoothingChainWitness CurrentKernelAverageSealed SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentKernelSmoothingWitnessAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
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
Local Notation D:=(@current_test_space R h2 (n+n)%N (Full (n+n)%N) hSource m).
Local Notation TargetTest:=(@current_test_space R h2 n (Full n) (hFull n) (1+m)%N).
Local Notation RawOmega:=(fun omega:TargetTest=>
  @current_test_equal_domain R h2 n (1+m)%N (Full n) (Full n)
    (hFull n) hTarget (erefl _) omega).
Local Notation Inc:=(smooth_test_inclusion
  (@current_smooth_space_laws R h2 n (Full n) hTarget (1+m)%N)).
Local Notation KH:=(@CurrentHomotopyTransgression.value R h2 (n+n)%N n m
  (fun _=>True) (Full (n+n)%N) (Full n) q End H hH).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Variable T:@current_space R h2 n (Full n) (hFull n) m.

(** Source for [current_kernel_smoothing_witness_action]:
    the actual chain witness acts as the original
    compact kernel product on a compact representative
    of K_H omega, Federer 4.1.18, p. 374. *)
Theorem current_kernel_smoothing_witness_action
    (omega:TargetTest) (beta:D) (W:set Z):
  @open (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (n+n)%N))) W ->
  [set a:Z|N n (@euclidean_first_block_map R n n a)<=epsilon] `<=` W ->
  (forall a,W a->@current_test_value R h2 (n+n)%N (Full (n+n)%N) hSource m beta a=
    @current_smooth_value R h2 (n+n)%N (Full (n+n)%N) hSource m
      (KH (Inc (RawOmega omega))) a) ->
  @current_value R h2 n (Full n) (hFull n) (1+m)%N
    (@current_kernel_smoothing_chain_witness R h2 n m phi family hPhi hFamily
      epsilon hEpsilon T) omega=
  @current_value R h2 (n+n)%N AB hAB m
    (@CartesianCurrentProduct.value R h2 n n 0%N m
      (Full n) (Full n) (hFull n) (hFull n) S T)
    (@current_kernel_parameter_test R h2 n m beta).
Proof.
move=>hW hStrip hBeta.
pose Input:=@current_kernel_parameter_input R h2 n m phi family hPhi hFamily epsilon hEpsilon T.
have hReplacement:@is_current_homotopy_test_replacement R h2 (n+n)%N n m m
    (fun _=>True) (Full (n+n)%N) (Full n) q End H hH Input
    (Inc (RawOmega omega)) beta.
  exists W;split;first exact:hW.
  split.
  - move=>a ha;apply:hStrip.
    exact:(@current_kernel_parameter_input_bound R h2 n m phi family hPhi hFamily
      epsilon hEpsilon T a ha).
  split;first by move=>a _.
  exact:hBeta.
rewrite /current_kernel_smoothing_chain_witness current_equal_domain_test_action_reverse.
rewrite (@current_deformation_chain_test_action R h2 (n+n)%N n m
  (fun _=>True) (Full (n+n)%N) (Full n) q End H hH Input
  (@current_kernel_parameter_homotopy_proper R h2 n m phi family hPhi hFamily
    epsilon hEpsilon T) (RawOmega omega) beta hReplacement).
exact:current_kernel_parameter_input_action.
Qed.
End CurrentKernelSmoothingWitnessAction.
