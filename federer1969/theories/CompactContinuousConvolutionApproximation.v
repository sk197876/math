(** Federer (1969), 4.1.5, pp. 349–350: each
    compact continuous field has actual smoothing tests,
    a common compact support and a uniform limit. This
    adapter retains both the independent approximation
    law and the actual small-scale convolution formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP NormClassOneUP NormClassZeroWhole
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CompactSupportFunctionUP CompactContinuousVectorFields CompactContinuousDomainFields SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP CompactContinuousSmoothingTests CompactUniformApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousConvolutionApproximation.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation value := (smooth_test_value hE).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [compact_continuous_convolution_test_approximation]:
    actual common-support uniform convolutions of an
    arbitrary original compact continuous field, as used
    in both estimates of Federer 4.1.5, p. 350. *)
Theorem compact_continuous_convolution_test_approximation w:
  @compact_continuous_domain_fields R XT U Y NY hNY w ->
  exists P:R->DT,
    @is_compact_uniform_test_approximation R XT U Y NY DT values w P /\
    exists r:R,0<r /\ forall e:R,0<e ->e<r ->
      is_smoothing_convolution hNY (family e) w (value (P e)).
Proof.
move=>hw.
pose K:=@Build_smooth_compact_set R X N hN U
  (@real_function_support R XT (fun x=>NY (w x))) hw.2 hw.1.2.
have hClass:=@norm_continuous_whole_class_zero R X Y N NY hN hNY w hw.1.1.
have hOff:forall x,~smooth_compact_carrier K x ->w x=0.
  move=>x hx; exact:(@compact_continuous_vector_zero_off_norm_support R XT Y NY hNY w x hx).
have[r [hr [C [P [hP hApprox]]]]]:=@compact_continuous_smoothing_tests R n Y NY hNY hY
  U hU E ev hE phi hPhi family hFamily K w hClass hOff.
exists P; split.
- exists (smooth_compact_carrier C); split; first exact:smooth_compact_is_compact C.
  split; first exact:smooth_compact_in_domain C.
  exists r; split=>//; split.
  + move=>e he her.
    exact:((@smooth_function_compact_support_iff R X Y N NY hN hNY U E ev hE C
      (smooth_test_inclusion hE (P e))).1 (hP e he her).2).
  + move=>eta hEta; have[d [hd [_ hBound]]]:=hApprox eta hEta.
    by exists d.
- exists r; split=>// e he her; exact:(hP e he her).1.
Qed.
End CompactContinuousConvolutionApproximation.
