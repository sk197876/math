(** Federer (1969), 4.1.5, p. 349: every compact
    continuous vector field on the open source admits
    actual common-support uniform test approximations.
    The original convolution theorem supplies existence;
    the approximation laws contain no chosen kernel. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP NormClassOneUP
  NormClassZeroWhole GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CompactSupportFunctionUP CompactContinuousVectorFields SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothingKernelSealed SmoothingDilationSealed
  CompactContinuousSmoothingTests CompactUniformApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousTestApproximation.
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
Local Notation value := (smooth_test_value hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation A := (@is_compact_uniform_test_approximation R XT U Y NY DT values).

(** Source for [compact_continuous_test_approximation_exists]:
    the actual common-support approximation needed for
    the extension of S in Federer 4.1.5, p. 349.
    The opaque normalized kernel proves existence and is
    not part of the independent approximation definition. *)
Theorem compact_continuous_test_approximation_exists
    (K:smooth_compact_set hN U) (w:X->Y):
  norm_class_zero N NY (fun _=>True) w ->
  (forall x,~smooth_compact_carrier K x ->w x=0) ->
  exists P:R->DT,A w P.
Proof.
move=>hContinuous hOff.
pose phi:=@SmoothingKernel.value R n.
pose family:=@SmoothingDilation.value R n phi.
have[r [hr [C [P [hP hApprox]]]]]:=@compact_continuous_smoothing_tests R n Y NY hNY hY
  U hU E ev hE phi (@SmoothingKernel.laws R n) family (@SmoothingDilation.laws R n phi)
  K w hContinuous hOff.
exists P; exists (smooth_compact_carrier C); split; first exact:smooth_compact_is_compact C.
split; first exact:smooth_compact_in_domain C.
exists r; split=>//; split.
- move=>e he her.
  exact:((@smooth_function_compact_support_iff R X Y N NY hN hNY U E ev hE C
    (smooth_test_inclusion hE (P e))).1 (hP e he her).2).
- move=>eta hEta; have[d [hd [_ hBound]]]:=hApprox eta hEta.
  by exists d.
Qed.

(** Source for [compact_continuous_field_test_approximation]:
    all actual compact continuous fields supported in U,
    including empty supports, admit the approximations
    used in Federer 4.1.5, p. 349. *)
Theorem compact_continuous_field_test_approximation (w:X->Y):
  @compact_continuous_vector_fields R XT Y NY hNY w ->
  @real_function_support R XT (fun x=>NY (w x)) `<=` U ->
  exists P:R->DT,A w P.
Proof.
move=>hw hSupport.
pose K:=@Build_smooth_compact_set R X N hN U
  (@real_function_support R XT (fun x=>NY (w x))) hSupport hw.2.
apply:(@compact_continuous_test_approximation_exists K w).
- exact:(@norm_continuous_whole_class_zero R X Y N NY hN hNY w hw.1).
- move=>x hx; exact:(@compact_continuous_vector_zero_off_norm_support R XT Y NY hNY w x hx).
Qed.
End CompactContinuousTestApproximation.
