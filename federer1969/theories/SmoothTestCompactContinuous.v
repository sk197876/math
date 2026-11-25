(** Federer (1969), 4.1.5, p. 349: every original
    test belongs to the compact continuous extension
    domain D. The existing compact smooth zero-extension
    theorem proves whole-source continuity; the original
    compact test bound controls the whole norm support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity NormClassZeroTopology
  CompactSupportFunctionUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothCompactZeroExtension
  SmoothTestSpaces SmoothTestEvaluation CompactContinuousVectorFields CompactContinuousDomainFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_test_compact_continuous_field]:
    inclusion of the actual D(U,Y) in the compact
    continuous vector space D to which S is extended
    in Federer 4.1.5, p. 349. No extra boundary
    regularity of the open U is required. *)
Theorem smooth_test_compact_continuous_field (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev) (phi:smooth_test_space hE):
  @compact_continuous_domain_fields R (real_norm_metric_space hNX) U Y NY hNY
    (smooth_test_value hE phi).
Proof.
pose value:=smooth_test_value hE phi.
have[K hK]:=smooth_test_support_bound hE phi.
have hOff:forall x,~smooth_compact_carrier K x ->value x=0.
  exact:((@smooth_function_compact_support_iff R X Y NX NY hNX hNY U E ev hE K
    (smooth_test_inclusion hE phi)).1 hK).
have hGlobal:=@smooth_compact_zero_extension_regular R X Y NX NY hNX hNY U E ev hE
  K (smooth_test_inclusion hE phi) hK.
have hNormSupport:@real_function_support R (real_norm_metric_space hNX) (fun x=>NY (value x)) `<=`
    smooth_compact_carrier K.
  apply:(@real_function_support_in_closed_set R (real_norm_metric_space hNX) (fun x=>NY (value x))
    (smooth_compact_carrier K)
    (compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact K)))=>x hx.
  by rewrite (hOff x hx) (real_seminorm_zero hNY.1).
split.
- split.
  + move=>x; exact:(@norm_class_zero_continuous_at R X Y NX NY hNX hNY setT value x
      (norm_class_continuous (hGlobal 0%N)) Logic.I).
  + exact:(@subclosed_compact (real_norm_metric_space hNX) _ _
      (@real_function_support_closed R (real_norm_metric_space hNX) _) (smooth_compact_is_compact K) hNormSupport).
- move=>x hx; exact:smooth_compact_in_domain K x (hNormSupport x hx).
Qed.
