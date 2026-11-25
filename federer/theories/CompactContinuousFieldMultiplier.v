(** Federer (1969), 4.1.5, p. 350: multiplying
    the compact continuous vector field by the continuous
    scalar cutoff preserves the original extension domain.
    The whole support remains inside the original support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricJointScale
  CompactSupportFunctionUP CompactContinuousVectorFields CompactContinuousDomainFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_field_multiplier]:
    the original h w and its support in Federer
    4.1.5, p. 350. The scalar multiplier need only
    be continuous because w already has compact support. *)
Theorem compact_continuous_field_multiplier (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (w:X->Y) (f:X->R):
  compact_continuous_domain_fields U hNY w ->
  continuous (f:X->real_line_metric R) ->
  compact_continuous_domain_fields U hNY (fun x=>f x*:w x).
Proof.
move=>hw hf.
have hSupport:@real_function_support R X (fun x=>NY (f x*:w x)) `<=`
    @real_function_support R X (fun x=>NY (w x)).
  apply:(@real_function_support_in_closed_set R X (fun x=>NY (f x*:w x)) _
    (@real_function_support_closed R X (fun x=>NY (w x))))=>x hx.
  rewrite (@compact_continuous_vector_zero_off_norm_support R X Y NY hNY w x hx).
  by rewrite scaler0 (real_seminorm_zero hNY.1).
split.
- split.
  + move=>x; exact:continuous_comp (cvg_pair (hf x) (hw.1.1 x))
      (@real_norm_metric_joint_scale_continuous R Y NY hNY (f x,w x)).
  + exact:(@subclosed_compact X _ _ (@real_function_support_closed R X _) hw.1.2 hSupport).
- move=>x hx; exact:hw.2 x (hSupport x hx).
Qed.
