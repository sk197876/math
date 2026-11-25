(** Federer (1969), 4.1.7, p. 358: a
    smooth coefficient field has a continuous
    pointwise norm on the original domain.
    Reuse class-zero subspace continuity and
    the earlier norm-continuity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology functions.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity RealMetricBackground NormRegularity
  NormClassZeroTopology SmoothFunctionSpaceUP MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smooth_field_norm_continuity]: the
    original coefficient norm is continuous on U,
    supporting smooth current multiplication and
    normality in Federer 4.1.7, p. 358.
    No global field bound is imposed. *)
Theorem smooth_field_norm_continuity (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev) (f:E):
  continuous (fun x:metric_subset (U:set (real_norm_metric_space hNX))=>
    (NY (ev f (set_val x)):real_line_metric R)).
Proof.
have hClass:=norm_class_continuous (smooth_function_evaluation_smooth hE f 0%N).
have hValue:=@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U (ev f) hClass.
move=>x;exact:continuous_comp (hValue x)
  (@real_norm_metric_norm_continuous R Y NY hNY (ev f (set_val x))).
Qed.
