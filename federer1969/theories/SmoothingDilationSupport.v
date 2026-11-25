(** Federer (1969), 4.1.2, pp. 346–347:
    the actual dilated support is compact and lies
    inside the open epsilon ball. The proof uses
    compact images and the exact positive-scale formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals classical_sets topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness CompactSupportFunctionUP SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingDilationSupport.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable e:R.
Hypothesis he:0<e.
Local Notation K := (@real_function_support R T phi).
Local Notation C := ((fun x:T=>(e*:x:T)) @` K).

(** Source for [smoothing_dilation_support_image_compact]: the
    scaled original compact support is compact,
    supporting Federer 4.1.2, pp. 346–347. *)
Lemma smoothing_dilation_support_image_compact:compact C.
Proof.
have hCompact:@compact T K:=@smoothing_kernel_support_compact R n phi hPhi.
have hScale:continuous (fun x:T=>(e*:x:T)):=@real_norm_metric_scale_continuous R X N hN e.
apply:continuous_compact hCompact.
exact:continuous_subspaceT hScale.
Qed.

(** Source for [smoothing_dilation_zero_off_image]: the
    rescaled kernel vanishes outside the scaled support,
    supporting Federer 4.1.2, pp. 346–347. *)
Lemma smoothing_dilation_zero_off_image x:~C x ->family e x=0.
Proof.
move=>hx.
have hNo:~K (e^-1*:x).
  move=>hK; apply:hx; exists (e^-1*:x); first exact hK.
  by rewrite scalerA mulfV ?scale1r // gt_eqF.
rewrite (@hFamily e he x) (@real_function_zero_off_support R T phi (e^-1*:x) hNo) mulr0.
reflexivity.
Qed.

(** Source for [smoothing_dilation_support_compact]: every
    actual rescaled kernel has compact support,
    Federer 4.1.2, pp. 346–347. *)
Theorem smoothing_dilation_support_compact:compact (@real_function_support R T (family e)).
Proof.
apply:(@real_function_compact_support_in_closed_set R T (family e) C
  smoothing_dilation_support_image_compact).
- exact:compact_closed (@metric_hausdorff R T) smoothing_dilation_support_image_compact.
- exact:smoothing_dilation_zero_off_image.
Qed.

(** Source for [smoothing_dilation_support_radius]: the
    original strict support bound |x|<epsilon,
    Federer 4.1.2, pp. 346–347. *)
Theorem smoothing_dilation_support_radius:
  @real_function_support R T (family e) `<=` [set x|N x<e].
Proof.
have hSubset:=@real_function_support_in_closed_set R T (family e) C
  (compact_closed (@metric_hausdorff R T) smoothing_dilation_support_image_compact)
  smoothing_dilation_zero_off_image.
move=>x hx; have [z hz <-]:=hSubset x hx.
change (is_true (N (e*:z)<e)).
rewrite (real_seminorm_scale hN.1) (ger0_norm (ltW he)) -{2}(mulr1 e) ltr_pM2l //.
exact:(@smoothing_kernel_support_unit_ball R n phi hPhi z hz).
Qed.
End SmoothingDilationSupport.
