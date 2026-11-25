(** Federer (1969), 4.1.2, p. 347: the
    original compact kernel has a finite absolute bound,
    and its positive-scale bound is M epsilon^-n.
    Compact continuity and the exact dilation formula
    suffice; the kernel need not be symmetric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CompactSupportFunctionUP SmoothingKernelUP SmoothingDilationUP CompactScalarKernelBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingKernelScalarBound.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.

(** Source for [smoothing_kernel_absolute_bound]: the finite
    sup im Phi used in the original smoothing
    error display, Federer 4.1.2, p. 347. *)
Theorem smoothing_kernel_absolute_bound:
  exists M:R,0<M /\ forall z,`|phi z|<=M.
Proof.
have hOff z:1<N z ->phi z=0.
  move=>hz; apply/eqP; apply/negPn/negP=>hNonzero.
  have hSupport:@real_function_support R (real_norm_metric_space hN) phi z.
    apply:subset_closure; exact/eqP.
  have hSmall:=@smoothing_kernel_support_unit_ball R n phi hPhi z hSupport.
  by have:=lt_trans hSmall hz; rewrite ltxx.
exact:(@compact_scalar_kernel_bound_exists R n phi 1
  (norm_class_continuous (@smoothing_kernel_smooth R n phi hPhi 0%N)) hOff).
Qed.

(** Source for [smoothing_dilation_absolute_bound]: the original
    epsilon^-n kernel bound in Federer 4.1.2,
    p. 347, with its exact dilation coefficient. *)
Theorem smoothing_dilation_absolute_bound (family:R->X->R) M:
  is_smoothing_dilation phi family ->
  (forall z,`|phi z|<=M) ->
  forall e:R,0<e ->forall z,`|family e z|<=M/(e^+n).
Proof.
move=>hFamily hBound e he z.
have hCoeff:0<(e^+n)^-1 by rewrite invr_gt0; exact:exprn_gt0.
rewrite (@hFamily e he z) normrM (ger0_norm (ltW hCoeff)) mulrC.
exact:(ler_wpM2r (ltW hCoeff) (hBound (e^-1*:z))).
Qed.
End SmoothingKernelScalarBound.
