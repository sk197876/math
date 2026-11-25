(** Federer (1969), 4.1.2, pp. 346–347:
    every nonzero rescaled kernel value lies in
    the original open epsilon ball. This follows
    from the already proved strict support bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CompactSupportFunctionUP SmoothingKernelUP SmoothingDilationUP SmoothingDilationSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_dilation_nonzero_radius]: the strict
    support inclusion in the first display of
    Federer 4.1.2, pp. 346–347, applied
    to each actual nonzero kernel value. *)
Theorem smoothing_dilation_nonzero_radius (R:realType) n
    (phi:R_n R n->R) (family:R->R_n R n->R):
  is_smoothing_kernel phi ->is_smoothing_dilation phi family ->
  forall e:R,0<e ->forall z,family e z!=0 ->
    inner_norm (@euclidean_inner_productP R n) z<e.
Proof.
move=>hPhi hFamily e he z hz.
have hSupport:@real_function_support R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) (family e) z.
  apply:subset_closure; exact/eqP.
exact:(@smoothing_dilation_support_radius R n phi hPhi family hFamily e he z hSupport).
Qed.

(** Source for [smoothing_dilation_zero_beyond_radius]: the original
    rescaled kernel vanishes beyond its radius,
    Federer 4.1.2, pp. 346–347. *)
Theorem smoothing_dilation_zero_beyond_radius (R:realType) n
    (phi:R_n R n->R) (family:R->R_n R n->R):
  is_smoothing_kernel phi ->is_smoothing_dilation phi family ->
  forall e:R,0<e ->forall z,e<inner_norm (@euclidean_inner_productP R n) z ->family e z=0.
Proof.
move=>hPhi hFamily e he z hz.
apply/eqP; apply/negPn/negP=>hNonzero.
have hSmall:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily e he z hNonzero.
by have:=lt_trans hSmall hz; rewrite ltxx.
Qed.
