(** Federer (1969), 4.1.1, p. 345: compact supports of
    the existing Euclidean partition remain compact and subordinate
    after a bounded linear coordinate change. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric CompactSupportFunctionUP FiniteNormEuclideanChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PartitionSupportPullback.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable e:Hom (R_n R n) X.
Variable p:Hom X (R_n R n).
Hypothesis hChart:is_finite_norm_euclidean_chart NX e p.
Local Notation Z := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation XN := (real_norm_metric_space hNX).

(** Source for [smooth_partition_pullback_support_bound]: the
    support of v composed with the inverse coordinate map is
    contained in the forward image of spt v, supporting the
    original-norm partition in Federer 4.1.1, p. 345. *)
Theorem smooth_partition_pullback_support_bound (v:Z->R):
  compact (real_function_support v) ->
  @real_function_support R XN (fun x=>v (p x)) `<=`
    (fun z:Z=>(e z:XN)) @` real_function_support v.
Proof.
move=>hK.
have hImageCompact:compact ((fun z:Z=>(e z:XN)) @` real_function_support v).
  have hCont:continuous (fun z:Z=>(e z:XN)):=
    @finite_norm_chart_forward_continuous R X NX hNX n e p hChart.
  have hWithin:{within real_function_support v,continuous (fun z:Z=>(e z:XN))}.
    exact:continuous_subspaceT hCont.
  exact (@continuous_compact [the topologicalType of Z] [the topologicalType of XN]
    (fun z:Z=>(e z:XN)) (real_function_support v) hWithin hK).
have hImageClosed:=compact_closed (@metric_hausdorff R XN) hImageCompact.
apply:(@real_function_support_in_closed_set R XN (fun x=>v (p x))
  ((fun z:Z=>(e z:XN)) @` real_function_support v) hImageClosed)=>x hx.
apply:(@real_function_zero_off_support R Z v (p x))=>hpx.
apply:hx; exists (p x)=>//; exact:finite_norm_chart_right_inverse hChart x.
Qed.

(** Source for [smooth_partition_pullback_support_compact]: the
    actual pulled-back support is compact, supporting the compact
    partition functions used in Federer 4.1.1, p. 345. *)
Theorem smooth_partition_pullback_support_compact (v:Z->R):
  compact (real_function_support v) ->
  compact (@real_function_support R XN (fun x=>v (p x))).
Proof.
move=>hK.
have hImage:compact ((fun z:Z=>(e z:XN)) @` real_function_support v).
  have hCont:continuous (fun z:Z=>(e z:XN)):=
    @finite_norm_chart_forward_continuous R X NX hNX n e p hChart.
  have hWithin:{within real_function_support v,continuous (fun z:Z=>(e z:XN))}.
    exact:continuous_subspaceT hCont.
  exact (@continuous_compact [the topologicalType of Z] [the topologicalType of XN]
    (fun z:Z=>(e z:XN)) (real_function_support v) hWithin hK).
apply:(subclosed_compact (@real_function_support_closed R XN (fun x=>v (p x))) hImage).
exact:smooth_partition_pullback_support_bound hK.
Qed.
End PartitionSupportPullback.
