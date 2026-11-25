(** Federer (1969), 4.1.1, p. 345: finite pieces of the
    existing smooth partition provide compactly supported smooth
    cutoffs and finite decompositions. The finite sum below is
    used only as a proved cutoff existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityFiniteSum
  CompactSupportFunctionUP SmoothCompactPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PartitionFiniteSum.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable U:X->Prop.
Variable J:choiceType.
Variable I:J->Prop.
Variable v:J->X->R.
Hypothesis hv:is_smooth_compact_partition hNX U I v.
Variable F:{fset J}.
Hypothesis hFI:forall s,s \in F -> I s.
Local Notation XN := (real_norm_metric_space hNX).

(** Source for [smooth_partition_finite_sum]: a finite sum of
    the original v_s, supporting the smooth compact cutoff
    used in the support arguments of Federer 4.1.1, p. 345. *)
Definition smooth_partition_finite_sum (x:X):R:=\sum_(s:F) v (val s) x.

(** Source for [smooth_partition_finite_sum_support_bound]: a
    finite union of original partition supports, supporting
    compactness of the cutoff in Federer 4.1.1, p. 345. *)
Definition smooth_partition_finite_sum_support_bound:set XN:=
  \bigcup_(s in [set` (predT:pred (F:Type))]) @real_function_support R XN (v (val s)).

(** Source for [smooth_partition_finite_sum_regular]: the
    finite sum is globally smooth by the existing finite-class
    sum theorem, supporting Federer 4.1.1, p. 345. *)
Theorem smooth_partition_finite_sum_regular:
  norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True)
    smooth_partition_finite_sum.
Proof.
move=>k.
rewrite /smooth_partition_finite_sum.
have hOpen x (_:True):norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact:ltr01; by move=>y hy.
have hTerms (s:F):norm_class hNX (@scalar_absolute_value_norm R) (fun _=>True)
    (fun x=>v (val s) x) k.
  exact (@smooth_partition_global_class R X NX hNX U J I v hv (val s)
    (@hFI (val s) (valP s)) k).
exact (@norm_class_finite_sum R X R^o NX (fun t=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun _=>True) [the finType of (F:Type)]
  (fun s:F=>v (val s)) k hOpen hTerms).
Qed.

(** Source for [smooth_partition_finite_sum_support_compact]:
    a finite union of compact partition supports is compact,
    supporting the cutoff in Federer 4.1.1, p. 345. *)
Lemma smooth_partition_finite_sum_support_compact:
  compact smooth_partition_finite_sum_support_bound.
Proof.
rewrite /smooth_partition_finite_sum_support_bound bigcup_pred.
apply:bigsetU_compact=>s _.
exact (@smooth_partition_compact_support R X NX hNX U J I v hv (val s)
  (@hFI (val s) (valP s))).
Qed.

(** Source for [smooth_partition_finite_sum_support_in_domain]:
    the finite support bound remains inside U, supporting the
    localized cutoff in Federer 4.1.1, p. 345. *)
Lemma smooth_partition_finite_sum_support_in_domain:
  smooth_partition_finite_sum_support_bound `<=` U.
Proof.
move=>x [s _ hs].
exact (@smooth_partition_support_in_domain R X NX hNX U J I v hv (val s)
  (@hFI (val s) (valP s)) x hs).
Qed.

(** Source for [smooth_partition_finite_sum_support]: the actual
    cutoff support is contained in the finite compact bound,
    supporting Federer 4.1.1, p. 345. *)
Theorem smooth_partition_finite_sum_support:
  @real_function_support R XN smooth_partition_finite_sum `<=`
    smooth_partition_finite_sum_support_bound.
Proof.
have hClosed:=compact_closed (@metric_hausdorff R XN)
  smooth_partition_finite_sum_support_compact.
apply:(@real_function_support_in_closed_set R XN smooth_partition_finite_sum
  smooth_partition_finite_sum_support_bound hClosed)=>x hx.
rewrite /smooth_partition_finite_sum; apply:big1=>s _.
apply:(@real_function_zero_off_support R XN (v (val s)) x)=>hs.
apply:hx; by exists s.
Qed.
End PartitionFiniteSum.
