(** Federer (1969), 4.1.1, p. 345: a smooth partition
    of unity associated with an open cover, using 3.1.13,
    pp. 224–225. The qualitative laws needed for distributions
    are specified independently of the Euclidean construction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity CompactSupportFunctionUP
  NormLocallyFiniteFamilyUP FiniteFamilySumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_smooth_compact_partition]: independent
    qualitative partition laws supporting the decomposition
    T=sum T restricted by v_s in Federer 4.1.1, p. 345.
    Smoothness, compact support, local finiteness and the sum
    identity are properties to prove of a supplied family. *)
Record is_smooth_compact_partition (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:X->Prop)
    (J:choiceType) (I:J->Prop) (v:J->X->R):Prop:={
  (** Source for [smooth_partition_global_range]: each v_s
      takes values in [0,1], 3.1.13, p. 225, supporting the
      associated partition in Federer 4.1.1, p. 345. *)
  smooth_partition_global_range:forall s,I s -> forall x,0<=v s x<=1;
  (** Source for [smooth_partition_global_class]: each v_s
      extends smoothly to the whole source, 3.1.13, p. 225,
      supporting Federer 4.1.1, p. 345. *)
  smooth_partition_global_class:forall s,I s ->
    norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True) (v s);
  (** Source for [smooth_partition_compact_support]: every
      partition function has compact support, 3.1.13, pp. 224–225,
      supporting the distribution decomposition in 4.1.1, p. 345. *)
  smooth_partition_compact_support:forall s,I s ->
    compact (@real_function_support R (real_norm_metric_space hNX) (v s));
  (** Source for [smooth_partition_support_in_domain]: partition
      supports remain in U, 3.1.13, pp. 224–225, supporting
      Federer 4.1.1, p. 345. *)
  smooth_partition_support_in_domain:forall s,I s ->
    @real_function_support R (real_norm_metric_space hNX) (v s) `<=` U;
  (** Source for [smooth_partition_locally_finite]: a common
      finite set of terms suffices on a neighbourhood of each
      point of U, 3.1.13, p. 225, supporting 4.1.1, p. 345. *)
  smooth_partition_locally_finite:is_norm_locally_finite_function_family NX U I v;
  (** Source for [smooth_partition_sum_one]: the locally finite
      sum equals one on U, 3.1.13, p. 225, supporting the
      distribution decomposition in Federer 4.1.1, p. 345. *)
  smooth_partition_sum_one:is_finite_family_sum_on U I v (fun _=>1)
}.
