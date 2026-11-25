(** Federer (1969), 4.1.5, p. 349: D is the space
    of continuous Y-valued functions on the original domain
    with compact support. The norm has the same nonzero
    locus as the vector field, so scalar support results
    express exactly the original compact-support condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricContinuity
  CompactSupportFunctionUP ContinuousVectorFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousVectorFields.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.

(** Source for [compact_continuous_vector_fields]: the original
    compact continuous vector space D used to extend S in
    Federer 4.1.5, p. 349. This specifies the actual functions
    by continuity and compact support before any extension
    functional is constructed. *)
Definition compact_continuous_vector_fields:set (X->Y):=
  [set w|@continuous_normed_functions R X Y NY hNY w /\
    compact (@real_function_support R X (fun x=>NY (w x)))].

(** Source for [compact_vector_norm_support_identity]: the
    support of the norm is exactly the original vector-field
    support, for the compact fields in Federer 4.1.5, p. 349. *)
Lemma compact_vector_norm_support_identity (w:X->Y):
  @real_function_support R X (fun x=>NY (w x))=closure [set x:X|w x<>0].
Proof.
congr closure; apply:funext=>x; apply:propext; split.
- move=>hn hz; apply:hn; by rewrite hz (real_seminorm_zero hNY.1).
- move=>hn hz; exact:hn (hNY.2 _ hz).
Qed.

(** Source for [compact_continuous_vector_fields_original_support]:
    the specified D is exactly the compact-support continuous
    vector space in the prose of Federer 4.1.5, p. 349,
    with no additional source or target condition. *)
Theorem compact_continuous_vector_fields_original_support (w:X->Y):
  compact_continuous_vector_fields w <->
    continuous (w:X->real_norm_metric_space hNY) /\ compact (closure [set x:X|w x<>0]).
Proof.
change ((continuous (w:X->real_norm_metric_space hNY) /\
  compact (@real_function_support R X (fun x=>NY (w x)))) <->
  (continuous (w:X->real_norm_metric_space hNY) /\ compact (closure [set x:X|w x<>0]))).
by rewrite compact_vector_norm_support_identity.
Qed.

(** Source for [compact_continuous_vector_field_norm]: the
    original norm of a compact continuous vector field lies
    in K(U), needed to apply 2.5.12 in Federer 4.1.5, p. 349. *)
Theorem compact_continuous_vector_field_norm w:
  compact_continuous_vector_fields w ->
    @compactly_supported_continuous_functions R X (fun x=>NY (w x)).
Proof.
move=>[hW hCompact]; split; last exact hCompact.
move=>x; exact:continuous_comp (hW x) (@real_norm_metric_norm_continuous R Y NY hNY (w x)).
Qed.

(** Source for [compact_continuous_vector_zero_off_norm_support]:
    outside the original compact norm support the vector
    field vanishes, used for compact convolution extension
    in Federer 4.1.5, pp. 349–350. *)
Lemma compact_continuous_vector_zero_off_norm_support (w:X->Y) x:
  ~@real_function_support R X (fun x=>NY (w x)) x ->w x=0.
Proof.
move=>hx; exact:(hNY.2 (w x) (@real_function_zero_off_support R X (fun x=>NY (w x)) x hx)).
Qed.
End CompactContinuousVectorFields.
