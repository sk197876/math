(** Federer (1969), 4.1.5, p. 350:
    for the scalar Daniell assertion the compact
    continuous scalar fields are precisely K(U).
    The original support and topology are unchanged
    by the absolute-value norm presentation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealMetricBackground
  ScalarNormExtendedEmbedding CompactSupportFunctionUP CompactContinuousVectorFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_absolute_function_support]: the original
    scalar support equals its norm support in
    the scalar restriction of Federer 4.1.5,
    p. 350. *)
Lemma scalar_absolute_function_support (R:realType) (X:topologicalType) (f:X->R):
  real_function_support (fun x=>`|f x|)=real_function_support f.
Proof.
have hEqual:[set x:X | `|f x|<>0]=[set x:X | f x<>0].
  apply/seteqP; split=>x hNot hZero.
  - by apply:hNot; rewrite hZero normr0.
  - apply:hNot; apply/eqP; by rewrite -normr_eq0 hZero eqxx.
by rewrite /real_function_support hEqual.
Qed.

(** Source for [real_scalar_norm_identity_continuous]: the
    original scalar topology agrees with its
    norm presentation, supporting Federer 4.1.5,
    p. 350. *)
Lemma real_scalar_norm_identity_continuous (R:realType):
  continuous (fun t:real_line_metric R=>(t:real_norm_metric_space (@scalar_absolute_value_norm R))).
Proof.
apply:(@metric_fixed_lipschitz_continuous R (real_line_metric R)
  (real_norm_metric_space (@scalar_absolute_value_norm R))
  (fun t:real_line_metric R=>(t:real_norm_metric_space (@scalar_absolute_value_norm R))) 1 ler01).
by move=>x y; change (is_true (`|x-y|<=1*`|x-y|)); rewrite mul1r.
Qed.

(** Source for [compact_scalar_field_to_function]: every
    scalar compact continuous field is an
    original K(U) function, Federer 4.1.5,
    p. 350. *)
Theorem compact_scalar_field_to_function (R:realType) (X:topologicalType) (f:X->R^o):
  @compact_continuous_vector_fields R X R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R) f ->
  compactly_supported_continuous_functions f.
Proof.
move=>[hContinuous hSupport]; split.
- move=>x; exact:(continuous_comp (hContinuous x) (@scalar_norm_real_identity_continuous R (f x))).
- by rewrite -scalar_absolute_function_support.
Qed.

(** Source for [compact_function_to_scalar_field]: every
    original K(U) function is a compact
    continuous scalar field in the norm
    presentation, Federer 4.1.5, p. 350. *)
Theorem compact_function_to_scalar_field (R:realType) (X:topologicalType) (f:X->R):
  compactly_supported_continuous_functions f ->
  @compact_continuous_vector_fields R X R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R) f.
Proof.
move=>[hContinuous hSupport]; split.
- move=>x; exact:(continuous_comp (hContinuous x) (@real_scalar_norm_identity_continuous R (f x))).
- by rewrite scalar_absolute_function_support.
Qed.
