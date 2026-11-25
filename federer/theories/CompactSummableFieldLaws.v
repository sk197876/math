(** Federer (1969), 4.1.18, p. 375: actual compactly
    supported summable fields and their finite L1 size. These
    public laws use the opaque carrier and the original L1
    seminorm. Almost-equal raw fields may be distinct; their
    integral size is therefore a seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric Hom ModuleQuotient
  SubspaceCarrier MeasureUP PartialFunctionBasic MeasurableNormedFunctionUP
  TotalMeasurableFunctionSpace MeasureLpNormTotal ExtendedSeminormUP
  CompactSummableFieldUP CompactSummableFieldSealed
  LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Laws.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation W:=(@CompactSummableField.space R X V N hN mu hm).
Local Notation inc:=(@CompactSummableField.inclusion R X V N hN mu hm).
Local Notation hW:=(@CompactSummableField.laws R X V N hN mu hm).
Local Notation L:=(@total_measurable_lp_norm R X V N hN mu hm 1).

(** Source for [compact_summable_field_value]: the actual
    representative of a member of Omega_m in Federer 4.1.18,
    p. 375. Values are total on the original domain. *)
Definition compact_summable_field_value (f:W):
    X->real_norm_metric_space hN:=subspace_val (inc f).

(** Source for [compact_summable_field_measurable]: every
    field of Omega_m is measurable, as part of summability
    in Federer 4.1.18, p. 375, by 2.4.12, pp. 86–87. *)
Lemma compact_summable_field_measurable (f:W):
  is_measurable_normed_function mu
    (partial_function_total (compact_summable_field_value f)).
Proof. exact:(subspace_valP (inc f)). Qed.

(** Source for [compact_summable_field_finite]: Omega_m
    retains finite original L1 size in Federer 4.1.18, p. 375. *)
Lemma compact_summable_field_finite (f:W):L (inc f)< +oo.
Proof. exact:(subspace_representation_member hW f).1. Qed.

(** Source for [compact_summable_field_compact]: a compact
    carrier for every representative in Omega_m, Federer
    4.1.18, p. 375, without closing it outside U. *)
Lemma compact_summable_field_compact (f:W):
  exists K:set X,compact K /\
    forall x,~K x->compact_summable_field_value f x=0%R.
Proof. exact:(subspace_representation_member hW f).2. Qed.

(** Source for [compact_summable_field_value_add]: pointwise
    addition in the original Omega_m, Federer 4.1.18, p. 375. *)
Lemma compact_summable_field_value_add (f g:W):
  compact_summable_field_value (f+g)%R=
    (fun x=>(compact_summable_field_value f x+
      compact_summable_field_value g x)%R).
Proof. by rewrite /compact_summable_field_value !linearD. Qed.

(** Source for [compact_summable_field_value_scale]: pointwise
    real scalar multiplication in Omega_m, Federer 4.1.18, p. 375. *)
Lemma compact_summable_field_value_scale (c:R) (f:W):
  compact_summable_field_value (c*:f)%R=
    (fun x=>(c*:compact_summable_field_value f x)%R).
Proof. by rewrite /compact_summable_field_value !linearZ. Qed.

(** Source for [compact_summable_field_size]: the finite
    integral size of the actual field, used in J of Federer
    4.1.18, p. 375. It is the earlier L1 value, not a new
    normalization or a positive-definite raw-field norm. *)
Definition compact_summable_field_size (f:W):R:=fine (L (inc f)).

(** Source for [compact_summable_field_size_exact]: exact
    recovery of the original L1 value from its finite real
    value, supporting J in Federer 4.1.18, p. 375. *)
Lemma compact_summable_field_size_exact (f:W):
  (compact_summable_field_size f)%:E=L (inc f).
Proof.
rewrite /compact_summable_field_size fineK //.
have hL:=@total_measurable_lp_norm_seminorm R X V N hN mu hm 1 (lexx 1).
by rewrite (ge0_fin_numE (extended_seminorm_nonnegative hL (inc f)));
  exact:compact_summable_field_finite.
Qed.

(** Source for [compact_summable_field_size_seminorm]: the
    three seminorm laws for each summand in the cost J of
    Federer 4.1.18, p. 375. These are restrictions of 2.4.12,
    p. 86, with the total-domain correction retained. *)
Theorem compact_summable_field_size_seminorm:
  is_real_seminorm compact_summable_field_size.
Proof.
have hL:=@total_measurable_lp_norm_seminorm R X V N hN mu hm 1 (lexx 1).
constructor.
- move=>f;apply:fine_ge0.
  exact:(extended_seminorm_nonnegative hL (inc f)).
- move=>c f.
  have he:L (inc (c*:f)%R)=`|c|%:E*L (inc f).
    rewrite linearZ;exact:(extended_seminorm_scale hL c (inc f)).
  rewrite -!compact_summable_field_size_exact -EFinM in he.
  by injection he.
- move=>f g.
  have he:L (inc (f+g)%R)<=L (inc f)+L (inc g).
    rewrite linearD;exact:(extended_seminorm_triangle hL (inc f) (inc g)).
  by rewrite -!compact_summable_field_size_exact -EFinD lee_fin in he.
Qed.
End Laws.
