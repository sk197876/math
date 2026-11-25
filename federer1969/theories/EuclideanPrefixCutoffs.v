(** Federer (1969), 3.1.4, pp. 214–215: the C cutoffs
    in a fixed ambient dimension, with arbitrary admissible prefix length.
    The variation threshold is corrected by erratum p. 4, book p. 214
    line 24, to at least 1/j. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanPrefixTranslation EuclideanSliceTranslation
  EuclideanSliceVariationSets EuclideanSliceUniformCutoffs EuclideanSmallMassCutoffs
  RealMetricBackground PartialFunctionBasic MeasureUP MeasurableFunctionUP ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section PrefixCutoffs.
Variable R : realType.
Variables m k : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Z := (inner_metric_space (@euclidean_inner_productP R k)).
Variable B : set X.
Variable g : X -> R^o.
Variables e c : R.

(** Source for [prefix_slice_variation_exception]: Z before its
    radius restriction, Federer 3.1.4, p. 214; corrected weak
    derivative threshold in erratum p. 4, book p. 214 line 24. *)
Definition prefix_slice_variation_exception : set (X*Z) :=
  [set az | ~B (@euclidean_prefix_translation R m k az.1 az.2) \/
    e<=`|g (@euclidean_prefix_translation R m k az.1 az.2)-g az.1|].

(** Source for [prefix_slice_uniform_cutoff]: C(i,j,p,q)
    in Federer 3.1.4, p. 214, with B fixed and k=i-1.
    Positive radius indices are represented by successors. *)
Definition prefix_slice_uniform_cutoff q : set X :=
  B `&` euclidean_small_mass_cutoff prefix_slice_variation_exception c q.

(** Source for [prefix_slice_uniform_cutoff_increasing]:
    monotonicity of C in q, Federer 3.1.4, p. 215. *)
Lemma prefix_slice_uniform_cutoff_increasing q r :
  (q<=r)%N -> prefix_slice_uniform_cutoff q `<=` prefix_slice_uniform_cutoff r.
Proof.
move=> hqr a [hBa hsmall]; split=> //.
exact: (@euclidean_small_mass_cutoff_increasing R m k
  prefix_slice_variation_exception c q r hqr a hsmall).
Qed.
End PrefixCutoffs.

(** Source for [prefix_slice_variation_blocks]: the same Z
    in the block coordinates used for the Fubini argument,
    Federer 3.1.4, pp. 214–215. *)
Lemma prefix_slice_variation_blocks (R : realType) k l
    (B : set (inner_metric_space (@euclidean_inner_productP R (k+l))))
    (g : inner_metric_space (@euclidean_inner_productP R (k+l)) -> R^o) e :
  @prefix_slice_variation_exception R (k+l) k B g e=
    @euclidean_slice_variation_exception R k l B g e.
Proof.
have he : @euclidean_prefix_translation R (k+l) k=
    @euclidean_slice_translation R k l.
  apply: funext=> a; apply: funext=> z; exact: euclidean_prefix_translation_blocks.
by rewrite /prefix_slice_variation_exception /euclidean_slice_variation_exception he.
Qed.

(** Source for [prefix_slice_uniform_cutoff_blocks]: the
    fixed-dimension presentation of C equals its block presentation,
    supporting Federer 3.1.4, p. 215. *)
Lemma prefix_slice_uniform_cutoff_blocks (R : realType) k l
    (B : set (inner_metric_space (@euclidean_inner_productP R (k+l))))
    (g : inner_metric_space (@euclidean_inner_productP R (k+l)) -> R^o) e c :
  @prefix_slice_uniform_cutoff R (k+l) k B g e c=
    @euclidean_slice_uniform_cutoff R k l B g e c.
Proof.
apply: funext=> q.
by rewrite /prefix_slice_uniform_cutoff /euclidean_slice_uniform_cutoff
  prefix_slice_variation_blocks.
Qed.

(** Source for [prefix_slice_uniform_cutoff_measurable]:
    measurability of C for every coordinate i in the same R^m,
    Federer 3.1.4, p. 215. *)
Lemma prefix_slice_uniform_cutoff_measurable (R : realType) m k
    (B : set (inner_metric_space (@euclidean_inner_productP R m)))
    (g : inner_metric_space (@euclidean_inner_productP R m) -> R^o) e c q :
  (k<=m)%N -> measure_measurable (@euclidean_lebesgue_measure R m) B ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total g) ->
  measure_measurable (@euclidean_lebesgue_measure R m)
    (@prefix_slice_uniform_cutoff R m k B g e c q).
Proof.
move=> hk hB hg.
have hn : m=(k+(m-k))%N by rewrite addnC subnK.
move: B g hB hg; rewrite hn=> B g hB hg.
rewrite prefix_slice_uniform_cutoff_blocks.
exact: euclidean_slice_uniform_cutoff_measurable hB hg.
Qed.

(** Source for [prefix_slice_uniform_cutoffs_conull]:
    the C exhaustion of B up to a null set, Federer 3.1.4,
    p. 215, with no extra hypothesis on the translated restrictions. *)
Theorem prefix_slice_uniform_cutoffs_conull (R : realType) m k
    (B : set (inner_metric_space (@euclidean_inner_productP R m)))
    (g : inner_metric_space (@euclidean_inner_productP R m) -> R^o) e c :
  (k<=m)%N -> measure_measurable (@euclidean_lebesgue_measure R m) B ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total g) -> 0<e -> 0<c ->
  euclidean_lebesgue_measure m
    (B `\` \bigcup_q @prefix_slice_uniform_cutoff R m k B g e c q)=0%E.
Proof.
move=> hk hB hg he hc.
have hn : m=(k+(m-k))%N by rewrite addnC subnK.
move: B g hB hg; rewrite hn=> B g hB hg.
rewrite prefix_slice_uniform_cutoff_blocks.
exact: euclidean_slice_uniform_cutoffs_conull hB hg he hc.
Qed.
