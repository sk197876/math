(** Federer (1969), 3.2.14, p. 252: translating
    one bounded Euclidean parameter set permits the
    union of two rectifiable images. The translated
    partial function is specified by its graph law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric PartialFunctionUP
  PartialFunctionPrecomposition PartialMetricLipschitz CoveringFamilyUP
  CoveringFamilyLaws MetricBoundedUnion MetricClosedBalls MetricBoundedClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_partial_euclidean_translation]: the
    source translation supporting the binary union in
    Federer 3.2.14, p. 252. Its inverse is subtraction
    of the translation vector on the actual graph. *)
Definition is_partial_euclidean_translation (R : realType) m
    (X : metricType R)
    (f g : partial_function (inner_metric_space (@euclidean_inner_productP R m)) X)
    (v : R_n R m) : Prop :=
  forall x y, partial_function_graph g x y <-> partial_function_graph f (x-v) y.

(** Source for [partial_euclidean_translation_exists]:
    existence of the source translation used for the
    union observation, Federer 3.2.14, p. 252. *)
Lemma partial_euclidean_translation_exists (R : realType) m
    (X : metricType R)
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R m)) X)
    (v : R_n R m) :
  exists g, is_partial_euclidean_translation f g v.
Proof. exists (partial_function_precompose (fun x => x-v) f); by move=> x y. Qed.

(** Source for [euclidean_translation_metric]: translation
    leaves parameter distances unchanged in the proof
    of Federer 3.2.14, p. 252, by the metric of 1.7.1. *)
Lemma euclidean_translation_metric (R : realType) m
    (v x y : inner_metric_space (@euclidean_inner_productP R m)) :
  mdist (x-v) (y-v)=mdist x y.
Proof. by rewrite !inner_metric_distanceE opprD addrA addrAC addrK. Qed.

(** Source for [partial_euclidean_translation_range]:
    a source translation keeps the exact parametrized
    image, supporting Federer 3.2.14, p. 252. *)
Lemma partial_euclidean_translation_range (R : realType) m
    (X : metricType R)
    (f g : partial_function (inner_metric_space (@euclidean_inner_productP R m)) X)
    (v : R_n R m) :
  is_partial_euclidean_translation f g v ->
  partial_function_range g=partial_function_range f.
Proof.
move=> hg; apply/seteqP; split=> y [x hx].
- exists (x-v); exact: (hg x y).1 hx.
- exists (x+v); apply: (hg (x+v) y).2; by rewrite addrK.
Qed.

(** Source for [partial_euclidean_translation_lipschitz]:
    source translation keeps the Lipschitz bound for
    the union in Federer 3.2.14, p. 252. *)
Lemma partial_euclidean_translation_lipschitz (R : realType) m
    (X : metricType R)
    (f g : partial_function (inner_metric_space (@euclidean_inner_productP R m)) X)
    (v : R_n R m) (L : R) :
  is_partial_euclidean_translation f g v ->
  is_partial_metric_lipschitz_bound f L -> is_partial_metric_lipschitz_bound g L.
Proof.
move=> hg hf; split; first exact: hf.1.
move=> x y a b ha hb.
have hh := hf.2 (x-v) (y-v) a b ((hg x a).1 ha) ((hg y b).1 hb).
by rewrite euclidean_translation_metric in hh.
Qed.

(** Source for [partial_euclidean_translation_bounded]:
    boundedness of the shifted parameter set for
    Federer 3.2.14, p. 252. The target may be empty. *)
Lemma partial_euclidean_translation_bounded (R : realType) m
    (X : metricType R)
    (f g : partial_function (inner_metric_space (@euclidean_inner_productP R m)) X)
    (v : R_n R m) :
  is_partial_euclidean_translation f g v ->
  metric_set_bounded (partial_function_domain f) -> metric_set_bounded (partial_function_domain g).
Proof.
move=> hg hb.
have [r [hr hbound]] := metric_bounded_distance_bound
  (0 : inner_metric_space (@euclidean_inner_productP R m)) hb.
have hsub : partial_function_domain g `<=`
    metric_closed_ball (v : inner_metric_space (@euclidean_inner_productP R m)) r.
  move=> x [y hy].
  have hd : partial_function_domain f (x-v) by exists y; exact: (hg x y).1 hy.
  have hh := hbound (x-v) hd.
  change (is_true (inner_norm (@euclidean_inner_productP R m) (0-(x-v))<=r)) in hh.
  change (is_true (inner_norm (@euclidean_inner_productP R m) (v-x)<=r)).
  rewrite -[v-x]opprB inner_normN.
  by move: hh; rewrite sub0r inner_normN.
exact: (metric_bounded_subset hsub (@covering_closed_ball_bounded R
  (inner_metric_space (@euclidean_inner_productP R m)) v r hr)).
Qed.
