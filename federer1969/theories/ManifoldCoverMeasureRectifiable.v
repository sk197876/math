(** Federer (1969), 3.2.29, p. 267:
    a countable family of m-dimensional class-one
    manifolds covering almost all of W proves
    countable (H^m,m) rectifiability. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableManifoldCoverUP SubmanifoldCountablyRectifiable RectifiableSetUP CountablyRectifiableUnions
  HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [manifold_cover_measure_rectifiable]: the
    reverse implication of Federer 3.2.29, p. 267.
    No finite mass or W measurability is assumed;
    positive classes and all natural dimensions are retained. *)
Theorem manifold_cover_measure_rectifiable (R:realType) n m k (W:set (R_n R n)):
  (1<=k)%N ->has_countable_submanifold_measure_cover m k W ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W.
Proof.
move=>hk [C hC]; split; first exact:hausdorff_measure_is_measure.
exists (\bigcup_(S in C) S); split.
- apply:(@countably_rectifiable_countable_union R
    (inner_metric_space (@euclidean_inner_productP R n)) [the choiceType of set (R_n R n)]
    m C id (submanifold_measure_cover_countable hC)).
  move=>S hS; exact:submanifold_countably_rectifiable hk (submanifold_measure_cover_class hC hS).
- exact:submanifold_measure_cover_almost hC.
Qed.
