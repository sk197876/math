(** Federer (1969), 3.2.29, pp. 267–268: countable
    (H^m,m) rectifiability is equivalent to an almost cover
    by countably many class-one m-dimensional submanifolds. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableManifoldCoverUP RectifiableClassOneManifoldCover
  ManifoldCoverMeasureRectifiable HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_29]: the whole numbered theorem
    in Federer 3.2.29, p. 267, proved on p. 268.
    The manifold family is specified by independent countability,
    class and almost-cover laws. Both implications are proved for
    all natural dimensions and arbitrary W, without measurability
    or finite-mass premises. The proof uses only containment in
    the printed error-image display; see the supporting remainder
    lemma for that local set-theoretic correction. *)
Theorem federer_3_2_29 (R:realType) n m (W:set (R_n R n)):
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W <->
  has_countable_submanifold_measure_cover m 1 W.
Proof.
split; first exact:rectifiable_class_one_manifold_cover.
exact:manifold_cover_measure_rectifiable (leqnn 1).
Qed.
