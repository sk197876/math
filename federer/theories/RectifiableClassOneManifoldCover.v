(** Federer (1969), 3.2.29, pp. 267–268: extend each
    original partial Lipschitz parametrization, obtain countable
    class-one manifold images, and retain the given null remainder. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableManifoldCoverUP LipschitzImageManifoldCover
  ZeroRectifiableManifoldCover SubmanifoldCoverClosure EuclideanPartialLipschitzExtension
  MeasureAlmostUP PartialMetricLipschitz PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [positive_rectifiable_class_one_manifold_cover]:
    supporting passage from a bounded Lipschitz parametrization to
    the global Lipschitz map used in Federer 3.2.29, p. 268.
    The opaque same-bound extension agrees on the actual partial
    domain. The larger global image is used only as an almost cover. *)
Lemma positive_rectifiable_class_one_manifold_cover (R:realType) n m (E:set (R_n R n)):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m.+1 E ->
  has_countable_submanifold_measure_cover m.+1 1 E.
Proof.
move=>[f [_ [[L hL] hRange]]].
have [F [hF hGraph]]:=euclidean_partial_lipschitz_global_extension hL.
apply:(@submanifold_cover_subset R n m.+1 1 E (F @` setT) _ (lipschitz_image_countable_manifold_cover hF)).
move=>y hy.
have [x hx]:partial_function_range f y by rewrite hRange.
exists x; first exact I.
rewrite hGraph in hx; exact hx.2.
Qed.

(** Source for [countably_rectifiable_class_one_manifold_cover]:
    the countable exact-carrier reduction in Federer 3.2.29,
    pp. 267–268. Unite the local manifold families of all
    rectifiable pieces; use zero-dimensional singleton manifolds
    separately, as required by the finite-set convention. *)
Theorem countably_rectifiable_class_one_manifold_cover (R:realType) n m (S:set (R_n R n)):
  @is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m S ->
  has_countable_submanifold_measure_cover m 1 S.
Proof.
case:m=>[|m] hS.
- apply:zero_rectifiable_manifold_cover.
  split; first exact:hausdorff_measure_is_measure.
  exists S; split; first exact hS.
  rewrite /measure_almost_included setDv; exact:measure_empty (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0).
- have [C [hC [hRect hUnion]]]:=hS.
  rewrite hUnion.
  apply:(@submanifold_cover_countable_union R n m.+1 1 [the choiceType of set (R_n R n)] C id hC).
  move=>E hE; exact:positive_rectifiable_class_one_manifold_cover (hRect E hE).
Qed.

(** Source for [rectifiable_class_one_manifold_cover]: the forward
    implication of Federer 3.2.29, p. 267. An arbitrary W
    with a countably rectifiable almost carrier is covered by
    countably many actual class-one m-submanifolds almost everywhere.
    No W measurability, finite mass or dimension bound is added. *)
Theorem rectifiable_class_one_manifold_cover (R:realType) n m (W:set (R_n R n)):
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  has_countable_submanifold_measure_cover m 1 W.
Proof.
move=>[_ [S [hS hWS]]].
exact (submanifold_cover_almost_transfer hWS (countably_rectifiable_class_one_manifold_cover hS)).
Qed.
