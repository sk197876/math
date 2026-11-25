(** Federer (1969), 3.2.21, p. 257: the image
    lying in the purely unrectifiable target contributes zero
    Hausdorff mass in the equal-dimension case, by 3.2.14,
    p. 252. These support lemmas require no Borel hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic RectifiableSetUP PureUnrectifiableLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  EuclideanLipschitzRectifiableImage HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pure_countably_rectifiable_subset_null]: supporting
    consequence of pure unrectifiability in Federer 3.2.14,
    p. 252, for the equal-dimension case of 3.2.21,
    p. 257. A countable rectifiable cover reduces to the
    defining null-mass condition and countable subadditivity. *)
Lemma pure_countably_rectifiable_subset_null (R : realType) (X : metricType R)
    (mu : set X -> \bar R) m (T S : set X) :
  is_purely_measure_m_unrectifiable mu m T ->
  S `<=` T -> is_countably_m_rectifiable m S -> mu S=0.
Proof.
move=> hPure hST [C [hC [hRect hCover]]].
have [hm hNull] := (@pure_unrectifiable_iff_rectifiable_subsets_null R X mu m T).1 hPure.
rewrite hCover.
apply: (measure_null_countable_union hm hC)=> E hE.
apply: (hNull E _ (hRect E hE))=> x hx.
apply: hST; rewrite hCover; by exists E.
Qed.

(** Source for [pure_unrectifiable_lipschitz_image_null]: the zero
    target area behind the appeal to 3.2.3 in Federer 3.2.21,
    p. 257. Split any Euclidean parameter set into bounded
    pieces as in 3.2.14. The image need not be given measurable,
    bounded or finite-mass in advance. *)
Lemma pure_unrectifiable_lipschitz_image_null (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (A : set (R_n R m)) (T : set (R_n R n)) :
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) setT f ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m T ->
  f @` A `<=` T ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)=0.
Proof.
move=> hLip hPure hSub.
apply: (pure_countably_rectifiable_subset_null hPure hSub).
have [L [hL hBound]] := hLip.
apply: euclidean_lipschitz_image_countably_rectifiable.
exists L; split; first exact hL.
exact: (metric_lipschitz_bound_restrict (fun _ _=>I) hBound).
Qed.
