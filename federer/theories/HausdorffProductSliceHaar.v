(** Federer (1969), 2.10.45, pp. 202–203: the cube bound makes the
    translation-invariant slice measure finite on compact subsets of R^m.
    Its Borel regularisation retains the Borel values and translation
    invariance, supplying the hypotheses for 2.7.7. This does not assert
    Borel regularity of the original slice on arbitrary sets. Source
    context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanAdditiveGroup EuclideanCoordinateCubeLaws
  SquaredMetricProductUP SquaredMetricProductLaws MetricProductRectangles
  HausdorffMeasure HausdorffProductSliceMeasure HausdorffProductSliceTranslation
  EuclideanProductCoefficient EuclideanCubeProductUpperBound
  MeasureUP MeasureBasic MeasurePushforward TopologicalBorel BorelRegularMeasureUP
  BorelRegularisation BorelRegularisationBijection TranslationInvariantHaar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_product_slice_compact_finite]: supporting
    local finiteness required by the appeal to 2.7.7
    in 2.10.45, p. 203. A compact set lies
    in a coordinate cube; its upper bound is finite
    because the prescribed H^k(V) is finite. *)
Theorem hausdorff_product_slice_compact_finite (R : realType) m k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  (hausdorff_measure k V< +oo)%E -> forall K,
  compact K -> (hausdorff_product_slice_measure first second V (k+m) K< +oo)%E.
Proof.
move=> hV K hK; have [r [hr hb]] := @euclidean_compact_coordinate_bound R m K hK.
pose origin : R_n R m := [ffun _=> -r].
pose Q : set (inner_metric_space (@euclidean_inner_productP R m)) :=
  [set x | forall i, -r<=x i<= -r+(r+r)].
have ho i : origin i= -r by rewrite /origin ffunE.
have hu : 0<=r+r by lra.
have hQ := @euclidean_coordinate_cube_laws R m origin (-r) (r+r) ho hu.
have hKQ : K `<=` Q.
  move=> x hx i; have hh := hb x hx i; move: hh; rewrite ler_norml=> /andP[hl hu']; apply/andP; split; lra.
have hbound := @hausdorff_euclidean_cube_product_upper_bound R m k P Y pair first second hp
  origin (@coordinate_basis R m) Q (r+r) V hQ hu hV.
have hmono := measure_mono (@hausdorff_product_slice_is_measure R P
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y first second V (k+m)) hKQ.
apply: le_lt_trans hmono _; apply: le_lt_trans hbound _.
have hvfin : hausdorff_measure k V \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative (@hausdorff_measure_is_measure R Y k) V)).
rewrite -(fineK hvfin) -EFinM; exact: ltry.
Qed.

(** Source for [hausdorff_product_slice_regularised_invariant]: supporting
    Borel regular measure used for the uniqueness step in
    2.10.45, p. 203. Regularisation preserves every
    Borel value, finite compact values, and translations;
    it imposes no measurability requirement on V. *)
Theorem hausdorff_product_slice_regularised_invariant (R : realType) m k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  (hausdorff_measure k V< +oo)%E ->
  is_invariant_borel_measure (fun x y : inner_metric_space (@euclidean_inner_productP R m)=>x+y)
    (borel_regularisation (hausdorff_product_slice_measure first second V (k+m))).
Proof.
move=> hV.
pose gamma := hausdorff_product_slice_measure first second V (k+m).
have hm := @hausdorff_product_slice_is_measure R P
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y first second V (k+m).
have hb A (hA : borel_set A) : measure_measurable gamma A.
  exact (@hausdorff_product_slice_borel_measurable R P
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y
    pair first second (squared_metric_product_cartesian hp) V (k+m) A hA).
constructor.
- exact: borel_regularised_measure_is_measure hm.
- exact: borel_regularised_measure_borel_regular hm hb.
- move=> K hK.
  have hKb := closed_borel_set (compact_closed
    (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) hK).
  rewrite (borel_regularised_measure_borel_value hm hKb).
  exact (@hausdorff_product_slice_compact_finite R m k P Y pair first second hp V hV K hK).
- move=> a; apply: funext=> A; rewrite /measure_pushforward.
  have htrans z B : gamma ((fun x=>z+x) @` B)=gamma B.
    exact (@hausdorff_product_slice_translation R m P Y pair first second hp V (k+m) z B).
  have hi B := @borel_regularisation_invariant_bijection R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] gamma
    (fun x=> -a+x) (fun x=>a+x)
    (fun x=>addNKr a x) (fun x=>addKr a x)
    (@euclidean_translation_continuous R m (-a)) (@euclidean_translation_continuous R m a)
    (htrans (-a)) B.
  have he : (fun x=>a+x) @^-1` A=(fun x=> -a+x) @` A.
    apply/seteqP; split=> x.
    + move=> hx; exists (a+x)=> //; by rewrite addKr.
    + move=> [y hy <-]; by rewrite /= addNKr.
  by rewrite he hi.
Qed.
