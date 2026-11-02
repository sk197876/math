(** Federer (1969), 3.1.4, p. 215: the measure estimate
    for bad prefix and scalar increments. A product of containing
    balls gives a convenient bound with the same final constant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume
  EuclideanBallBoxBound MetricClosedBalls TopologicalBorel BorelRegularMeasureUP
  MeasureUP MeasureBasic ProductMeasure ProductSections CountablyMeasurableUP
  ProductExceptionalSectionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_exceptional_section_estimate]: the first
    measure estimate for S_i in Federer 3.1.4, p. 215, on the
    prefix and scalar blocks. The remaining coordinates are included
    afterwards by a containing product. Empty prefix blocks are allowed. *)
Theorem euclidean_exceptional_section_estimate (R : realType) k
    (S : set (inner_metric_space (@euclidean_inner_productP R k)*
      inner_metric_space (@euclidean_inner_productP R 1)))
    (Z : set (inner_metric_space (@euclidean_inner_productP R k))) (c r : R) :
  0<=c -> 0<=r ->
  measure_countably_measurable (product_measure (euclidean_lebesgue_is_measure R k)
    (euclidean_lebesgue_is_measure R 1)) S ->
  measure_measurable (@euclidean_lebesgue_measure R k) Z ->
  S `<=` metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R k)) r `*`
    metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R 1)) r ->
  (euclidean_lebesgue_measure k
    (metric_closed_ball (0%R : inner_metric_space (@euclidean_inner_productP R k)) r `&` Z)
    <=(c*r^+k)%R%:E)%E ->
  (forall x, metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R k)) r x ->
    ~Z x -> (euclidean_lebesgue_measure 1%N (product_vertical_section S x)<=(c*r)%R%:E)%E) ->
  (product_measure (euclidean_lebesgue_is_measure R k) (euclidean_lebesgue_is_measure R 1) S
    <=((2+2^+k)*c*r^+k.+1)%R%:E)%E.
Proof.
move=> hc hr hS hZ hs hz ht.
pose E n := inner_metric_space (@euclidean_inner_productP R n).
pose B n := metric_closed_ball (0 : E n) r.
have hB n : measure_measurable (@euclidean_lebesgue_measure R n) (B n).
  apply: (borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_borel_regular R n)).
  apply: closed_borel_set; exact: metric_closed_ball_closed.
have hcr : (0<=(c*r)%R%:E)%E by rewrite lee_fin mulr_ge0.
have h := @product_exceptional_section_bound R [the choiceType of E k]
  [the choiceType of E 1%N] _ _ (euclidean_lebesgue_is_measure R k)
  (euclidean_lebesgue_is_measure R 1) S (B k) Z (B 1%N) (c*r)%R%:E
  hS (hB k) hZ (hB 1%N) hcr hs ht.
apply: le_trans h _.
have hfirst : (euclidean_lebesgue_measure k (B k `&` Z)*euclidean_lebesgue_measure 1%N (B 1%N)
    <=(c*r^+k)%R%:E*euclidean_lebesgue_measure 1%N (B 1%N))%E.
  apply: lee_wpmul2r.
  - exact (@measure_nonnegative R [the choiceType of E 1%N]
      (@euclidean_lebesgue_measure R 1) (euclidean_lebesgue_is_measure R 1) (B 1%N)).
  exact hz.
apply: le_trans (leeD hfirst (lexx _)) _.
rewrite /B !euclidean_closed_ball_normalized_volume // euclidean_unit_ball_volume1 expr1
  -!EFinM -EFinD lee_fin exprS.
have hv := euclidean_unit_ball_box_bound R k.
have hterm : c*r*(euclidean_unit_ball_volume R k*r^+k)<=c*r*(2^+k*r^+k).
  apply: ler_wpM2l; first by rewrite mulr_ge0.
  apply: ler_wpM2r; first by rewrite exprn_ge0.
  exact hv.
have hid : c*r^+k*(2*r)+c*r*(2^+k*r^+k)=(2+2^+k)*c*(r*r^+k) by ring.
rewrite -hid; exact: lerD (lexx _) hterm.
Qed.
