(** Federer (1969), 2.10.45, pp. 202–203: complete the positive-mass
    proportionality assertion on all Lebesgue-measurable subsets of R^m. A
    finite increasing Borel exhaustion and the Borel sandwich extend the
    Haar identity beyond Borel sets and finite measure values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology EuclideanInnerProduct InnerMetric
  SquaredMetricProductUP SquaredMetricProductLaws HausdorffMeasure
  HausdorffProductSliceMeasure HausdorffProductBorelMultiple
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  BorelFiniteIncreasingCover BorelScaledCompletionAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_product_slice_measurable_multiple]: direct
    positive-mass proportionality part of 2.10.45,
    pp. 202–203, for every Lebesgue-measurable U.
    The multiplier still includes H^k(V), to be
    divided out in the final normalised formula.
    Measurability for the slice measure is also proved. *)
Theorem hausdorff_product_slice_measurable_multiple (R : realType) m k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  0<hausdorff_measure k V -> hausdorff_measure k V< +oo ->
  exists2 d : R, (0<d)%R & forall U,
    measure_measurable (@euclidean_lebesgue_measure R m) U ->
    measure_measurable (hausdorff_product_slice_measure first second V (k+m)) U /\
    hausdorff_product_slice_measure first second V (k+m) U=
      d%:E*euclidean_lebesgue_measure m U.
Proof.
move=> hVp hVf.
have [d hd he] := @hausdorff_product_slice_borel_multiple R m k P Y pair first second hp V hVp hVf.
have hm := @hausdorff_product_slice_is_measure R P
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y first second V (k+m).
have hn := euclidean_lebesgue_is_measure R m.
have hr := euclidean_lebesgue_borel_regular R m.
have [hWo hWc hWT] := @euclidean_ball_cover R m.
have hWf n : euclidean_lebesgue_measure m (@euclidean_open_ball_sequence R m n)< +oo.
  have [C hC hWC] := hWc n.
  exact: le_lt_trans (measure_mono hn hWC) (euclidean_compact_finite hC).
have [E [hE [hEf [hEm hcov]]]] := @borel_finite_increasing_cover R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) (@euclidean_open_ball_sequence R m) hn hr hWf.
have hwhole x : exists n, E n x.
  have [n hn'] := hWT x.
  have hx : (\bigcup_n @euclidean_open_ball_sequence R m n) x by exists n.
  have [j _ hj] := hcov x hx; by exists j.
have hb B (hB : borel_set B) : measure_measurable (hausdorff_product_slice_measure first second V (k+m)) B.
  exact (@hausdorff_product_slice_borel_measurable R P
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y
    pair first second (squared_metric_product_cartesian hp) V (k+m) B hB).
exists d=> // U hU.
exact (@borel_scaled_agreement_completed_measure R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
  (hausdorff_product_slice_measure first second V (k+m)) (@euclidean_lebesgue_measure R m)
  hm hn hr d E hd hb he hE hEf hEm hwhole U hU).
Qed.
