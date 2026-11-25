(** Federer (1969), 2.10.45, p. 203, last paragraph: when H^k(V)>0 the Borel
    restriction of gamma is a positive constant multiple of Lebesgue
    measure. The positive unit-cube value follows from the printed lower
    bound; local finiteness follows from the proved cube upper bound. Haar
    uniqueness is the existing theorem 2.7.7, applied to the Borel
    regularisation. Source context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation ExtendedRealOrderTopology EuclideanInnerProduct InnerMetric
  SquaredMetricProductUP SquaredMetricProductLaws HausdorffMeasure
  RealHausdorffProductSliceMeasure RealHausdorffProductSliceHaar RealHausdorffRectangleLowerBound
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanLebesgueRegularity EuclideanLebesgueHaar EuclideanAdditiveGroup
  MeasureUP TopologicalBorel BorelRegularMeasureUP BorelRegularisation
  TranslationInvariantHaar HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_product_slice_borel_multiple]: direct
    positive-mass Borel restriction assertion at the end of
    2.10.45, p. 203. The constant here includes
    the factor H^k(V); division by that finite positive
    value is reserved for the final normalised statement. *)
Theorem real_hausdorff_product_slice_borel_multiple (R : realType) (m : nat) (k : R) (hk : (0<=k)%R) (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  0<real_hausdorff_measure hk V -> real_hausdorff_measure hk V< +oo ->
  exists2 d : R, (0<d)%R & forall U, borel_set U ->
    real_hausdorff_product_slice_measure first second V (addr_ge0 hk (ler0n R m)) U=
      d%:E*euclidean_lebesgue_measure m U.
Proof.
move=> hVp hVf.
pose gamma := real_hausdorff_product_slice_measure first second V (addr_ge0 hk (ler0n R m)).
pose reg := borel_regularisation gamma.
have hm := @real_hausdorff_product_slice_is_measure R P
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y first second V (k+m%:R)%R (addr_ge0 hk (ler0n R m)).
have hr := @real_hausdorff_product_slice_regularised_invariant R m k hk P Y pair first second hp V hVf.
pose C : set (inner_metric_space (@euclidean_inner_productP R m)) :=
  [set x | forall i, (0<=x i<=1)%R].
have [hCc hCv] := @euclidean_unit_closed_cube R m.
have hCb : borel_set C := closed_borel_set (compact_closed
  (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) hCc).
have hCm := @borel_regular_borel_measurable R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  (euclidean_lebesgue_borel_regular R m) C hCb.
have hl := @real_hausdorff_euclidean_rectangle_lower_bound R m P Y pair first second
  (squared_metric_product_cartesian hp) k hk C V hCm.
rewrite /C hCv mul1e in hl.
have hgp : 0<gamma C.
  rewrite ltNge; apply/negP=> hle.
  have hz : gamma C=0.
    by apply/eqP; rewrite eq_le hle (measure_nonnegative hm) /=.
  rewrite -/gamma hz mule0 in hl.
  by move: hVp; rewrite ltNge hl.
have hrp : 0<reg C by rewrite /reg (borel_regularised_measure_borel_value hm hCb).
have [base hbase] := @euclidean_countable_open_base R m.
have [hWo hWc hWT] := @euclidean_ball_cover R m.
have hh := invariant_borel_left_haar (euclidean_additive_lch_group R m)
  hbase hWo hWc hWT hr hCc hrp.
have [d hd he] := @euclidean_haar_measure_multiple R m reg (or_introl hh).
exists d=> // U hU.
have hval := @borel_regularised_measure_borel_value R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] gamma hm U hU.
exact: eq_trans (esym hval) (he U).
Qed.
