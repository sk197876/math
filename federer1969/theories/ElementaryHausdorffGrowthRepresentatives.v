(** Federer (1969), 3.4.8(13), pp. 328, 336:
    endpoint representatives. The origin has counting mass one
    at degree zero. A compact neighbourhood in the full
    ambient dimension satisfies the existing isodiametric bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric UniformHausdorffGrowthUP
  MetricDiameter MetricDiameterMaps CoveringFamilyUP CompactMetricBounded CompactSetDistanceProfile
  HausdorffMeasure HausdorffCountingMeasure HausdorffDiameterCost HausdorffCountableNull
  HausdorffPowerCostLaws EuclideanLebesgueDimensions EuclideanHausdorffLebesgue EuclideanIsodiametric
  EuclideanBoundedRectifiability RectifiableSetUP RectifiableFiniteHausdorffMass
  RectifiableElementary MeasureUP MeasureBasic CountingMeasure MetricBoundedClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [singleton_zero_hausdorff_growth]: the point
    representative for dimension zero in 3.4.8(13),
    p. 336. The positive counting atom remains;
    diameter to degree zero is one. *)
Theorem singleton_zero_hausdorff_growth (R:realType) n (a:R_n R n):
  @is_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0) 0 [set a] /\
  @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) 0 [set a] 1.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
split.
- apply:(@rectifiable_hausdorff_measure_rectifiable R 0 n [set a]).
  exact:finite_set1.
- constructor.
  + by rewrite /metric_set_bounded extended_metric_diameter_singleton ltry.
  + exact:ler01.
  + move=>T hT;rewrite expe0 mule1.
    apply:(le_trans (measure_mono (@hausdorff_measure_is_measure R X 0) hT)).
    by rewrite hausdorff_zero_singleton.
Qed.

(** Source for [compact_ambient_hausdorff_growth]: the full-dimensional
    representative in 3.4.8(13), p. 336. The
    existing isodiametric theorem provides the uniform coefficient;
    the compact set need not be convex. *)
Theorem compact_ambient_hausdorff_growth (R:realType) n
    (S:compact_metric_set (inner_metric_space (@euclidean_inner_productP R n))):
  @is_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) n) n (val S) /\
  @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) n (val S)
    (@hausdorff_normalisation R n).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hBound:=compact_metric_diameter_finite S.
split.
- exact:rectifiable_hausdorff_measure_rectifiable (euclidean_bounded_identity_rectifiable hBound).
- constructor;[exact:hBound|exact:ltW (@hausdorff_normalisation_positive R n)|].
  move=>T hT.
  rewrite (euclidean_hausdorff_spherical_lebesgue T).1.
  case:(pselect (T !=set0))=>hNonempty.
  + exact:lebesgue_isodiametric_bound hNonempty.
  + have hEmpty:T=set0 by apply/seteqP;split=>[x hx|x []];exfalso;apply:hNonempty;by exists x.
    rewrite hEmpty (measure_empty (@euclidean_lebesgue_is_measure R n)).
    change ((0: \bar R)<=@hausdorff_diameter_cost R X n set0)%E.
    exact:hausdorff_diameter_cost_nonnegative.
Qed.
