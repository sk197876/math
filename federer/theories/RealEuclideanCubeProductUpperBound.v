(** Federer (1969), 2.10.45, printed pp. 202–203: gamma(U) <= u^m xi H^k(V)
    for a Euclidean cube U of side u, when H^k(V) is finite. First remove
    the mesh margin at each positive cutoff, then use the abstract cutoff
    supremum. The argument allows zero side length and zero mass in either
    degree. Source context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation ExtendedRealOrderTopology ExtendedRealBounds GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBoxUP SquaredMetricProductUP MetricProductRectangles MetricDiameter
  HausdorffLengthUP HausdorffDiameterCost HausdorffMeasureUP HausdorffMeasure
  MetricScaleEnvelopeUP CaratheodoryLimitUP MeasureUP
  RealEuclideanProductCoefficient RealEuclideanCubeProductCutoffBound PolynomialMarginLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_hausdorff_euclidean_cube_product_upper_bound]: direct
    cube bound asserted before the covering argument in
    2.10.45, p. 202, and proved on p. 203.
    Finiteness of H^k(V) permits the polynomial limit;
    V remains arbitrary, with no measurability hypothesis.
    The coefficient xi is the printed one by
    euclidean_product_coefficient_printed. *)
Theorem real_hausdorff_euclidean_cube_product_upper_bound (R : realType) (m : nat) (k : R) (hk : (0<=k)%R) (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second)
    origin axis Q (u : R) (V : set Y) :
  @is_euclidean_rectangular_box R m origin axis (fun _=>u) Q ->
  0<=u -> (real_hausdorff_measure hk V< +oo)%E ->
    (real_hausdorff_measure (addr_ge0 hk (ler0n R m)) (metric_product_rectangle first second Q V)<=
      (real_euclidean_product_upper_coefficient m hk*u^+m)%:E*
        real_hausdorff_measure hk V)%E.
Proof.
move=> hQ hu hV.
have hv0 := measure_nonnegative (@real_hausdorff_measure_is_measure R Y k hk) V.
have hvfin : real_hausdorff_measure hk V \is a fin_num by rewrite (ge0_fin_numE hv0).
pose v := fine (real_hausdorff_measure hk V).
have hve : real_hausdorff_measure hk V=v%:E := esym (fineK hvfin).
have hv : 0<=v by move: hv0; rewrite hve lee_fin.
pose C := real_euclidean_product_upper_coefficient m hk.
have hC : 0<C := real_euclidean_product_upper_coefficient_positive m hk.
have hK : 0<=C*v := mulr_ge0 (ltW hC) hv.
apply: (caratheodory_limit_least (@real_hausdorff_measure_specification R P (k+m%:R)%R (addr_ge0 hk (ler0n R m))))=> Delta nu hDelta hn.
have [q [hq hqd]] := @extended_rationals_order_dense R 0%E Delta hDelta.
have hq0 : (0<ratr q :>R) by move: hq; rewrite lte_fin.
pose s := (Num.sqrt m.+1%:R : R).
have hs : 0<s by rewrite /s sqrtr_gt0 ltr0n.
pose cap := ratr q/s.
have hcap : 0<cap := divr_gt0 hq0 hs.
have hb : (nu (metric_product_rectangle first second Q V)<=((C*v)*u^+m)%:E)%E.
  apply: (@nonnegative_polynomial_margin_limit R m u cap (C*v) _ hu hcap hK)=> delta hd hdcap.
  have hpdelta : ((s*delta)%:E<=Delta)%E.
    apply: le_trans _ (ltW hqd); rewrite lee_fin.
    have hh : s*delta<ratr q.
      by move: hdcap; rewrite /cap ltr_pdivlMr // mulrC.
    exact: ltW hh.
  have hh := @real_euclidean_cube_product_cutoff_margin_bound R m k hk P Y pair first second hp
    origin axis Q u delta V Delta nu hQ hu hd hpdelta hn.
  rewrite hve -EFinM in hh.
  have he : C*(u+delta)^+m*v=C*v*(u+delta)^+m by ring.
  by rewrite -/C he in hh.
rewrite hve -EFinM.
have he : C*u^+m*v=C*v*u^+m by ring.
by rewrite -/C he.
Qed.
