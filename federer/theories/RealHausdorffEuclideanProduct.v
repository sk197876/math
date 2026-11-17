(** Federer (1969), 2.10.45, printed pp. 202–203: for a squared-metric
    product R^m times Z and finite H^k(V), H^(k+m)(U times V) is c L^m(U)
    H^k(V) for every Lebesgue-measurable U. The coefficient lies between
    alpha(k+m)/(alpha(k)alpha(m)) and xi. This file first gives that
    equivalent unnormalised interval form. The natural Euclidean dimension and real section degree may both be zero;
    no measurability of V is assumed. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation ExtendedRealOrderTopology GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric SquaredMetricProductUP SquaredMetricProductLaws
  EuclideanCoordinateCubeLaws EuclideanBallVolume EuclideanLebesgue EuclideanLebesgueHaar
  EuclideanLebesgueDimensions HausdorffMeasure RealHausdorffProductSliceMeasure
  RealHausdorffProductMeasurableMultiple RealHausdorffProductNullFactor RealHausdorffRectangleLowerBound
  RealEuclideanProductCoefficient RealEuclideanProductCoefficientBounds RealEuclideanCubeProductUpperBound
  MeasureUP TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_hausdorff_euclidean_product_coefficient]: direct
    product equality and equivalent coefficient bounds of
    2.10.45, pp. 202–203, for every real k>=0 and natural Euclidean dimension m.
    The zero-mass case uses a proved nonempty coefficient
    interval; the positive case divides the Haar multiplier
    only by the finite positive H^k(V). *)
Theorem real_hausdorff_euclidean_product_coefficient (R : realType) (m : nat) (k : R) (hk : (0<=k)%R) (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  (real_hausdorff_measure hk V< +oo)%E -> exists c : R,
    real_euclidean_product_lower_coefficient m hk<=c /\
    c<=real_euclidean_product_upper_coefficient m hk /\
    forall U, measure_measurable (@euclidean_lebesgue_measure R m) U ->
      real_hausdorff_product_slice_measure first second V (addr_ge0 hk (ler0n R m)) U=
        (c%:E*euclidean_lebesgue_measure m U*real_hausdorff_measure hk V)%E.
Proof.
move=> hVf.
case: (eqVneq (real_hausdorff_measure hk V) 0%E)=> hV0.
  exists (real_euclidean_product_lower_coefficient m hk); split; first exact: lexx.
  split; first exact: real_euclidean_product_coefficient_interval.
  move=> U _; rewrite hV0 mule0.
  exact (@real_hausdorff_product_slice_null_factor R m k hk P Y pair first second hp V hV0 U).
have hVpos : (0<real_hausdorff_measure hk V)%E.
  by rewrite lt_def hV0 (measure_nonnegative (@real_hausdorff_measure_is_measure R Y k hk)).
have [d hd he] := @real_hausdorff_product_slice_measurable_multiple R m k hk P Y pair first second hp V hVpos hVf.
have hvfin : real_hausdorff_measure hk V \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative (@real_hausdorff_measure_is_measure R Y k hk) V)).
pose v := fine (real_hausdorff_measure hk V).
have hve : real_hausdorff_measure hk V=v%:E := esym (fineK hvfin).
have hv : 0<v by move: hVpos; rewrite hve lte_fin.
pose U : set (inner_metric_space (@euclidean_inner_productP R m)) :=
  [set x | forall i, 0<=x i<=1].
have [hUc hUv] := @euclidean_unit_closed_cube R m.
have hUb := closed_borel_set (compact_closed
  (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) hUc).
have hUm := @borel_regular_borel_measurable R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  (euclidean_lebesgue_borel_regular R m) U hUb.
have hgamma := (he U hUm).2; rewrite /U hUv mule1 in hgamma.
have hl := @real_hausdorff_euclidean_rectangle_lower_bound R m P Y pair first second
  (squared_metric_product_cartesian hp) k hk U V hUm.
rewrite hgamma /U hUv mul1e hve -EFinM lee_fin in hl.
have ho i : (0 : R_n R m) i=0 by rewrite ffunE.
have hQ := @euclidean_coordinate_cube_laws R m 0 0 1 ho ler01.
rewrite add0r in hQ.
have hu := @real_hausdorff_euclidean_cube_product_upper_bound R m k hk P Y pair first second hp
  0 (@coordinate_basis R m) U 1 V hQ ler01 hVf.
change (is_true (real_hausdorff_product_slice_measure first second V (addr_ge0 hk (ler0n R m)) U<=
  (real_euclidean_product_upper_coefficient m hk*1^+m)%:E*real_hausdorff_measure hk V)%E) in hu.
rewrite hgamma hve expr1n mulr1 -EFinM lee_fin in hu.
pose L := real_euclidean_product_lower_coefficient m hk.
pose A := real_hausdorff_normalisation hk*real_hausdorff_normalisation (ler0n R m)/
  real_hausdorff_normalisation (addr_ge0 hk (ler0n R m)).
have hL := real_euclidean_product_lower_coefficient_positive m hk.
have hLA : L*A= 1.
  rewrite /L /A /real_euclidean_product_lower_coefficient.
  field; rewrite ?gt_eqF //; exact: real_hausdorff_normalisation_positive.
have hlow : L<=d/v.
  rewrite ler_pdivlMr //.
  have hb := ler_wpM2l (ltW hL) hl.
  by rewrite mulrA hLA mul1r in hb.
have hupp : d/v<=real_euclidean_product_upper_coefficient m hk.
  by rewrite ler_pdivrMr.
exists (d/v); split=> //; split=> // W hW.
rewrite (he W hW).2 hve muleAC -EFinM divfK //.
exact: lt0r_neq0 hv.
Qed.
