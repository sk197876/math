(** Federer (1969), 2.10.46, pp. 203–204: the Gross product upper bound for
    finite second-factor mass and positive first dimension. Pass from the
    finite positive calculation to arbitrary first volume, handling a null
    second factor by its independently proved nullity theorem. The latter
    also proves zero when the printed ordinary product is undefined; the
    totalised zero-times-infinity notation here denotes that proved endpoint
    extension, not a silently imposed book convention. Source context:
    GrossFiniteProductUpper.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  MetricProductRectangles EuclideanLebesgueDimensions ProjectionMeasure
  MeasureUP MeasureBasic GrossFiniteProductUpper GrossProductNullFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_product_upper_finite_second]: finite
    second-factor upper inequality of 2.10.46, pp. 203–204,
    with arbitrary first sets in positive dimension. The null
    second factor is proved separately and then included in the
    totalised formula, even for infinite first volume. *)
Theorem gross_product_upper_finite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (@gross_measure R n k V< +oo)%E ->
  (@gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)<=
    euclidean_lebesgue_measure m.+1 U*@gross_measure R n k V)%E.
Proof.
move=> hkn hfin.
have [hzero|hnzero] := eqVneq (@gross_measure R n k V) 0%E.
  by rewrite (@gross_product_null_second_factor R m.+1 n k V hkn hzero U) hzero mule0.
have hvnon := measure_nonnegative (@gross_measure_is_measure R n k hkn) V.
have hvfin : @gross_measure R n k V \is a fin_num by rewrite (ge0_fin_numE hvnon).
pose v := fine (@gross_measure R n k V).
have hve : @gross_measure R n k V=v%:E := esym (fineK hvfin).
have hv : 0<v.
  have hh : (0<@gross_measure R n k V)%E by rewrite lt_def hnzero hvnon.
  by move: hh; rewrite hve lte_fin.
have hunon := measure_nonnegative (euclidean_lebesgue_is_measure R m.+1) U.
rewrite hve.
case hU: (euclidean_lebesgue_measure m.+1 U) hunon=> [u| |] hunon.
- rewrite lee_fin in hunon; rewrite -EFinM.
  exact (@gross_finite_product_upper_bound R m n k U V u v hkn hunon hv hU hve).
- by rewrite gt0_mulye ?lte_fin // leey.
- by rewrite leeNy_eq in hunon.
Qed.

(** Source for [gross_product_upper_defined]: upper product
    inequality of 2.10.46, p. 204, in positive first
    dimension on the ordinary defined-product domain of 2.1.1,
    p. 51. A finite second mass also includes the separately
    proved null-second-factor extension. For infinite second mass,
    positive first volume makes the upper bound infinity. *)
Theorem gross_product_upper_defined (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N ->
  ((@gross_measure R n k V< +oo)%E \/
    (0<euclidean_lebesgue_measure m.+1 U)%E) ->
  (@gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)<=
    euclidean_lebesgue_measure m.+1 U*@gross_measure R n k V)%E.
Proof.
move=> hkn hdomain.
have [hfin|hinf] := ltP (@gross_measure R n k V) +oo%E.
  exact: gross_product_upper_finite_second.
have heq : @gross_measure R n k V=+oo%E.
  apply/eqP; by rewrite eq_le leey hinf.
have hpos : (0<euclidean_lebesgue_measure m.+1 U)%E.
  case: hdomain=> // hh; by move: hh; rewrite heq ltxx.
by rewrite heq muleC gt0_mulye // leey.
Qed.
