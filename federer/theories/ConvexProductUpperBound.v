(** Federer (1969), 2.10.46, pp. 203–204: the Caratheodory product upper
    bound for finite second-factor mass and positive first dimension. Pass
    from the finite positive calculation to arbitrary first volume, handling
    a null second factor by its independently proved nullity theorem. The
    latter also proves zero when the printed ordinary product is undefined;
    the totalised zero-times-infinity notation here denotes that proved
    endpoint extension, not a silently imposed book convention. Source
    context: ConvexFiniteProductUpper.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  MetricProductRectangles EuclideanLebesgueDimensions ProjectionMeasure
  MeasureUP MeasureBasic ConvexFiniteProductUpper ConvexProductNullFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [caratheodory_projection_product_upper_finite_second]: finite
    second-factor upper inequality of 2.10.46, pp. 203–204,
    with arbitrary first sets in positive dimension. The null
    second factor is proved separately and then included in the
    totalised formula, even for infinite first volume. *)
Theorem caratheodory_projection_product_upper_finite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (@caratheodory_projection_measure R n k V< +oo)%E ->
  (@caratheodory_projection_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)<=
    euclidean_lebesgue_measure m.+1 U*@caratheodory_projection_measure R n k V)%E.
Proof.
move=> hkn hfin.
have [hzero|hnzero] := eqVneq (@caratheodory_projection_measure R n k V) 0%E.
  by rewrite (@caratheodory_projection_product_null_second_factor R m.+1 n k V hkn hzero U) hzero mule0.
have hvnon := measure_nonnegative (@caratheodory_projection_measure_is_measure R n k hkn) V.
have hvfin : @caratheodory_projection_measure R n k V \is a fin_num by rewrite (ge0_fin_numE hvnon).
pose v := fine (@caratheodory_projection_measure R n k V).
have hve : @caratheodory_projection_measure R n k V=v%:E := esym (fineK hvfin).
have hv : 0<v.
  have hh : (0<@caratheodory_projection_measure R n k V)%E by rewrite lt_def hnzero hvnon.
  by move: hh; rewrite hve lte_fin.
have hunon := measure_nonnegative (euclidean_lebesgue_is_measure R m.+1) U.
rewrite hve.
case hU: (euclidean_lebesgue_measure m.+1 U) hunon=> [u| |] hunon.
- rewrite lee_fin in hunon; rewrite -EFinM.
  exact (@caratheodory_projection_finite_product_upper_bound R m n k U V u v hkn hunon hv hU hve).
- by rewrite gt0_mulye ?lte_fin // leey.
- by rewrite leeNy_eq in hunon.
Qed.

(** Source for [caratheodory_projection_product_upper_defined]: upper product
    inequality of 2.10.46, p. 203, in positive first
    dimension on the ordinary defined-product domain of 2.1.1,
    p. 51. A finite second mass also includes the separately
    proved null-second-factor extension. For infinite second mass,
    positive first volume makes the upper bound infinity. *)
Theorem caratheodory_projection_product_upper_defined (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N ->
  ((@caratheodory_projection_measure R n k V< +oo)%E \/
    (0<euclidean_lebesgue_measure m.+1 U)%E) ->
  (@caratheodory_projection_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)<=
    euclidean_lebesgue_measure m.+1 U*@caratheodory_projection_measure R n k V)%E.
Proof.
move=> hkn hdomain.
have [hfin|hinf] := ltP (@caratheodory_projection_measure R n k V) +oo%E.
  exact: caratheodory_projection_product_upper_finite_second.
have heq : @caratheodory_projection_measure R n k V=+oo%E.
  apply/eqP; by rewrite eq_le leey hinf.
have hpos : (0<euclidean_lebesgue_measure m.+1 U)%E.
  case: hdomain=> // hh; by move: hh; rewrite heq ltxx.
by rewrite heq muleC gt0_mulye // leey.
Qed.
