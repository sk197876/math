(** Federer (1969), 2.10.46, p. 204: the Gross product equality on completed
    measurable factors. A finite Gross-measurable second factor contains a
    Borel subset of equal measure by the finite sandwich of 2.2.3, p. 61.
    Monotonicity gives the lower bound from that Borel subset; the upper
    estimate already applies to arbitrary sets. Source context and the
    completion argument: GrossMeasurableProduct.v. The assertion for
    nonmeasurable factors is not proved here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions ProjectionMeasure MeasureUP MeasureBasic
  BorelRegularMeasureUP BorelRegularSandwich GrossMeasurableProduct GrossProductUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_completed_product_finite_second]: product
    identity of 2.10.46, p. 204, for a
    Lebesgue-measurable first factor in positive dimension and
    a finite Gross-measurable second factor. Neither factor
    is required to be Borel or to have finite first volume. *)
Theorem gross_completed_product_finite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> measure_measurable (@euclidean_lebesgue_measure R m.+1) U ->
  measure_measurable (@gross_measure R n k) V -> (@gross_measure R n k V< +oo)%E ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=
    (euclidean_lebesgue_measure m.+1 U*@gross_measure R n k V)%E.
Proof.
move=> hkn hU hV hfin.
have hm := @gross_measure_is_measure R n k hkn.
have hr := @gross_measure_borel_regular R n k hkn.
have [D [B [hD [hB [hDV [hVB hz]]]]]] := borel_regular_finite_sandwich hm hr hV hfin.
have hDB : D `<=` B := subset_trans hDV hVB.
have hi : B `&` D=D.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hDB.
have hval := borel_regular_borel_measurable hm hr hD B.
rewrite hi hz adde0 in hval.
have hDVval := measure_mono hm hDV.
have hVBval := measure_mono hm hVB.
have heq : @gross_measure R n k D=@gross_measure R n k V.
  apply/eqP; rewrite eq_le hDVval /=; by rewrite -hval.
have hDf : (@gross_measure R n k D< +oo)%E by rewrite heq.
have hprod := @gross_measurable_product_finite_second R m n k U D hkn hU hD hDf.
have hupp := @gross_product_upper_finite_second R m n k U V hkn hfin.
apply/eqP; rewrite eq_le hupp /= -heq -hprod.
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
apply: (measure_mono (@gross_measure_is_measure R (m.+1+n) (m.+1+k) hdim))=> x [hx hy].
split=> //; exact: hDV hy.
Qed.
