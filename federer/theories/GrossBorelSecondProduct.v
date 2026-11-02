(** Federer (1969), 2.10.46, p. 204: the Gross product identity for an
    arbitrary first factor and Borel second factor, including infinite
    second mass. Choose a Borel hull of the product with equal Gross
    measure. The measurable first-factor enlargement furnished by 2.2.13
    still has its rectangle inside this hull, so the previously proved
    measurable-factor identity applies. No Borel subset of the arbitrary
    first factor is presumed to exist. Source context and the
    projection-hull step: EuclideanRectangleMeasurableHull.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions ProjectionMeasure MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  EuclideanRectangleMeasurableHull GrossInfiniteSecondProduct GrossArbitraryProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_arbitrary_first_borel_second_product]:
    product identity of 2.10.46, p. 204, on the
    ordinary product domain of 2.1.1, p. 51. Only
    the second factor is Borel; first-factor measurability and
    finiteness of either factor are not hypotheses. *)
Theorem gross_arbitrary_first_borel_second_product (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> borel_set V ->
  (@gross_measure R n k V< +oo \/ 0<euclidean_lebesgue_measure m U) ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=
    euclidean_lebesgue_measure m U*@gross_measure R n k V.
Proof.
move=> hkn hV hdom.
have [hf|hi] := ltP (@gross_measure R n k V) +oo.
  exact: gross_product_finite_second.
have hInf : @gross_measure R n k V=+oo by apply/eqP; rewrite eq_le leey hi.
have hp : 0<euclidean_lebesgue_measure m U.
  case: hdom=> // hf; by rewrite hInf ltxx in hf.
pose rect := metric_product_rectangle
  (fun z=>(@euclidean_block_split R m n z).1)
  (fun z=>(@euclidean_block_split R m n z).2).
have hdim : (m+k<=m+n)%N by rewrite leq_add2l.
have ht := @gross_measure_is_measure R (m+n) (m+k) hdim.
have hr := @gross_measure_borel_regular R (m+n) (m+k) hdim.
have [H [hSH [hH he]]] := borel_regular_cover hr (rect U V).
have [W [hUW [hW hWH]]] := @euclidean_rectangle_first_measurable_hull R m n U V H hV hH hSH.
have hWp : 0<euclidean_lebesgue_measure m W.
  exact: lt_le_trans hp (measure_mono (euclidean_lebesgue_is_measure R m) hUW).
have hprod := @gross_measurable_borel_product R m n k W V hkn hW hV (or_intror hWp).
rewrite hInf muleC gt0_mulye // in hprod.
rewrite hInf muleC gt0_mulye //.
apply/eqP; rewrite eq_le leey /= he.
apply: le_trans _ (measure_mono ht hWH).
by rewrite hprod.
Qed.
