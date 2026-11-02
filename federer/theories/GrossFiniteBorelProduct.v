(** Federer (1969), 2.10.46, p. 204: combine the two independently proved
    inequalities to obtain the Gross product identity for Borel factors of
    finite first volume. Infinite second measure is included when the first
    volume is positive, as required by the ordinary arithmetic convention of
    2.1.1, p. 51. This does not assert the still separate extension to
    arbitrary factors. Source context and the partition argument:
    GrossBorelProductLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions ProjectionMeasure MeasureUP MeasureBasic TopologicalBorel
  GrossBorelProductLower GrossProductUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_finite_borel_product]: Gross product
    equality of 2.10.46, p. 204, for Borel factors,
    positive first dimension, and finite first volume. The
    second measure may be infinite if the first volume is
    positive. A zero first volume requires finite second mass. *)
Theorem gross_finite_borel_product (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) (u : R) :
  (k<=n)%N -> borel_set U -> borel_set V ->
  euclidean_lebesgue_measure m.+1 U=u%:E ->
  ((0<u)%R \/ (@gross_measure R n k V< +oo)%E) ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=
    (u%:E*@gross_measure R n k V)%E.
Proof.
move=> hkn hU hV hvol hdomain.
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
have hunon : 0<=u.
  have hh := measure_nonnegative (euclidean_lebesgue_is_measure R m.+1) U.
  by move: hh; rewrite hvol lee_fin.
have hdom : (@gross_measure R n k V< +oo)%E \/ (0<euclidean_lebesgue_measure m.+1 U)%E.
  case: hdomain=> [hu|hv]; [right; by rewrite hvol lte_fin|by left].
have hupper := @gross_product_upper_defined R m n k U V hkn hdom.
rewrite hvol in hupper.
apply/eqP; rewrite eq_le hupper /=.
have [->|hne] := eqVneq u 0.
  rewrite mul0e; exact (measure_nonnegative (@gross_measure_is_measure R (m.+1+n) (m.+1+k) hdim) _).
have hu : 0<u by rewrite lt_def hne hunon.
exact (@gross_borel_product_lower_finite_first R m.+1 n k U V u hkn hU hV hu hvol).
Qed.
