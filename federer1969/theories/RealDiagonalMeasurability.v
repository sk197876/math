(** We prove the bounded diagonal directly from rational-cut triangles. This
    supports the local associativity correction to Federer 2.6.5, p. 119,
    and the diagonal example in 2.6.3(1), p. 117. No external product Borel
    algebra is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureFiniteClosure ProductMeasure
  ProductRectangleMeasurability ProductMeasureTranspose ProductTransposeMeasurability
  RealOrderTriangle ProductAssociativityObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_segment_diagonal_triangles]: Supporting Federer
    2.6.3(1), p. 117.Remove the two strict-order triangles of Federer 2.6.7,
    p. 121, from the closed square. *)
Lemma closed_segment_diagonal_triangles (R : realType) (a b : R) :
  restricted_diagonal [set x | a <= x /\ x <= b] =
  ([set x | a <= x /\ x <= b] `*` [set x | a <= x /\ x <= b]) `\`
    (real_order_triangle a b `|` product_transpose (real_order_triangle a b)).
Proof.
rewrite /restricted_diagonal /real_order_triangle /product_transpose.
apply/seteqP; split; move=> [x y] /=.
- move=> [[hax hxb] hxy]; subst y; split; first by split; split.
  move=> [[_ [hxx _]]|[_ [hxx _]]]; by rewrite ltxx in hxx.
- move=> [[[hax hxb] [hay hyb]] hn]; split; first by split.
  apply/eqP; rewrite eq_le; apply/andP; split.
  + rewrite leNgt; apply/negP=> hyx; apply: hn; right; by split=> //; split.
  + rewrite leNgt; apply/negP=> hxy; apply: hn; left; by split=> //; split.
Qed.

(** Source for [real_closed_segment_diagonal_measurable]: also the diagonal
    in Federer 2.6.3(1), p. 117. Measurable lower rays and the segment
    suffice; Borel regularity is not needed for this conclusion. *)
Theorem real_closed_segment_diagonal_measurable (R : realType)
    (alpha beta : set R -> \bar R) (ha : is_measure alpha) (hb : is_measure beta)
    (a b : R) :
  (forall t, measure_measurable alpha [set x | x < t]) ->
  (forall t, measure_measurable alpha [set x | x <= t]) ->
  (forall t, measure_measurable beta [set x | x < t]) ->
  (forall t, measure_measurable beta [set x | x <= t]) ->
  measure_measurable alpha [set x | a <= x /\ x <= b] ->
  measure_measurable beta [set x | a <= x /\ x <= b] ->
  measure_measurable (product_measure ha hb)
    (restricted_diagonal [set x | a <= x /\ x <= b]).
Proof.
move=> hAo hAc hBo hBc hA hB.
rewrite closed_segment_diagonal_triangles.
apply: (measure_measurable_difference (product_measure_is_measure ha hb)).
- exact: product_measure_rectangle_measurable hA hB.
- apply: (measure_measurable_union (product_measure_is_measure ha hb)).
  + exact (@real_order_triangle_measurable R alpha beta ha hb a b hAo hBc).
  + exact (@product_measurable_transpose R R R beta alpha hb ha (real_order_triangle a b)
      (@real_order_triangle_measurable R beta alpha hb ha a b hBo hAc)).
Qed.
