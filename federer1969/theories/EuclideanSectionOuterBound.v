(** Supporting Federer (1969), 2.10.46, p. 204: a horizontal-section lower
    volume bound in Euclidean block coordinates. The set and the parameter
    set may be arbitrary. Apply the rectangle-cover argument of 2.6.2, p.
    116, through the usual isomorphism of 2.6.5, p. 120. Source context and
    the integral comparison: ProductSectionOuterBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanBlockMeasure
  EuclideanLebesgueDimensions MeasureUP MeasurePushforward ProductSections ProductSectionOuterBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_horizontal_sections_outer_lower_bound]:
    supporting fibre-volume lower estimate for 2.10.46,
    p. 204, from 2.6.2 and 2.6.5. It requires
    neither measurability nor finite measure of the two sets. *)
Theorem euclidean_horizontal_sections_outer_lower_bound (R : realType) m k
    (S : set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (A : set (inner_metric_space (@euclidean_inner_productP R k))) (c : R) :
  (0<c)%R -> (forall y, A y -> c%:E<=euclidean_lebesgue_measure m
    [set x | S (@euclidean_block_join R m k (x,y))]) ->
  c%:E*euclidean_lebesgue_measure k A<=euclidean_lebesgue_measure (m+k) S.
Proof.
move=> hc hsec.
pose T := (@euclidean_block_join R m k) @^-1` S.
have h := @product_horizontal_sections_outer_lower_bound R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
  (@euclidean_lebesgue_measure R m) (@euclidean_lebesgue_measure R k)
  (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R k) T A c hc hsec.
rewrite -euclidean_block_measure /measure_pushforward in h.
have he : (@euclidean_block_split R m k) @^-1` T=S.
  apply/seteqP; split=> x; rewrite /T /= euclidean_block_splitK; by [].
by rewrite he in h.
Qed.
