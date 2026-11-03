(** Federer (1969), 3.2.41, printed p. 277, last displayed
    finite-family induction step: the two paired sums lie in
    opposite strict coordinate halfspaces of the original sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCoordinateHalfspaces MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coordinate_separated_volume_lower]: supporting
    first inequality in the last display of Federer 3.2.41,
    p. 277. Each original subset may be nonmeasurable and
    every volume may be infinite: the actual measurable separator
    and its null hyperplane suffice for this outer-volume bound. *)
Lemma coordinate_separated_volume_lower (R:realType) n (i:'I_n) (t:R)
    (C P Q:set (inner_metric_space (@euclidean_inner_productP R n))):
  P `<=` C ->Q `<=` C ->
  (forall x,P x ->(x i<t)%R) ->(forall x,Q x ->(t<x i)%R) ->
  @euclidean_lebesgue_measure R n P+@euclidean_lebesgue_measure R n Q<=
    @euclidean_lebesgue_measure R n C.
Proof.
move=> hPC hQC hLow hHigh.
rewrite (@euclidean_coordinate_halfspace_volume_split R n i t C).
apply:leeD.
- apply:(@measure_mono R _ _ (euclidean_lebesgue_is_measure R n)).
  move=> x hx; split; [exact:hPC x hx|exact:hLow x hx].
- apply:(@measure_mono R _ _ (euclidean_lebesgue_is_measure R n)).
  move=> x hx; split; [exact:hQC x hx|exact:hHigh x hx].
Qed.
