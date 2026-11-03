(** Federer (1969), 3.2.41, printed pp. 277--278:
    the sum with a nonempty set contains a translate of the other
    set. These supporting outer-volume inequalities handle zero
    and infinite volumes without any measurability premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueTranslation VectorSetSum VectorSetSumLaws MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_vector_sum_volume_lower_left]: supporting
    zero-volume and infinite-volume boundaries of Federer 3.2.41,
    pp. 277--278. A point of the original B supplies a true
    translate of A inside the actual A+B. *)
Lemma euclidean_vector_sum_volume_lower_left (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  B !=set0 ->@euclidean_lebesgue_measure R n A<=
    @euclidean_lebesgue_measure R n (vector_set_sum A B).
Proof.
move=> [b hb].
rewrite -(@euclidean_lebesgue_translation R n b A).
apply:(@measure_mono R _ _ (euclidean_lebesgue_is_measure R n)).
move=> z [a ha <-]; rewrite addrC; exact:vector_set_sum_contains ha hb.
Qed.

(** Source for [euclidean_vector_sum_volume_lower_right]: supporting
    symmetric boundary comparison in Federer 3.2.41, pp. 277--278.
    Original nonmeasurable sources and infinite outer volumes remain. *)
Lemma euclidean_vector_sum_volume_lower_right (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  A !=set0 ->@euclidean_lebesgue_measure R n B<=
    @euclidean_lebesgue_measure R n (vector_set_sum A B).
Proof.
move=> hA; rewrite vector_set_sum_commutative.
exact:euclidean_vector_sum_volume_lower_left hA.
Qed.
