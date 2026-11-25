(** Federer (1969), 3.2.41, printed p. 277, first proof paragraph:
    the Brunn--Minkowski inequality for the original nonempty bounded
    open coordinate boxes, before the finite-union induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions VectorSetSum EuclideanOpenCoordinateBoxUP
  EuclideanOpenCoordinateBoxSum EuclideanOpenCoordinateBoxMeasure
  ExtendedPositivePower PositiveBoxVolumeRootSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_box_brunn_minkowski]: direct first case of
    Federer 3.2.41, p. 277. The measures are the actual Euclidean
    Lebesgue measures of the two original boxes and their opaque
    actual vector sum. No independent volume or sum premise is added. *)
Theorem euclidean_box_brunn_minkowski (R : realType) n (a b c d : R_n R n)
    (A B : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<n)%N ->
  is_euclidean_open_coordinate_box a b A ->
  is_euclidean_open_coordinate_box c d B ->
  (extended_positive_power (@euclidean_lebesgue_measure R n A) (n%:R)^-1+
    extended_positive_power (@euclidean_lebesgue_measure R n B) (n%:R)^-1 <=
    extended_positive_power (@euclidean_lebesgue_measure R n (vector_set_sum A B))
      (n%:R)^-1)%E.
Proof.
move=> hn hA hB.
rewrite (open_coordinate_box_volume hA) (open_coordinate_box_volume hB)
  (open_coordinate_box_volume (open_coordinate_box_sum hA hB)).
rewrite /extended_positive_power -EFinD lee_fin.
have he i : (b+d) i-(a+c) i=(b i-a i)+(d i-c i).
  rewrite !ffunE; ring.
under [in X in _ <= X]eq_bigr do rewrite he.
exact (@positive_box_volume_root_sum R n (fun i=>b i-a i) (fun i=>d i-c i) hn
  (fun i=>ltac:(by rewrite subr_gt0; exact:hA.1 i))
  (fun i=>ltac:(by rewrite subr_gt0; exact:hB.1 i))).
Qed.
