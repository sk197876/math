(** Federer (1969), 3.2.41, printed pp. 277--278:
    Brunn--Minkowski for arbitrary nonempty original Euclidean
    sets. The finite-box induction, compact approximation,
    measurable approximation and actual density-one hull
    reduction discharge all of the printed proof stages. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  VectorSetSum ExtendedPositivePower EuclideanVolumeRootSum
  MeasurableBrunnMinkowski EuclideanBrunnMinkowskiHullReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_41]: direct Brunn--Minkowski theorem,
    Federer 3.2.41, p. 277. The n-th root of the outer volume
    of A+B is at least the sum of the n-th roots of the outer
    volumes of nonempty A,B in R^n, for positive n. No source
    or sum measurability, boundedness, or finiteness premise
    is imposed; zero and infinite volumes remain in scope. *)
Theorem federer_3_2_41 (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<n)%N ->A !=set0 ->B !=set0 ->
  (extended_positive_power (@euclidean_lebesgue_measure R n A) (n%:R)^-1+
    extended_positive_power (@euclidean_lebesgue_measure R n B) (n%:R)^-1<=
    extended_positive_power (@euclidean_lebesgue_measure R n (vector_set_sum A B)) (n%:R)^-1)%E.
Proof.
move=> hn.
apply:(@euclidean_brunn_minkowski_hull_reduction R n hn).
move=> C D hC hD hCNe hDNe.
exact:(@measurable_brunn_minkowski R n C D hn hC hD hCNe hDNe).
Qed.
