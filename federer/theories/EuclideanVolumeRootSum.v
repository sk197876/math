(** Federer (1969), 3.2.41, printed pp. 277--278:
    the Brunn--Minkowski comparison on the actual original pair.
    This named predicate abbreviates the displayed inequality for
    the induction; it specifies no additional mathematical object. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  VectorSetSum VectorSetSumLaws ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_volume_root_sum_bound]: direct inequality
    displayed in Federer 3.2.41, p. 277. The numbered theorem
    separately requires positive n, so no dimension-zero extension
    through totalized reciprocal zero is asserted. *)
Definition euclidean_volume_root_sum_bound (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  (extended_positive_power (@euclidean_lebesgue_measure R n A) (n%:R)^-1+
    extended_positive_power (@euclidean_lebesgue_measure R n B) (n%:R)^-1<=
    extended_positive_power (@euclidean_lebesgue_measure R n (vector_set_sum A B)) (n%:R)^-1)%E.

(** Source for [euclidean_volume_root_sum_symmetric]: supporting
    interchange of G and H in the finite-family induction of
    Federer 3.2.41, p. 277. The actual sum sets are equal. *)
Lemma euclidean_volume_root_sum_symmetric (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  euclidean_volume_root_sum_bound A B <->euclidean_volume_root_sum_bound B A.
Proof.
rewrite /euclidean_volume_root_sum_bound (@vector_set_sum_commutative _ A B)
  (@addeC R _ _); reflexivity.
Qed.
