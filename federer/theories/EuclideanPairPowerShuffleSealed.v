(** Opaque orthogonal coordinate regrouping for Federer (1969), 2.10.29, p.
    195. Expose only the two maps and their proved inverse, distance and set
    membership specification. *)
From mathcomp Require Import all_boot all_algebra boolp reals.
From Federer Require Import EuclideanPairPowerShuffleUP EuclideanPairPowerShuffleConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type EUCLIDEAN_PAIR_POWER_SHUFFLE.
(** Source for [value]: abstract coordinate
    regrouping supporting 2.10.29, p. 195. *)
Parameter value : forall (R : realType) q, euclidean_pair_power_shuffle_data R q.
(** Source for [laws]: inverse, orthogonal
    metric and set membership laws of
    the identification in 2.10.29, p. 195. *)
Parameter laws : forall (R : realType) q, is_euclidean_pair_power_shuffle (@value R q).
End EUCLIDEAN_PAIR_POWER_SHUFFLE.
Module EuclideanPairPowerShuffle : EUCLIDEAN_PAIR_POWER_SHUFFLE.
(** Source for [value]: selected proved
    coordinate witness for 2.10.29, p. 195,
    hidden by opaque module ascription. *)
Definition value (R : realType) q := projT1 (cid (@euclidean_pair_power_shuffle_exists R q)).
(** Source for [laws]: proved abstract
    specification of the orthogonal regrouping
    used in 2.10.29, p. 195. *)
Lemma laws (R : realType) q : is_euclidean_pair_power_shuffle (@value R q).
Proof. exact: projT2 (cid (@euclidean_pair_power_shuffle_exists R q)). Qed.
End EuclideanPairPowerShuffle.
