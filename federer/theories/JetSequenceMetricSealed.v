(** Federer (1969), 3.4.5, p. 319: the
    actual jet-series distance is hidden behind its exact formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP JetSequenceMetricUP JetSequenceMetricExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type JetSequenceMetricSignature.
(** Source for [distance]: the exact countable derivative
    distance in 3.4.5, p. 319. *)
Parameter distance:forall (R:realType) (G:choiceType) (Z:nat->lmodType R)
  (N:forall m,Z m->R),
  (forall m,is_real_norm (@N m))->(forall m,G->Z m)->G->G->R.
(** Source for [laws]: the independently specified series
    formula, 3.4.5, p. 319. *)
Parameter laws:forall (R:realType) (G:choiceType) (Z:nat->lmodType R)
  (N:forall m,Z m->R) (hN:forall m,is_real_norm (@N m)) (jet:forall m,G->Z m),
  is_jet_sequence_distance N jet (@distance R G Z N hN jet).
End JetSequenceMetricSignature.
Module JetSequenceMetric:JetSequenceMetricSignature.
(** Source for [distance]: private choice from proved finite
    series existence, 3.4.5, p. 319. *)
Definition distance (R:realType) (G:choiceType) (Z:nat->lmodType R)
    (N:forall m,Z m->R) (hN:forall m,is_real_norm (@N m)) (jet:forall m,G->Z m):=
  projT1 (cid (@jet_sequence_distance_exists R G Z N hN jet)).
(** Source for [laws]: the chosen distance satisfies the
    original series formula, 3.4.5, p. 319. *)
Lemma laws (R:realType) (G:choiceType) (Z:nat->lmodType R)
    (N:forall m,Z m->R) (hN:forall m,is_real_norm (@N m)) (jet:forall m,G->Z m):
  is_jet_sequence_distance N jet (@distance R G Z N hN jet).
Proof. exact:(projT2 (cid (@jet_sequence_distance_exists R G Z N hN jet))). Qed.
End JetSequenceMetric.
