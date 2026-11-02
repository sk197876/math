(** Federer (1969), 2.2.6, p. 63: the metric induces the Cartesian product
    topology of discrete positive-integer factors. Finite coordinate
    cylinders form the product-neighborhood base; initial segments suffice
    because every finite set of natural indices is bounded. The proof uses
    only the exposed metric formula and coordinate representation. Source
    editions: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpaceUP SequenceSpace SequenceWeights
  SequenceMetricPrefixes SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_prefix]: Federer 2.2.6,
    p. 63, supporting basic product neighborhood: agreement with
    a fixed sequence on its first N coordinates. The zero prefix
    imposes no restriction and is the whole space. *)
Definition positive_sequence_prefix (R : realType) (x : positive_sequence_space R) N :
    set (positive_sequence_space R) :=
  [set y | forall i, (i < N)%N -> positive_sequence_coordinates x i = positive_sequence_coordinates y i].

(** Source for [positive_sequence_prefix_neighborhood]: Federer
    2.2.6, p. 63, supporting direction of topology compatibility:
    a sufficiently small metric ball fixes any prescribed finite
    initial segment of coordinates. *)
Lemma positive_sequence_prefix_neighborhood (R : realType)
    (x : positive_sequence_space R) N : nbhs x (positive_sequence_prefix x N).
Proof.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x (positive_sequence_prefix x N))).
exists (sequence_metric_weight N / 2); first by rewrite /= divr_gt0 ?sequence_metric_weight_positive ?ltr0n.
move=> y hdist i hi.
apply: (@positive_sequence_small_distance_coordinate R _ _ _
  (positive_sequence_distance_specification R) x y i).
apply: lt_le_trans hdist _; apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
apply: sequence_metric_weight_antitone; exact: ltnW hi.
Qed.

(** Source for [positive_sequence_product_neighborhoods]: Federer 2.2.6, p.
    63, metric/product topology agreement in the finite-coordinate
    neighborhood-base formulation: a set is a neighborhood exactly when it
    contains an initial-coordinate cylinder. *)
Theorem positive_sequence_product_neighborhoods (R : realType)
    (x : positive_sequence_space R) (U : set (positive_sequence_space R)) :
  nbhs x U <-> exists N, positive_sequence_prefix x N `<=` U.
Proof.
split.
- move=> hu; have [r hr hball] := proj1 (metricType_numDomainType.nbhs_mdistP x U) hu.
  have [N hN] := sequence_inverse_power_small hr.
  exists N=> y hy; apply: hball; rewrite /= positive_sequence_metric_distanceE.
  apply: le_lt_trans _ hN.
  exact: (@positive_sequence_prefix_distance_bound R _ _ _
    (positive_sequence_distance_specification R) x y N hy).
- move=> [N hN]; exact: filterS hN (positive_sequence_prefix_neighborhood x N).
Qed.
