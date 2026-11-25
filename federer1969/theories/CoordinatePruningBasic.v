(** Federer (1969), 2.2.12, p. 69: consequences of the coordinate-pruning
    recursion, derived only from its laws. Each stage imposes the finite
    prefix of bounds, the stages decrease, and closedness is preserved. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceFiniteBounds CoordinatePruningUP
  TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [coordinate_pruning_prefix_formula]: supporting
    finite-stage version of the intersection formula for Z_i in
    Federer 2.2.12, p. 69. Stage k retains exactly those
    original witness points satisfying the first k coordinate bounds. *)
Lemma coordinate_pruning_prefix_formula (R : realType) (X : topologicalType)
    (Z : set (X * positive_sequence_space R)) b F :
  is_coordinate_pruning Z b F -> forall k,
  F k = Z `&` [set p | sequence_box_prefix b k p.2].
Proof.
move=> hF k; elim: k=> [|k ih].
- rewrite (coordinate_pruning_initial hF); apply/seteqP; split.
  + move=> p hp; split=> // i; by rewrite ltn0.
  + by move=> p [hp _].
- rewrite (coordinate_pruning_step hF) ih; apply/seteqP; split.
  + move=> p [[hz hp] hb]; split=> // i hi.
    case: (ltngtP i k)=> hik.
    * exact: hp i hik.
    * by move: hi; rewrite ltnS leqNgt hik.
    * by rewrite hik.
  + move=> p [hz hp]; split.
    * split=> // i hi; apply: hp; exact: ltn_trans hi (ltnSn k).
    * exact: hp k (ltnSn k).
Qed.

(** Source for [coordinate_pruning_decreasing]: direct nesting
    of the Z_i in Federer 2.2.12, p. 69: later stages
    retain all earlier coordinate constraints. *)
Lemma coordinate_pruning_decreasing (R : realType) (X : topologicalType)
    (Z : set (X * positive_sequence_space R)) b F :
  is_coordinate_pruning Z b F -> forall n m, (n <= m)%N -> F m `<=` F n.
Proof.
move=> hF n m hnm; rewrite !(@coordinate_pruning_prefix_formula R X Z b F hF).
move=> p [hz hp]; split=> // i hi; apply: hp; exact: leq_trans hi hnm.
Qed.

(** Source for [coordinate_pruning_closed]: direct closedness
    of every Z_i in Federer 2.2.12, p. 69. A new
    stage intersects the preceding closed set with a closed
    discrete-coordinate condition. *)
Lemma coordinate_pruning_closed (R : realType) (X : topologicalType)
    (Z : set (X * positive_sequence_space R)) b F :
  is_coordinate_pruning Z b F -> closed Z -> forall k, closed (F k).
Proof.
move=> hF hZ k; elim: k=> [|k ih].
- by rewrite (coordinate_pruning_initial hF).
- rewrite (coordinate_pruning_step hF); apply: closedI=> //.
  apply: (proj1 (continuous_closedP (@snd X (positive_sequence_space R))) _
    (@sequence_coordinate_bound R k (b k)) (@sequence_coordinate_bound_closed R k (b k))).
  exact: second_projection_continuous.
Qed.
