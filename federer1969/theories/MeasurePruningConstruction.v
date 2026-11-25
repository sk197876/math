(** Federer (1969), 2.2.12, p. 69: private existence proof of the successive
    coordinate choices, using regular continuity from below. it does not
    reproduce this Suslin argument. The half-error budget is documented in
    MeasurePruningUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace SequenceFiniteBounds CoordinatePruningUP
  MeasurePruningUP MeasureUP RegularMeasureUP RegularProjectionLoss GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Construction.
Variables (R : realType) (X : topologicalType) (gamma : set X -> \bar R).
Variables (hm : is_measure gamma) (hr : is_regular_measure gamma).
Variables (htotal : gamma setT < +oo) (delta : R) (hd : (0 < delta)%R).

(** Source for [pruning_next_bound]: private choice at one
    stage of Federer 2.2.12, p. 69, justified by the
    proved approximation theorem, with the positive geometric budget. *)
Definition pruning_next_bound k (W : set (X * positive_sequence_space R)) :=
  projT1 (cid (@regular_projection_coordinate_approximation R X gamma hm hr W k
    (geometric_error_budget delta k) htotal (geometric_error_budget_positive k hd))).

(** Source for [pruning_witness_stage]: private recursion for
    the closed witnesses Z_i of Federer 2.2.12, p. 69.
    The initial witness and each successive coordinate cut agree
    with the abstract recursion laws. *)
Fixpoint pruning_witness_stage (Z : set (X * positive_sequence_space R)) k :=
  match k with
  | 0%N => Z
  | j.+1 => let W := pruning_witness_stage Z j in
      W `&` [set p | sequence_coordinate_bound j (pruning_next_bound j W) p.2]
  end.

(** Source for [measure_coordinate_pruning_exists]: existence
    of the m_i,Z_i selected inductively in Federer 2.2.12,
    p. 69. The construction proves, rather than assumes,
    the measure-loss and recursion laws used downstream. *)
Theorem measure_coordinate_pruning_exists (Z : set (X * positive_sequence_space R)) :
  exists b F, is_measure_coordinate_pruning gamma Z delta b F.
Proof.
pose F := pruning_witness_stage Z.
pose b k := pruning_next_bound k (F k).
exists b, F; constructor.
- constructor=> //.
- exact hd.
- move=> k; exact: projT2 (cid (@regular_projection_coordinate_approximation R X gamma hm hr
    (F k) k (geometric_error_budget delta k) htotal (geometric_error_budget_positive k hd))).
Qed.
End Construction.
