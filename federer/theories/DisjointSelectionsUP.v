(** Abstract two-selection specification for Federer (1969), 2.2.4, p. 62.
    Each function chooses a member of every prescribed set and their ranges
    are disjoint. These are the exact consequences of the printed
    transfinite construction needed by the measure argument. Source
    editions: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_disjoint_family_selection]: supporting abstract laws for
    f and g in Federer 2.2.4, p. 62 Both images meet every prescribed
    member, and no value of one selection is a value of the other. *)
Record is_disjoint_family_selection (I T : Type) (E : I -> set T)
    (f g : I -> T) : Prop := {
  disjoint_selection_left_member : forall i, E i (f i);
  disjoint_selection_right_member : forall i, E i (g i);
  disjoint_selection_separated : forall i j, f i <> g j
}.
