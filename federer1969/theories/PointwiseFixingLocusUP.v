(** Federer (1969), 3.4.8(4), p. 326:
    H_j and Q_m fix the specified original basis
    vectors pointwise. Their membership equations precede
    all subgroup, compactness and Haar conclusions. *)
From mathcomp Require Import all_boot all_order boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_pointwise_fixing_locus]: the exact
    fixed-vector equations in H_j and Q_m,
    3.4.8(4), p. 326, for a specified index set. *)
Definition is_pointwise_fixing_locus (G X:Type) (action:G->X->X) n
  (e:'I_n->X) (J:set 'I_n) (S:set G):Prop:=
  forall g,S g <->forall i,J i ->action g (e i) = e i.
