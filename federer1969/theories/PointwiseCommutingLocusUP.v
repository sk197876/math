(** Federer (1969), 3.4.12, p. 339:
    the original unitary transformations commute with complex
    scalar multiplication. Specify these actual equations before
    proving closedness, subgroup laws or Haar existence. *)
From mathcomp Require Import all_boot classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_pointwise_commuting_locus]: the original
    complex-linearity equations defining the unitary subgroup
    in 3.4.12, p. 339. This supporting
    formulation permits any actual family of operators. *)
Definition is_pointwise_commuting_locus (G X I:Type)
    (action:G->X->X) (P:I->X->X) (S:set G):Prop:=
  forall g,S g <->forall i x,action g (P i x)= P i (action g x).
