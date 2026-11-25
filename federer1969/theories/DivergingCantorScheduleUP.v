(** Federer (1969), 3.3.21, p. 309: the exact original subdivision hypothesis. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [cantor_schedule_tends_infinity]: the original
    n_j->infinity hypothesis of 3.3.21, p. 309. Every eventual
    natural threshold is attained permanently. Monotonicity and any
    specified rate of growth are deliberately not imposed. *)
Definition cantor_schedule_tends_infinity (n:nat->nat):Prop:=
  forall N:nat,exists J:nat,forall j,(J<=j)%N ->(N<=n j)%N.
