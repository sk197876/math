(** Federer (1969), 2.5.10, p. 101, first paragraph: summing densities
    supported on pairwise disjoint pieces. This abstract specification means
    agreement on each piece and zero outside the union; it requires no
    countability of the family. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [is_disjoint_function_gluing]: abstract density gluing law in
    Federer 2.5.10, p. 101, first paragraph Local functions are specified
    only on their own pieces. *)
Definition is_disjoint_function_gluing (R : realType) (X J : Type)
    (D : set J) (B : J -> set X) (f : J -> X -> R) (g : X -> R) :=
  (forall j x, D j -> B j x -> g x=f j x) /\
  forall x, ~ (\bigcup_(j in D) B j) x -> g x=0.
