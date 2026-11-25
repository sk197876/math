(** Federer (1969), 2.4.3, pp. 81–82: pointwise numerical inequalities
    asserted almost everywhere. Both partial values must exist at each point
    where the comparison holds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_le_locus]: comparison f<=g
    used in Federer 2.4.3(2), p. 81. *)
Definition partial_extended_le_locus (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) :=
  [set x | exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ a <= b].

(** Source for [partial_extended_nonnegative_locus]: nonnegativity
    used in Federer 2.4.3(3), p. 82. *)
Definition partial_extended_nonnegative_locus (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :=
  [set x | exists a, partial_function_graph f x a /\ 0 <= a].

(** Source for [partial_extended_below_infinity_locus]: the
    pointwise conclusion f(x)<infinity in Federer 2.4.3(4),
    p. 82. Negative infinity is still permitted by this assertion. *)
Definition partial_extended_below_infinity_locus (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :=
  [set x | exists a, partial_function_graph f x a /\ a < +oo].
