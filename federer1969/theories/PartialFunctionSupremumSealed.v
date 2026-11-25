(** Federer (1969), 2.3.2, p. 74: sealed partial pointwise supremum. Only
    the domain, upper-bound and leastness laws cross the module boundary.
    Source context and specification: PartialFunctionSupremumUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology PartialFunctionSupremumUP
  PartialFunctionSupremumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type PartialFunctionSupremumSignature.
(** Source for [value]: abstract upper envelope in Federer
    2.3.2, p. 74, countable-family paragraph. *)
Parameter value : forall (R : realType) (X J : Type) (D : set J),
  (J -> partial_function X (extended_real_line R)) -> partial_function X (extended_real_line R).
(** Source for [laws]: the domain and supremum laws of the
    upper envelope in Federer 2.3.2, p. 74. *)
Parameter laws : forall (R : realType) (X J : Type) (D : set J)
  (f : J -> partial_function X (extended_real_line R)),
  is_partial_function_supremum D f (@value R X J D f).
End PartialFunctionSupremumSignature.
Module PartialFunctionSupremum : PartialFunctionSupremumSignature.
(** Source for [value]: private witness selection from the
    proved upper-envelope existence for Federer 2.3.2, p. 74. *)
Definition value (R : realType) (X J : Type) (D : set J)
  (f : J -> partial_function X (extended_real_line R)) :=
  projT1 (cid (@partial_function_supremum_exists R X J D f)).
(** Source for [laws]: the selected envelope satisfies the
    abstract laws supporting Federer 2.3.2, p. 74. *)
Lemma laws (R : realType) (X J : Type) (D : set J)
  (f : J -> partial_function X (extended_real_line R)) :
  is_partial_function_supremum D f (@value R X J D f).
Proof. exact: projT2 (cid (@partial_function_supremum_exists R X J D f)). Qed.
End PartialFunctionSupremum.
