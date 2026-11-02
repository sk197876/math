(** Federer (1969), 2.3.2, p. 74: sealed partial pointwise infimum. Only the
    domain, lower-bound and greatestness laws cross the module boundary.
    Source context and specification: PartialFunctionInfimumUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology PartialFunctionInfimumUP
  PartialFunctionInfimumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type PartialFunctionInfimumSignature.
(** Source for [value]: abstract lower envelope in Federer
    2.3.2, p. 74, countable-family paragraph. *)
Parameter value : forall (R : realType) (X J : Type) (D : set J),
  (J -> partial_function X (extended_real_line R)) -> partial_function X (extended_real_line R).
(** Source for [laws]: the domain and infimum laws of the
    lower envelope in Federer 2.3.2, p. 74. *)
Parameter laws : forall (R : realType) (X J : Type) (D : set J)
  (f : J -> partial_function X (extended_real_line R)),
  is_partial_function_infimum D f (@value R X J D f).
End PartialFunctionInfimumSignature.
Module PartialFunctionInfimum : PartialFunctionInfimumSignature.
(** Source for [value]: private witness selection from the
    proved lower-envelope existence for Federer 2.3.2, p. 74. *)
Definition value (R : realType) (X J : Type) (D : set J)
  (f : J -> partial_function X (extended_real_line R)) :=
  projT1 (cid (@partial_function_infimum_exists R X J D f)).
(** Source for [laws]: the selected envelope satisfies the
    abstract laws supporting Federer 2.3.2, p. 74. *)
Lemma laws (R : realType) (X J : Type) (D : set J)
  (f : J -> partial_function X (extended_real_line R)) :
  is_partial_function_infimum D f (@value R X J D f).
Proof. exact: projT2 (cid (@partial_function_infimum_exists R X J D f)). Qed.
End PartialFunctionInfimum.
