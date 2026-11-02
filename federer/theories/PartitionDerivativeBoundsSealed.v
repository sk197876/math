(** Opaque sufficient derivative constants for the
    smooth partition in Federer (1969), 3.1.13,
    p. 225. Only their recurrence is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import PartitionDerivativeBoundsUP PartitionDerivativeBoundsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type PartitionDerivativeBoundsSignature.
(** Source for [value]: the constants V_i
    depend only on C and G,
    with C= 129^m in Federer 3.1.13,
    p. 225. *)
Parameter value : forall (R : realType), R->(nat->R)->nat->R.
(** Source for [laws]: the sufficient recurrence
    for V_i is proved, supporting the
    last estimate in Federer 3.1.13, p. 225. *)
Parameter laws : forall (R : realType) C G,
  is_partition_derivative_bounds C G (@value R C G).
End PartitionDerivativeBoundsSignature.

Module PartitionDerivativeBounds : PartitionDerivativeBoundsSignature.
(** Source for [value]: choose the privately
    proved recurrence witness, Federer 3.1.13,
    p. 225. *)
Definition value (R : realType) C G : nat->R :=
  projT1 (cid (@partition_derivative_bounds_exists R C G)).
(** Source for [laws]: proof of the
    exposed recurrence specification, supporting
    Federer 3.1.13, p. 225. *)
Lemma laws (R : realType) C G :
  is_partition_derivative_bounds C G (@value R C G).
Proof. exact: (projT2 (cid (@partition_derivative_bounds_exists R C G))). Qed.
End PartitionDerivativeBounds.
