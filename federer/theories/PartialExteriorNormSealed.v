(** Federer (1969), 3.2.20, p. 256: opaque intrinsic
    exterior norm on a bounded partial graph. Only its independently
    specified least-bound laws are exposed; supremum witnesses are private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations PartialFunctionUP
  PartialExteriorNormUP PartialExteriorNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type PARTIAL_EXTERIOR_NORM.
(** Source for [value]: the norm supporting Federer 3.2.20,
    p. 256, conditional on a proved finite nonnegative bound
    on its actual partial exterior words. *)
Parameter value : forall (R : realType) (n k q : nat)
  (d : partial_function (R_n R n) (R_n R k)),
  (exists L : R, 0<=L /\ is_partial_exterior_bound q d L) -> R.
(** Source for [laws]: the independent norm laws of Federer
    3.2.20, p. 256, with the supremum convention of 1.7.6,
    p. 33. The implementation proves these laws. *)
Parameter laws : forall (R : realType) n k q
  (d : partial_function (R_n R n) (R_n R k))
  (hd : exists L : R, 0<=L /\ is_partial_exterior_bound q d L),
  is_partial_exterior_norm q d (@value R n k q d hd).
End PARTIAL_EXTERIOR_NORM.
Module PartialExteriorNorms : PARTIAL_EXTERIOR_NORM.
(** Source for [value]: select the proved bounded-cost norm
    witness supporting Federer 3.2.20, p. 256; opaque ascription
    hides the real supremum construction. *)
Definition value (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k))
    (hd : exists L : R, 0<=L /\ is_partial_exterior_bound q d L) :=
  projT1 (cid (@partial_exterior_norm_bounded_witness_exists R n k q d hd)).
(** Source for [laws]: the selected witness satisfies the norm
    laws supporting Federer 3.2.20, p. 256. *)
Lemma laws (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k))
    (hd : exists L : R, 0<=L /\ is_partial_exterior_bound q d L) :
  is_partial_exterior_norm q d (@value R n k q d hd).
Proof. exact: projT2 (cid (@partial_exterior_norm_bounded_witness_exists R n k q d hd)). Qed.
End PartialExteriorNorms.
