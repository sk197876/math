(** Opaque selection of the projection constants of Federer (1969),
    2.7.16(6), pp. 139–140, used in 2.10.5, p. 172. Source context:
    ProjectionBetaConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExteriorDiameterUP ProjectionConstantNorms ProjectionBetaConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

Module Type ProjectionBetaSignature.
(** Source for [value]: abstract normalization beta_t
    in Federer 2.10.5, p. 172. *)
Parameter value : forall (R : realType) (n m : nat), (m<=n)%N ->
  \bar R -> R.
(** Source for [laws]: the universal projection-norm
    formula of Federer 2.7.16(6), pp. 139–140,
    for the normalization used in 2.10.5, p. 172. *)
Parameter laws : forall (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (t : \bar R) (ht : 1<=t),
  is_extended_projection_constant (real_exterior_two_nonzero R) t n m
    (@value R n m hmn t).
End ProjectionBetaSignature.

Module ProjectionBeta : ProjectionBetaSignature.
(** Source for [value]: private selection from the
    proved existence of the beta used in Federer
    2.10.5, p. 172. *)
Definition value := @projection_beta_witness.
(** Source for [laws]: the private witness satisfies
    the normalization formula required in Federer
    2.10.5, p. 172. *)
Lemma laws (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (t : \bar R) (ht : 1<=t) :
  is_extended_projection_constant (real_exterior_two_nonzero R) t n m
    (@value R n m hmn t).
Proof. exact: (@projection_beta_witness_laws R n m hmn t ht). Qed.
End ProjectionBeta.
