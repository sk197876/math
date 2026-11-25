(** Opaque minimum-modulus witness for Federer (1969), 3.1.1, p. 209. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom RealNormUP NormMinimumModulusUP NormMinimumModulusConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type NormMinimumModulusSignature.
(** Source for [value]: the finite infimum in Federer 3.1.1, p. 209,
    supplied independently of its private infimum construction. *)
Parameter value : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R), is_real_norm NX -> is_real_norm NY ->
  (exists x : X, x != 0) -> Hom X Y -> R.
(** Source for [laws]: the homogeneous infimum laws of Federer 3.1.1,
    p. 209, satisfied by the opaque witness. *)
Parameter laws : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
  (hNY : is_real_norm NY) (hX : exists x : X, x != 0) (L : Hom X Y),
  is_norm_minimum_modulus NX NY L (@value R X Y NX NY hNX hNY hX L).
End NormMinimumModulusSignature.
Module NormMinimumModulus : NormMinimumModulusSignature.
(** Source for [value]: private selection of the proved finite
    infimum in Federer 3.1.1, p. 209. *)
Definition value (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
  (hNY : is_real_norm NY) (hX : exists x : X, x != 0) (L : Hom X Y) : R :=
  sval (constructive_indefinite_description
    (@norm_minimum_modulus_exists R X Y NX NY hNX hNY L hX)).
(** Source for [laws]: the selected witness satisfies the minimum
    modulus specification of Federer 3.1.1, p. 209. *)
Lemma laws (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
  (hNY : is_real_norm NY) (hX : exists x : X, x != 0) (L : Hom X Y) :
  is_norm_minimum_modulus NX NY L (@value R X Y NX NY hNX hNY hX L).
Proof. exact: (svalP (constructive_indefinite_description
  (@norm_minimum_modulus_exists R X Y NX NY hNX hNY L hX))). Qed.
End NormMinimumModulus.
