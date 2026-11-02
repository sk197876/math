(** Federer (1969), 1.8.2, p. 39: complex absolute value exposed only by its
    nonnegative square specification. Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import ComplexScalarSealed ComplexModulusUP ComplexModulusConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type ComplexModulusSig.
(** Source for [norm]: Federer 1.8.2, p. 39,
    scalar absolute value used in Hermitian Cauchy's inequality. *)
Parameter norm : forall R : rcfType, ComplexScalars.C R -> R.
(** Source for [laws]: Federer 1.8.2, p. 39,
    the chosen absolute value obeys its defining specification. *)
Parameter laws : forall (R : rcfType) (z : ComplexScalars.C R),
  is_complex_modulus z (@norm R z).
End ComplexModulusSig.
Module ComplexModulus : ComplexModulusSig.
(** Source for [norm]: Federer 1.8.2, p. 39,
    select the proved modulus witness inside the opaque module. *)
Definition norm (R : rcfType) (z : ComplexScalars.C R) : R :=
  sval (constructive_indefinite_description (complex_modulus_exists z)).
(** Source for [laws]: Federer 1.8.2, p. 39,
    the selected witness satisfies the public scalar laws. *)
Lemma laws (R : rcfType) (z : ComplexScalars.C R) : is_complex_modulus z (@norm R z).
Proof. exact: (svalP (constructive_indefinite_description (complex_modulus_exists z))). Qed.
End ComplexModulus.
