(** Federer (1969), 1.10.5, p. 48: sealed implementation of the dual mass
    specification. Source context and the degree-zero convention:
    SymmetricMassConstruction.v. Only the abstract supremum laws are exposed
    to downstream developments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricMassUP SymmetricMassConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SymmetricMassSignature.
(** Source for [value]: Federer 1.10.5, p. 48, the real
    mass of a symmetric vector over an arbitrary normed real space. *)
Parameter value : forall (R : realType) (V : lmodType R) (N : V -> R),
  is_real_norm N -> forall m, symmetric_power V m -> R.
(** Source for [laws]: Federer 1.10.5, p. 48, the
    mass value satisfies the upper-bound and approximation laws
    defining the dual supremum. *)
Parameter laws : forall (R : realType) (V : lmodType R) (N : V -> R)
  (hN : is_real_norm N) m (x : symmetric_power V m),
  is_symmetric_mass (proj1 hN) x (@value R V N hN m x).
End SymmetricMassSignature.

Module SymmetricMass : SymmetricMassSignature.
(** Source for [value]: Federer 1.10.5, p. 48,
    private choice from the proved existence theorem. *)
Definition value (R : realType) (V : lmodType R) (N : V -> R)
    (hN : is_real_norm N) m (x : symmetric_power V m) :=
  projT1 (cid (@symmetric_mass_exists R V N hN m x)).
(** Source for [laws]: Federer 1.10.5, p. 48,
    the private witness discharges the public supremum specification. *)
Lemma laws (R : realType) (V : lmodType R) (N : V -> R)
    (hN : is_real_norm N) m (x : symmetric_power V m) :
  is_symmetric_mass (proj1 hN) x (@value R V N hN m x).
Proof. exact: projT2 (cid (@symmetric_mass_exists R V N hN m x)). Qed.
End SymmetricMass.
