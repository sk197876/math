(** Federer (1969), 1.10.5, p. 48: sealed existence of the mass infimum in
    positive degree. Source context and conventions:
    SymmetricMassInfimumUP.v. The real-infimum construction is hidden behind
    the abstract approximation and lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricMassInfimumUP SymmetricMassInfimumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SymmetricMassInfimumSignature.
(** Source for [value]: Federer 1.10.5, p. 48,
    abstract real mass infimum for positive degree and a given seminorm. *)
Parameter value : forall (R : realType) (V : lmodType R) (N : V -> R),
  is_real_seminorm N -> forall m, (0<m)%N -> symmetric_power V m -> R.
(** Source for [laws]: Federer 1.10.5, p. 48,
    the chosen value satisfies the infimum specification. *)
Parameter laws : forall (R : realType) (V : lmodType R) (N : V -> R)
  (hN : is_real_seminorm N) m (hm : (0<m)%N) (x : symmetric_power V m),
  is_symmetric_mass_infimum N x (@value R V N hN m hm x).
End SymmetricMassInfimumSignature.

Module SymmetricMassInfimum : SymmetricMassInfimumSignature.
(** Source for [value]: Federer 1.10.5, p. 48,
    private selection from the proved existence theorem. *)
Definition value (R : realType) (V : lmodType R) (N : V -> R)
    (hN : is_real_seminorm N) m (hm : (0<m)%N) (x : symmetric_power V m) :=
  projT1 (cid (@symmetric_mass_infimum_exists R V N hN m hm x)).
(** Source for [laws]: Federer 1.10.5, p. 48,
    the selected witness discharges the abstract infimum laws. *)
Lemma laws (R : realType) (V : lmodType R) (N : V -> R)
    (hN : is_real_seminorm N) m (hm : (0<m)%N) (x : symmetric_power V m) :
  is_symmetric_mass_infimum N x (@value R V N hN m hm x).
Proof. exact: projT2 (cid (@symmetric_mass_infimum_exists R V N hN m hm x)). Qed.
End SymmetricMassInfimum.
