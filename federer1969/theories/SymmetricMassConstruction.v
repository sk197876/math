(** Federer (1969), 1.10.5, p. 48: private existence witness for the dual
    mass supremum in every degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricLowPowers SymmetricMassUP SymmetricProjectiveMass
  SymmetricMassDuality SymmetricDegreeZeroMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_mass_exists]: Federer 1.10.5,
    p. 48, existence of the real value specified by the dual
    supremum. The positive-degree infimum and the scalar zero-degree
    calculation are used solely to prove existence. *)
Theorem symmetric_mass_exists (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) m (x : symmetric_power V m) :
  exists c : R, is_symmetric_mass (proj1 hN) x c.
Proof.
case: m x=> [x|m x].
- exists `|symmetric_zeroth_inverse V x|.
  exact: symmetric_degree_zero_mass_specification.
- exists (symmetric_projective_mass (proj1 hN) (ltn0Sn m) x).
  exact: symmetric_mass_infimum_duality.
Qed.
