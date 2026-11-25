(** Federer (1969), 1.10.5, p. 48, equality of the dual supremum and the
    finite-decomposition infimum. The input is an arbitrary normed vector
    space. Positive degree is the necessary condition for the unweighted
    infimum formula. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricPairing SymmetricOperatorNorm SymmetricProjectiveMass
  SymmetricMassPairingBound SymmetricMassNormingForm SymmetricMassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Duality.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation hS := (proj1 hN).
Variable m : nat.
Variable hm : (0<m)%N.

(** Source for [symmetric_mass_infimum_duality]: Federer 1.10.5,
    p. 48, the decomposition infimum satisfies exactly the dual
    mass supremum specification. The upper bound follows termwise on
    decompositions; a Hahn-Banach norming form supplies approximation. *)
Theorem symmetric_mass_infimum_duality (x : symmetric_power V m) :
  is_symmetric_mass hS x (symmetric_projective_mass hS hm x).
Proof.
constructor.
- move=> phi hp; apply: le_trans (ler_norm _) _.
  exact (@symmetric_unit_covector_mass_bound R V N hN m hm phi x hp).
- move=> eps he; have [phi [hp hv]] := symmetric_mass_norming_form hS hm x.
  exists phi; split=> //; rewrite hv ltrBlDl ltrDr; exact he.
Qed.

(** Source for [symmetric_mass_supremum_equals_infimum]: Federer
    1.10.5, p. 48, equality of the displayed dual supremum
    with the decomposition infimum, expressed as an actual real supremum. *)
Theorem symmetric_mass_supremum_equals_infimum (x : symmetric_power V m) :
  sup (symmetric_mass_unit_values hS x) = symmetric_projective_mass hS hm x.
Proof.
have [phi [hp hv]] := symmetric_mass_norming_form hS hm x.
have hn : symmetric_mass_unit_values hS x !=set0.
  exists (symmetric_pairing x phi); by exists phi.
have hb : ubound (symmetric_mass_unit_values hS x) (symmetric_projective_mass hS hm x).
  move=> r [psi [hpsi ->]].
  exact (@symmetric_mass_upper_law R V N hS m x _ (symmetric_mass_infimum_duality x) psi hpsi).
have hu : has_ubound (symmetric_mass_unit_values hS x) by exists (symmetric_projective_mass hS hm x).
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: ge_sup hn hb.
- rewrite -hv; apply: ub_le_sup; first exact hu.
  by exists phi.
Qed.
End Duality.
