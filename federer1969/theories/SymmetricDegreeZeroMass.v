(** Federer (1969), 1.10.5, p. 48: mass in degree zero is scalar absolute
    value. Source context and the positive-degree restriction on the
    unweighted infimum: SymmetricDegreeZeroPairing.v. The dual supremum is
    valid in degree zero and is attained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP SeminormNormingFunctional SymmetricAlgebra
  SymmetricGrading SymmetricLowPowers SymmetricForms SymmetricFormZero
  SymmetricPairing SymmetricOperatorNorm SymmetricOperatorBoundary
  SymmetricMassUP SymmetricDegreeZeroPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DegreeZero.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Local Notation kappa := (symmetric_operator_norm (W:=R^o) hN (fun r:R=>`|r|)).

(** Source for [symmetric_degree_zero_mass_attained]: Federer
    1.10.5, p. 48, supporting degree-zero duality. There is
    a scalar zero-form of norm at most one pairing to the absolute
    value of the scalar coordinate, including when that coordinate is zero. *)
Lemma symmetric_degree_zero_mass_attained (x : symmetric_power V 0) :
  exists phi : S_m V R^o 0, (kappa phi <= 1)%E /\
    symmetric_pairing x phi = `|symmetric_zeroth_inverse V x|.
Proof.
pose c : R := symmetric_zeroth_inverse V x.
have [f [hf hfc]] := @seminorm_norming_functional R R^o (fun r:R=>`|r|)
  (proj1 (scalar_absolute_value_norm R)) c.
exists (zero_sform V (f 1)); split.
- rewrite symmetric_operator_constant lee_fin.
  have hh := hf 1; by rewrite normr1 in hh.
- rewrite symmetric_degree_zero_pairing zero_sformE.
  change (c * f 1 = `|c|).
  have hh : f (c *: (1:R^o)) = c *: f 1 by rewrite linearZ.
  change (f (c*1) = c*f 1) in hh.
  by rewrite mulr1 hfc in hh; symmetry.
Qed.

(** Source for [symmetric_degree_zero_mass_specification]: Federer
    1.10.5, p. 48, the displayed dual supremum equals absolute
    value in degree zero. This avoids extending the unweighted
    product-decomposition formula beyond its positive-degree domain. *)
Theorem symmetric_degree_zero_mass_specification (x : symmetric_power V 0) :
  is_symmetric_mass hN x `|symmetric_zeroth_inverse V x|.
Proof.
constructor.
- move=> phi hp; rewrite symmetric_operator_degree_zero lee_fin in hp.
  rewrite symmetric_degree_zero_pairing.
  change (symmetric_zeroth_inverse V x * phi [tuple] <= `|symmetric_zeroth_inverse V x|).
  apply: le_trans (ler_norm _) _; rewrite normrM.
  have hh := ler_wpM2l (normr_ge0 (symmetric_zeroth_inverse V x)) hp.
  by rewrite mulr1 in hh.
- move=> eps he; have [phi [hp hv]] := symmetric_degree_zero_mass_attained x.
  exists phi; split=> //; rewrite hv ltrBlDl ltrDr; exact he.
Qed.
End DegreeZero.
