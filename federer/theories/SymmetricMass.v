(** Federer (1969), 1.10.5, p. 48: public mass defined by the sealed dual
    supremum, and its identification with the decomposition infimum in
    positive degree. The original norm is abstract, and the ambient
    dimension is unrestricted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP RealSeminormOperations SymmetricAlgebra
  SymmetricGrading SymmetricLowPowers SymmetricMassUP SymmetricMassSealed
  SymmetricProjectiveMass SymmetricMassDuality SymmetricDegreeZeroMass
  SymmetricMassPositivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Mass.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.

(** Source for [symmetric_mass]: Federer 1.10.5, p. 48,
    the mass of a symmetric vector, specified by the dual supremum.
    The definition exposes no decomposition or auxiliary basis. *)
Definition symmetric_mass m (x : symmetric_power V m) :=
  @SymmetricMass.value R V N hN m x.

(** Source for [symmetric_massP]: Federer 1.10.5, p. 48,
    the public operation satisfies the abstract mass specification. *)
Lemma symmetric_massP m (x : symmetric_power V m) :
  is_symmetric_mass (proj1 hN) x (symmetric_mass x).
Proof. exact: SymmetricMass.laws. Qed.

(** Source for [symmetric_mass_positive_degree]: Federer 1.10.5,
    p. 48, equality of the dual supremum with the unweighted
    finite-decomposition infimum, for positive degree. *)
Theorem symmetric_mass_positive_degree m (hm : (0<m)%N) (x : symmetric_power V m) :
  symmetric_mass x = symmetric_projective_mass (proj1 hN) hm x.
Proof.
exact (@symmetric_mass_unique R V N (proj1 hN) m x _ _ (symmetric_massP x)
  (@symmetric_mass_infimum_duality R V N hN m hm x)).
Qed.

(** Source for [symmetric_mass_degree_zero]: Federer 1.10.5,
    p. 48, scalar mass equals absolute value under the degree-zero
    identification of 1.9.1, p. 41. *)
Theorem symmetric_mass_degree_zero (x : symmetric_power V 0) :
  symmetric_mass x = `|symmetric_zeroth_inverse V x|.
Proof.
exact (@symmetric_mass_unique R V N (proj1 hN) 0 x _ _ (symmetric_massP x)
  (symmetric_degree_zero_mass_specification (proj1 hN) x)).
Qed.

(** Source for [symmetric_mass_norm]: Federer 1.10.5,
    p. 48, mass is a norm in every degree, with no dimension
    restriction. Its norm laws are derived from the supremum
    specification and the proved identifications, not from its implementation. *)
Theorem symmetric_mass_norm m : is_real_norm (@symmetric_mass m).
Proof.
case: m=> [|m].
- have he : @symmetric_mass 0 = (fun x => `|symmetric_zeroth_inverse V x|).
    apply: funext=> x; exact: symmetric_mass_degree_zero.
  rewrite he; exact (@real_norm_injective_precompose R (symmetric_power V 0) R^o
    (fun r:R=>`|r|) (scalar_absolute_value_norm R) (symmetric_zeroth_inverse V)
    (can_inj (@symmetric_zeroth_inverseK R V))).
- have he : @symmetric_mass m.+1 = symmetric_projective_mass (proj1 hN) (ltn0Sn m).
    apply: funext=> x; exact: symmetric_mass_positive_degree.
  rewrite he; exact: symmetric_projective_mass_norm.
Qed.

(** Source for [symmetric_mass_nonnegative]: Federer 1.10.5,
    p. 48, mass is nonnegative. *)
Lemma symmetric_mass_nonnegative m (x : symmetric_power V m) : 0 <= symmetric_mass x.
Proof. exact: real_seminorm_nonnegative (proj1 (symmetric_mass_norm m)) x. Qed.

(** Source for [symmetric_mass_zero]: Federer 1.10.5,
    p. 48, the zero symmetric vector has mass zero. *)
Lemma symmetric_mass_zero m : symmetric_mass (0 : symmetric_power V m)=0.
Proof. exact: real_seminorm_zero (proj1 (symmetric_mass_norm m)). Qed.

(** Source for [symmetric_mass_scale]: Federer 1.10.5,
    p. 48, mass is absolutely homogeneous under scalar multiplication. *)
Lemma symmetric_mass_scale m c (x : symmetric_power V m) :
  symmetric_mass (c*:x) = `|c| * symmetric_mass x.
Proof. exact: real_seminorm_scale (proj1 (symmetric_mass_norm m)) c x. Qed.

(** Source for [symmetric_mass_triangle]: Federer 1.10.5,
    p. 48, mass satisfies the triangle inequality. *)
Lemma symmetric_mass_triangle m (x y : symmetric_power V m) :
  symmetric_mass (x+y) <= symmetric_mass x + symmetric_mass y.
Proof. exact: real_seminorm_triangle (proj1 (symmetric_mass_norm m)) x y. Qed.

(** Source for [symmetric_mass_positive]: Federer 1.10.5,
    p. 48, mass is strictly positive precisely on nonzero vectors. *)
Lemma symmetric_mass_positive m (x : symmetric_power V m) :
  (0 < symmetric_mass x) = (x != 0).
Proof. exact (@real_norm_positive R (symmetric_power V m) (@symmetric_mass m)
  (proj1 (symmetric_mass_norm m)) (proj2 (symmetric_mass_norm m)) x). Qed.
End Mass.
