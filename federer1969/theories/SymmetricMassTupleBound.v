(** Federer (1969), 1.10.5, p. 48: a decomposable symmetric vector has mass
    at most the product of its factor lengths. Source context:
    SymmetricMass.v. The degree-zero extension is the scalar identity one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SymmetricAlgebra SymmetricGrading SymmetricLowPowers
  SymmetricFormIsomorphism SymmetricDegreeZeroPairing RealNormUP SymmetricDecompositionCosts
  SymmetricProjectiveMass SymmetricMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_mass_tuple_bound]: Federer 1.10.5,
    p. 48, supporting mass estimate for a single product.
    This form includes the empty product in degree zero. *)
Lemma symmetric_mass_tuple_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) m (t : m.-tuple V) :
  symmetric_mass hN (symmetric_tuple_component t) <= symmetric_tuple_cost N t.
Proof.
case: m t=> [t|m t].
- have he : symmetric_zeroth_inclusion V (1:R) =
      symmetric_tuple_component ([tuple] : 0.-tuple V).
    by rewrite symmetric_zeroth_tuple_scalar scale1r.
  by rewrite (tuple0 t) -he symmetric_mass_degree_zero symmetric_zeroth_inclusionK
    normr1 /symmetric_tuple_cost big_ord0.
- rewrite (@symmetric_mass_positive_degree R V N hN m.+1 (ltn0Sn m)).
  exact: symmetric_projective_mass_tuple_bound.
Qed.
