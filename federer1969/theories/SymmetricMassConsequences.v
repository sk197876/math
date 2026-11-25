(** Federer (1969), 1.10.5, p. 48: pure-power mass, norming covectors, and
    optimal decompositions for the public dual-supremum interface. The
    public statements follow by uniqueness of the mass specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import LinearBasis SymmetricAlgebra SymmetricGrading SymmetricDimension
  SymmetricFormIsomorphism SymmetricForms SymmetricPairing RealNormUP SymmetricOperatorNorm
  SymmetricMass SymmetricMassNormingForm SymmetricDegreeZeroMass SymmetricFunctionalMassBound
  SymmetricDecompositionCosts SymmetricOptimalDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_mass_pure_power]: Federer 1.10.5,
    p. 48, the displayed identity ||x^k||=|x|^k for positive k.
    The ambient normed vector space may have arbitrary dimension. *)
Theorem symmetric_mass_pure_power (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) m (hm : (0<m)%N) x :
  symmetric_mass hN (symmetric_tuple_component [tuple x | i<m]) = (N x)^+m.
Proof.
rewrite (@symmetric_mass_positive_degree R V N hN m hm).
exact: symmetric_projective_mass_pure_power.
Qed.

(** Source for [symmetric_mass_attaining_covector]: Federer
    1.10.5, p. 48, supporting attainment of the dual supremum.
    Hahn-Banach supplies a covector of operator norm at most one
    whose pairing is the mass, in every degree and arbitrary dimension. *)
Theorem symmetric_mass_attaining_covector (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) m (x : symmetric_power V m) :
  exists phi : S_m V R^o m,
    (symmetric_operator_norm (W:=R^o) (proj1 hN) (fun r:R=>(`|r|)%R) phi<=1)%E /\
    symmetric_pairing x phi = symmetric_mass hN x.
Proof.
case: m x=> [x|m x].
- rewrite symmetric_mass_degree_zero; exact: symmetric_degree_zero_mass_attained.
- rewrite (@symmetric_mass_positive_degree R V N hN m.+1 (ltn0Sn m)).
  exact: symmetric_mass_norming_form.
Qed.

(** Source for [symmetric_mass_optimal_decomposition]: Federer
    1.10.5, p. 48, the finite-dimensional minimum and bound
    on the number of summands, for the public mass operation.
    Positive degree is explicit, as required by the unweighted
    decomposition formula. *)
Theorem symmetric_mass_optimal_decomposition (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V) (he : is_basis e)
    m (hm : (0<m)%N) (x : symmetric_power V m) :
  exists k, exists t : 'I_k -> m.-tuple V,
    (k <= dim (finite_symmetric_power he m))%N /\
    x = \sum_i symmetric_tuple_component (t i) /\
    symmetric_mass hN x = \sum_i symmetric_tuple_cost N (t i).
Proof.
rewrite (@symmetric_mass_positive_degree R V N hN m hm).
exact: symmetric_optimal_product_decomposition.
Qed.
