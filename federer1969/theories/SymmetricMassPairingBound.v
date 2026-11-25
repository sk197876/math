(** Federer (1969), 1.10.5, p. 48: comparison of the dual supremum with
    decomposition costs. Here the input is a normed space, as in Federer's
    statement. The auxiliary infimum remains defined for input seminorms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import Hom GradedComponents RealNormUP SymmetricAlgebra
  SymmetricGrading SymmetricForms SymmetricFormIsomorphism SymmetricPairing
  SymmetricDecompositions SymmetricDecompositionCosts SymmetricProjectiveMass
  SymmetricOperatorNormUP SymmetricOperatorNorm SymmetricOperatorTupleBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DualBound.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation hS := (proj1 hN).
Local Notation abs := (fun r : R => `|r|).

(** Source for [symmetric_unit_covector_tuple_bound]: Federer
    1.10.5, pp. 47-48, supporting evaluation bound: a scalar form
    of operator norm at most one evaluates a product to at most the
    product of its factor lengths in absolute value. *)
Lemma symmetric_unit_covector_tuple_bound m (f : S_m V R^o m) :
  (symmetric_operator_norm (W:=R^o) hS abs f <= 1)%E -> forall (t : m.-tuple V),
  `|f t| <= symmetric_tuple_cost N t.
Proof.
move=> hf t.
have hh := @symmetric_operator_finite_tuple_bound R V R^o N abs hN
  (proj1 (scalar_absolute_value_norm R)) m f 1 hf t.
by rewrite mul1r in hh.
Qed.

(** Source for [symmetric_unit_covector_decomposition_bound]: Federer
    1.10.5, p. 48, every unit-norm covector is bounded by every
    decomposition cost, by linearity and the scalar triangle inequality. *)
Lemma symmetric_unit_covector_decomposition_bound m (f : S_m V R^o m)
    (x : symmetric_power V m) s :
  (symmetric_operator_norm (W:=R^o) hS abs f <= 1)%E -> symmetric_decomposition x s ->
  `|symmetric_pairing x f| <= symmetric_decomposition_cost N s.
Proof.
move=> hf hx; rewrite /symmetric_decomposition in hx.
rewrite hx /symmetric_pairing linear_sum.
change (`|\sum_(t <- s) sform_to_hom f (symmetric_tuple_component t)| <=
  \sum_(t <- s) symmetric_tuple_cost N t).
under eq_bigr do rewrite sform_to_hom_tuple.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: ler_sum=> t _; exact: symmetric_unit_covector_tuple_bound hf t.
Qed.

(** Source for [symmetric_unit_covector_mass_bound]: Federer 1.10.5,
    p. 48, the dual supremum is at most the finite-decomposition
    infimum. The absolute-value form also controls negative evaluations. *)
Theorem symmetric_unit_covector_mass_bound m (hm : (0<m)%N)
    (f : S_m V R^o m) (x : symmetric_power V m) :
  (symmetric_operator_norm (W:=R^o) hS abs f <= 1)%E ->
  `|symmetric_pairing x f| <= symmetric_projective_mass hS hm x.
Proof.
move=> hf; apply: symmetric_projective_mass_greatest=> s hs.
exact: symmetric_unit_covector_decomposition_bound hf hs.
Qed.
End DualBound.
