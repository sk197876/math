(** Federer (1969), 1.10.5, p. 48: for dual unit basic sequences, alpha! <=
    ||omega^alpha|| <= m! and alpha!/m! <= ||e^alpha|| <= 1. The upper unit
    hypotheses below may be inequalities: the proofs do not need their
    equality form. All degrees, including zero, are retained. Mass refers to
    the dual-supremum norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import LinearBasis SymmetricAlgebra SymmetricGrading SymmetricLowPowers
  SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials SymmetricForms
  SymmetricFormIsomorphism SymmetricPairing RealNormUP SymmetricOperatorNorm
  SymmetricMassUP SymmetricMass SymmetricMassTupleBound SymmetricDecompositionCosts
  SymmetricMassNormingForm SymmetricMonomialTuples SymmetricDualMonomialForm
  SymmetricOneFormUnitBound PolynomialWeightedNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable omega : 'I_n -> S_m V R^o 1.
Hypothesis hd : forall i j,
  symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) = if j==i then 1 else 0.
Hypothesis hv : forall i, N (e i)<=1.
Local Notation kappa := (symmetric_operator_norm (W:=R^o) (proj1 hN) (fun r:R=>`|r|)).
Hypothesis hw : forall i, (kappa (omega i)<=1)%E.
Variable m : nat.
Variable a : symmetric_indices n m.
Local Notation Phi := (symmetric_dual_monomial_form omega a).
Local Notation X := (symmetric_tuple_component (symmetric_monomial_tuple e a)).
Local Notation afac := ((symmetric_multi_factorial (symmetric_indices_unbound a))%:R : R).

(** Source for [symmetric_dual_monomial_norm_upper]: Federer
    1.10.5, p. 48, ||omega^alpha||<=m!. Repeating the
    one-forms according to alpha and applying the permutation bound
    gives m! summands, each of absolute value at most one. *)
Theorem symmetric_dual_monomial_norm_upper : (kappa Phi <= ((m`!)%:R:R)%:E)%E.
Proof.
rewrite symmetric_dual_monomial_as_product.
apply: symmetric_unit_one_form_product_bound=> i; exact: hw.
Qed.

(** Source for [symmetric_dual_monomial_norm_lower]: Federer
    1.10.5, p. 48, alpha!<=||omega^alpha||. Evaluate
    the form on the unit tuple representing e^alpha; the
    dual-coordinate formula gives alpha! exactly. *)
Theorem symmetric_dual_monomial_norm_lower : (afac%:E<=kappa Phi)%E.
Proof.
have ht := @symmetric_monomial_unit_tuple R V N n e hv m a.
have hh := symmetric_operator_norm_upper (W:=R^o) (proj1 hN) (fun r:R=>`|r|) Phi ht.
by rewrite (@symmetric_dual_monomial_diagonal R (@pchar_num R) V n e he omega hd m a)
  normr_nat in hh.
Qed.

(** Source for [symmetric_monomial_mass_upper]: Federer 1.10.5,
    p. 48, ||e^alpha||<=1. The monomial itself is a
    product of unit-ball vectors; degree zero is the empty product. *)
Theorem symmetric_monomial_mass_upper : symmetric_mass hN X<=1.
Proof.
apply: le_trans (symmetric_mass_tuple_bound hN (symmetric_monomial_tuple e a)) _.
apply: (@symmetric_unit_tuple_cost_bound R V N (proj1 hN) m (symmetric_monomial_tuple e a)).
exact (@symmetric_monomial_unit_tuple R V N n e hv m a).
Qed.

(** Source for [symmetric_monomial_mass_lower]: Federer 1.10.5,
    p. 48, alpha!/m!<=||e^alpha||. Dividing omega^alpha
    by m! yields an admissible covector for the mass supremum,
    whose value on e^alpha is the required lower bound. *)
Theorem symmetric_monomial_mass_lower : afac / (m`!)%:R <= symmetric_mass hN X.
Proof.
pose c : R := (m`!)%:R.
have hc : 0<c by rewrite /c ltr0n fact_gt0.
have hc0 : c!=0 by rewrite (gt_eqF hc).
pose psi := c^-1 *: Phi.
have hpsi : (kappa psi<=1)%E.
  apply: (proj2 (symmetric_operator_norm_bound (W:=R^o) (proj1 hN) (fun r:R=>`|r|) psi 1))=> t ht.
  rewrite /psi sform_scaleE normrM normfV (ger0_norm (ltW hc)).
  have hb := proj1 (symmetric_operator_norm_bound (W:=R^o) (proj1 hN)
    (fun r:R=>`|r|) Phi c) symmetric_dual_monomial_norm_upper t ht.
  have hci : 0<=c^-1 by rewrite invr_ge0; exact: ltW hc.
  have hh := ler_wpM2l hci hb.
  by rewrite (mulVf hc0) in hh.
have hh := @symmetric_mass_upper_law R V N (proj1 hN) m X _ (symmetric_massP hN X) psi hpsi.
rewrite symmetric_pairing_tuple /psi sform_scaleE
  (@symmetric_dual_monomial_diagonal R (@pchar_num R) V n e he omega hd m a) in hh.
change (is_true (c^-1 * afac <= symmetric_mass hN X)) in hh.
by rewrite mulrC in hh.
Qed.
End Bounds.
