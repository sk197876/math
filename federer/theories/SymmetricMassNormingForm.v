(** Federer (1969), 1.10.5, p. 48, equality of the decomposition infimum and
    dual supremum. Hahn-Banach, proved locally from Federer 2.4.12, supplies
    a norming functional for the infimum seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import Hom RealNormUP SeminormNormingFunctional
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormIsomorphism
  SymmetricPairing SymmetricDecompositionCosts SymmetricProjectiveMass
  SymmetricProjectiveSeminorm SymmetricOperatorNormUP SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section NormingForm.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Local Notation abs := (fun r : R => `|r|).

(** Source for [symmetric_unit_tuple_cost_bound]: Federer 1.10.5,
    pp. 47-48, supporting comparison of the unit-tuple constraint
    with decomposition cost. The product of nonnegative lengths at most
    one is at most one, including the empty product. *)
Lemma symmetric_unit_tuple_cost_bound m (t : m.-tuple V) :
  symmetric_form_unit_tuple N t -> symmetric_tuple_cost N t <= 1.
Proof.
move=> ht; have he : (\prod_(i < m) (1:R)) = 1 by rewrite prodr_const expr1n.
rewrite /symmetric_tuple_cost -[X in _ <= X]he.
apply: ler_prod=> i _; apply/andP; split.
- exact: real_seminorm_nonnegative hN (tnth t i).
- exact: ht.
Qed.

(** Source for [symmetric_mass_norming_form]: Federer 1.10.5, p. 48, the
    dual supremum reaches the decomposition infimum. For each
    positive-degree vector, a symmetric scalar form of norm at most one
    takes exactly its infimum mass as its value. *)
Theorem symmetric_mass_norming_form m (hm : (0<m)%N) (x : symmetric_power V m) :
  exists phi : S_m V R^o m,
    (symmetric_operator_norm (W:=R^o) hN abs phi <= 1)%E /\
    symmetric_pairing x phi = symmetric_projective_mass hN hm x.
Proof.
have hM := @symmetric_projective_mass_seminorm R V N hN m hm.
have [f [hf hfx]] := @seminorm_norming_functional R (symmetric_power V m)
  (symmetric_projective_mass hN hm) hM x.
pose phi := hom_to_sform (hom_of_linear f).
exists phi; split.
- apply: (proj2 (symmetric_operator_norm_bound (W:=R^o) hN abs phi 1))=> t ht.
  rewrite /phi hom_to_sformE hom_of_linearE.
  apply: le_trans (hf _) _.
  apply: le_trans (symmetric_projective_mass_tuple_bound hN hm t) _.
  exact: symmetric_unit_tuple_cost_bound ht.
- by rewrite /phi /symmetric_pairing hom_to_sformK hom_of_linearE.
Qed.
End NormingForm.
