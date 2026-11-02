(** Federer (1969), 1.10.5, p. 48, mass estimates from the decomposition
    infimum. Supporting maximality: a seminorm bounded on products is
    bounded on every symmetric vector by the same multiple of the mass
    infimum. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP RealSeminormOperations SymmetricAlgebra
  SymmetricGrading SymmetricFormIsomorphism SymmetricDecompositions
  SymmetricDecompositionCosts SymmetricProjectiveMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Maximality.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variable m : nat.
Variable hm : (0<m)%N.
Variable Q : symmetric_power V m -> R.
Hypothesis hQ : is_real_seminorm Q.
Variable C : R.
Hypothesis hC : 0 <= C.
Hypothesis hword : forall t : m.-tuple V, Q (symmetric_tuple_component t) <= C * symmetric_tuple_cost N t.

(** Source for [symmetric_seminorm_decomposition_bound]: Federer
    1.10.5, p. 48, supporting extension of a product bound to
    each finite decomposition by the seminorm triangle inequality. *)
Lemma symmetric_seminorm_decomposition_bound x s :
  symmetric_decomposition x s -> Q x <= C * symmetric_decomposition_cost N s.
Proof.
rewrite /symmetric_decomposition=> ->.
apply: le_trans (real_seminorm_sequence_sum hQ _ _) _.
rewrite /symmetric_decomposition_cost mulr_sumr; apply: ler_sum=> t _; exact: hword.
Qed.

(** Source for [symmetric_projective_mass_maximal]: Federer 1.10.5, p. 48,
    supporting consequence of the infimum formula. Every seminorm bounded by
    C times the factor-length product on generators is bounded by C times
    the projective mass everywhere. *)
Theorem symmetric_projective_mass_maximal x : Q x <= C * symmetric_projective_mass hN hm x.
Proof.
case: (eqVneq C 0)=> [h0|hne].
- have [s hs] := symmetric_decomposition_exists hm x.
  have hh := symmetric_seminorm_decomposition_bound hs.
  by rewrite h0 !mul0r in hh *.
have hp : 0 < C by rewrite lt_def hne hC.
rewrite mulrC -(ler_pdivrMr _ _ hp).
apply: symmetric_projective_mass_greatest=> s hs.
rewrite (ler_pdivrMr _ _ hp) mulrC.
exact: symmetric_seminorm_decomposition_bound hs.
Qed.
End Maximality.
