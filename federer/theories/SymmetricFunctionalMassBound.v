(** Federer (1969), 1.10.5, p. 48, the pure-power mass identity. A dominated
    functional on V gives a product functional dominated by every
    decomposition cost. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SeminormNormingFunctional
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormIsomorphism
  SymmetricPairing SymmetricDecompositions SymmetricDecompositionCosts
  SymmetricProjectiveMass SymmetricFunctionalProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FunctionalBound.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variable f : {linear V -> R^o}.
Hypothesis hf : forall x, `|f x| <= N x.

(** Source for [symmetric_functional_product_cost_bound]: Federer
    1.10.5, p. 48, supporting domination of the product functional
    by each finite-decomposition cost. This works for an input seminorm. *)
Lemma symmetric_functional_product_cost_bound m (x : symmetric_power V m) s :
  symmetric_decomposition x s ->
  `|symmetric_functional_product_hom f m x| <= symmetric_decomposition_cost N s.
Proof.
rewrite /symmetric_decomposition=> hx; rewrite hx linear_sum.
change (`|\sum_(t <- s) symmetric_functional_product_hom f m (symmetric_tuple_component t)| <=
  \sum_(t <- s) symmetric_tuple_cost N t).
under eq_bigr do rewrite -symmetric_functional_product_pairing symmetric_pairing_tuple
  symmetric_functional_product_formE.
apply: le_trans (ler_norm_sum _ _ _) _; apply: ler_sum=> t _.
rewrite normr_prod; apply: ler_prod=> i _; apply/andP; split; first exact: normr_ge0.
exact: hf.
Qed.

(** Source for [symmetric_functional_product_mass_bound]: Federer
    1.10.5, p. 48, the product functional is bounded by the
    mass infimum because it is bounded by every decomposition cost. *)
Lemma symmetric_functional_product_mass_bound m (hm : (0<m)%N) (x : symmetric_power V m) :
  `|symmetric_functional_product_hom f m x| <= symmetric_projective_mass hN hm x.
Proof.
apply: symmetric_projective_mass_greatest=> s hs.
exact: symmetric_functional_product_cost_bound hs.
Qed.
End FunctionalBound.

(** Source for [symmetric_projective_mass_pure_power]: Federer 1.10.5, p.
    48, the displayed identity for the mass of x to the m-th power: it
    equals the m-th power of the norm of x. positive degree and arbitrary
    dimension are retained. *)
Theorem symmetric_projective_mass_pure_power (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) m (hm : (0<m)%N) (x : V) :
  symmetric_projective_mass hN hm (symmetric_tuple_component [tuple x | i < m]) = (N x)^+m.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hh := symmetric_projective_mass_tuple_bound hN hm [tuple x | i < m].
  rewrite /symmetric_tuple_cost in hh.
  have he : (\prod_(i < m) N (tnth [tuple x | j < m] i)) = (N x)^+m.
    under eq_bigr do rewrite tnth_mktuple.
    by rewrite prodr_const card_ord.
  by rewrite he in hh.
- have [f [hf hv]] := seminorm_norming_functional hN x.
  have hh := @symmetric_functional_product_mass_bound R V N hN f hf m hm
    (symmetric_tuple_component [tuple x | i < m]).
  rewrite -symmetric_functional_product_pairing symmetric_functional_product_diagonal hv
    normrX (ger0_norm (real_seminorm_nonnegative hN x)) in hh.
  exact hh.
Qed.
