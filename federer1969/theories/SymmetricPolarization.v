(** Federer (1969), 1.9.3, p. 43: the polarization formula. The proof
    follows the printed multinomial expansion and cancellation of all
    exponent tuples except the all-ones tuple. Characteristic zero replaces
    the sources' real scalar field. Degree zero is included as an
    empty-product extension. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricAlgebra SymmetricMultiIndices SymmetricIndexBounds
  SymmetricDividedMonomials SymmetricMultinomial SymmetricPolarizationCoefficients
  SymmetricPolarizationIndex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Polarization.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.

(** Source for [polarization_sign_weight]: Federer 1.9.3,
    p. 43, the factor product_i t_i multiplying the divided
    power at each of the sign choices in T. *)
Definition polarization_sign_weight m (t : polarization_signs m) : K :=
  \prod_(i < m) polarization_sign K (t i).

(** Source for [polarization_weight_monomial]: Federer 1.9.3,
    p. 43, supporting multiplication of scalar factors: the
    sign weight times t^alpha is product_i t_i^(1+alpha_i). *)
Lemma polarization_weight_monomial m (t : polarization_signs m) (a : symmetric_multi_index m) :
  polarization_sign_weight t * symmetric_scalar_monomial (fun i => polarization_sign K (t i)) a =
    \prod_(i < m) (polarization_sign K (t i)) ^+ (1 + a i).
Proof.
rewrite /polarization_sign_weight /symmetric_scalar_monomial -big_split.
apply: eq_bigr=> i _; by rewrite add1n exprS.
Qed.

(** Source for [symmetric_polarization_expansion]: Federer
    1.9.3, p. 43, the displayed intermediate sum: interchange
    the sign sum with the multinomial sum and collect the bracketed
    coefficient for each exponent tuple. *)
Lemma symmetric_polarization_expansion m (v : 'I_m -> V) :
  \sum_(t : polarization_signs m) polarization_sign_weight t *:
    symmetric_divided_vector_power (\sum_i (polarization_sign K (t i)) *: v i) m =
  \sum_(a : symmetric_indices m m) polarization_coefficient K (symmetric_indices_unbound a) *:
    symmetric_divided_monomial v (symmetric_indices_unbound a).
Proof.
under eq_bigr do rewrite (symmetric_weighted_multinomial h0) scaler_sumr.
rewrite exchange_big; apply: eq_bigr=> a _.
rewrite /polarization_coefficient scaler_suml.
apply: eq_bigr=> t _.
by rewrite scalerA polarization_weight_monomial.
Qed.

(** Source for [symmetric_polarization_formula]: Federer
    1.9.3, p. 43, the displayed polarization identity: summing
    product_i t_i times (sum_i t_i v_i)^m/m! over all signs
    gives 2^m times v_1 ... v_m. *)
Theorem symmetric_polarization_formula m (v : 'I_m -> V) :
  \sum_(t : polarization_signs m) polarization_sign_weight t *:
    symmetric_divided_vector_power (\sum_i (polarization_sign K (t i)) *: v i) m =
  (2%:R : K)^+m *: symmetric_word [seq v i | i <- enum 'I_m].
Proof.
rewrite symmetric_polarization_expansion.
under eq_bigr do rewrite
  (polarization_balanced_coefficient K (symmetric_indices_unbound_degree _))
  polarization_one_index_test.
rewrite (bigD1 (polarization_one_index m)) //= eqxx
  polarization_one_indexE symmetric_divided_monomial_one.
have hz : (\sum_(a : symmetric_indices m m | a != polarization_one_index m)
    (if a == polarization_one_index m then (2%:R : K)^+m else 0) *:
      symmetric_divided_monomial v (symmetric_indices_unbound a)) = 0.
  apply: big1=> a ha; by rewrite (negbTE ha) scale0r.
by rewrite hz addr0.
Qed.
End Polarization.
