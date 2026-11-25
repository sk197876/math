(** Federer (1969), 1.9.3, p. 42: the k-nomial formula for symmetric powers.
    The proof below inducts on the number of variables using the binomial
    theorem and a proved multiindex decomposition Characteristic zero
    justifies factorial division. Degree zero and no variables are included
    as extensions of the printed positive-integer statement. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear AlgebraUP AlgebraPowers DividedBinomial
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds
  SymmetricIndexRecursion SymmetricIndexSummation SymmetricMonomials
  SymmetricDividedMonomials SymmetricMonomialFactors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Multinomial.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Local Notation A := (symmetric_algebra V).

(** Source for [symmetric_divided_binomial]: Federer 1.9.3,
    p. 42, the two-variable case of the displayed k-nomial
    formula, ordered by the exponent of its first vector. *)
Lemma symmetric_divided_binomial (v w : V) m :
  symmetric_divided_vector_power (v+w) m =
    \sum_(i < m.+1) symmetric_product (symmetric_divided_vector_power v i)
      (symmetric_divided_vector_power w (m-i)).
Proof.
rewrite /symmetric_divided_vector_power !symmetric_vector_powerE linearD addrC.
under eq_bigr do rewrite !symmetric_vector_powerE.
change (@divided_power K A (symmetric_generator w + symmetric_generator v) m =
  \sum_(i < m.+1) symmetric_product (@divided_power K A (symmetric_generator v) i)
    (@divided_power K A (symmetric_generator w) (m-i))).
rewrite (@divided_binomial K h0 A (@symmetric_product_commute K V)
  (symmetric_unit_nonzero V)).
apply: eq_bigr=> i _; exact: symmetric_product_commute.
Qed.

(** Source for [symmetric_multinomial_empty]: Federer 1.9.3,
    p. 42, supporting empty-variable boundary: both sides
    are the unit in degree zero and zero in positive degrees. *)
Lemma symmetric_multinomial_empty (v : 'I_0 -> V) m :
  symmetric_divided_vector_power (\sum_i v i) m =
    \sum_(a : symmetric_indices 0 m) symmetric_divided_monomial v (symmetric_indices_unbound a).
Proof.
rewrite big_ord0; case: m=> [|m].
- pose c : symmetric_index_code 0 0 := Sub tt erefl.
  pose a0 := symmetric_index_code_to_indices c.
  rewrite (big_pred1 a0); last first.
    move=> a; have ha : a = a0.
      apply: val_inj; apply/ffunP=> i; by case: i=> i.
    change (true = (a == a0)); by rewrite ha eqxx.
  by rewrite /symmetric_divided_vector_power /symmetric_vector_power
    /symmetric_divided_monomial /symmetric_multi_factorial
    /symmetric_monomial /symmetric_monomial_word enum_ord0 big_ord0 /= invr1 !scale1r.
- have hz : symmetric_divided_vector_power (0 : V) m.+1 = 0.
    by rewrite /symmetric_divided_vector_power /symmetric_vector_power
      symmetric_word_cons linear0 (bil0l (symmetric_product_bilinear V)) scaler0.
  rewrite hz; symmetry; apply: big1=> a _.
  have h := symmetric_indices_unbound_degree a.
  by rewrite /symmetric_multi_degree big_ord0 in h.
Qed.

(** Source for [symmetric_multinomial]: Federer 1.9.3,
    p. 42, the k-nomial theorem with all scalar coefficients
    equal to one. The divided power of the sum equals the sum
    of divided monomials over Xi(k,m). *)
Theorem symmetric_multinomial n (v : 'I_n -> V) m :
  symmetric_divided_vector_power (\sum_i v i) m =
    \sum_(a : symmetric_indices n m) symmetric_divided_monomial v (symmetric_indices_unbound a).
Proof.
elim: n m v => [m v|n ih m v]; first exact: symmetric_multinomial_empty.
rewrite big_ord_recl symmetric_divided_binomial symmetric_indices_sum_cons.
apply: eq_bigr=> i _; rewrite ih.
rewrite (big_morph (fun z => symmetric_product (symmetric_divided_vector_power (v ord0) i) z)
  (bilDr (symmetric_product_bilinear V) _) (bil0r (symmetric_product_bilinear V) _)).
apply: eq_bigr=> a _.
by rewrite symmetric_indices_cons_unbound symmetric_divided_monomial_cons.
Qed.

(** Source for [symmetric_weighted_multinomial]: Federer 1.9.3,
    p. 42, the full displayed formula (sum_i t_i v_i)^m/m!
    equals sum_alpha t^alpha v^alpha/alpha!. The indices range
    over Xi(k,m); zero degrees and zero variables are also valid. *)
Theorem symmetric_weighted_multinomial n (v : 'I_n -> V) (t : 'I_n -> K) m :
  symmetric_divided_vector_power (\sum_i t i *: v i) m =
    \sum_(a : symmetric_indices n m)
      symmetric_scalar_monomial t (symmetric_indices_unbound a) *:
        symmetric_divided_monomial v (symmetric_indices_unbound a).
Proof.
rewrite symmetric_multinomial; apply: eq_bigr=> a _.
exact: symmetric_divided_monomial_scale.
Qed.
End Multinomial.
