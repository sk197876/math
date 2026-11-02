(** Federer (1969), 1.10.5, p. 48, final equality in the weighted polynomial
    estimate. The scalar multinomial identity is obtained from 1.9.3, p. 42,
    by evaluating the symmetric algebra in the scalar algebra. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP AlgebraUP ScalarCoefficients SymmetricAlgebra
  SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials
  SymmetricDividedMonomials SymmetricMultinomial SymmetricFunctionalProduct
  SymmetricMonomialTuples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarEvaluation.
Variable K : fieldType.
Local Notation F := (symmetric_functional_extension (linear_id K^o)).

(** Source for [scalar_identity_symmetric_word]: Federer 1.10.5,
    p. 48, supporting scalar evaluation of the multinomial
    formula: the product of scalar generators evaluates to their product. *)
Lemma scalar_identity_symmetric_word (s : seq K^o) :
  F (symmetric_word s) = \prod_(x <- s) x.
Proof.
rewrite /symmetric_functional_extension symmetric_algebra_extension_word
  scalar_functional_word_product; by [].
Qed.

(** Source for [scalar_identity_symmetric_divided_power]: Federer
    1.10.5, p. 48, supporting evaluation of the left side
    of the scalar multinomial formula, including degree zero. *)
Lemma scalar_identity_symmetric_divided_power (x : K^o) m :
  F (symmetric_divided_vector_power x m) = x^+m / (m`!)%:R.
Proof.
rewrite /symmetric_divided_vector_power linearZ /symmetric_vector_power
  scalar_identity_symmetric_word.
have hp : \prod_(y <- nseq m x) y = x^+m.
  by elim: m=> [|m ih]; rewrite ?big_nil ?big_cons ?expr0 ?exprS ?ih.
change ((m`!%:R : K)^-1 * (\prod_(y <- nseq m x) y) = x^+m / (m`!)%:R).
by rewrite hp mulrC.
Qed.

(** Source for [scalar_identity_symmetric_unit_monomial]: Federer
    1.10.5, p. 48, supporting evaluation of a monomial
    whose factors are all the scalar one. Its divided value is 1/alpha!. *)
Lemma scalar_identity_symmetric_unit_monomial n (a : symmetric_multi_index n) :
  F (symmetric_divided_monomial (fun _ : 'I_n => (1:K^o)) a) =
    (symmetric_multi_factorial a)%:R^-1.
Proof.
rewrite /symmetric_divided_monomial linearZ /symmetric_monomial scalar_identity_symmetric_word.
have hp : \prod_(x <- symmetric_monomial_word (fun _ : 'I_n => (1:K^o)) a) x = 1.
  apply: big1_seq=> x hx; have [i ->] := symmetric_monomial_word_member hx; by [].
change ((symmetric_multi_factorial a)%:R^-1 *
  (\prod_(x <- symmetric_monomial_word (fun _ : 'I_n => (1:K^o)) a) x) =
  (symmetric_multi_factorial a)%:R^-1).
by rewrite hp mulr1.
Qed.

(** Source for [scalar_divided_multinomial]: Federer 1.10.5,
    p. 48, the final equality: the sum of t^alpha/alpha!
    over degree-m multiindices equals (sum t_i)^m/m!. No sign
    or nonnegativity hypothesis is required for this scalar identity. *)
Theorem scalar_divided_multinomial (h0 : [pchar K] =i pred0) n (t : 'I_n -> K) m :
  \sum_(a : symmetric_indices n m)
    symmetric_scalar_monomial t (symmetric_indices_unbound a) /
      (symmetric_multi_factorial (symmetric_indices_unbound a))%:R =
    (\sum_i t i)^+m / (m`!)%:R.
Proof.
have hh := congr1 F (@symmetric_weighted_multinomial K h0 K^o n
  (fun _ => 1) t m).
have he : (\sum_i t i *: (1:K^o)) = (\sum_i t i : K^o).
  apply: eq_bigr=> i _; exact: mulr1.
rewrite he scalar_identity_symmetric_divided_power linear_sum in hh.
rewrite hh; apply: eq_bigr=> a _.
by rewrite linearZ scalar_identity_symmetric_unit_monomial.
Qed.
End ScalarEvaluation.

(** Source for [scalar_divided_multinomial_absolute]: Federer
    1.10.5, p. 48, the final equality with absolute
    coefficients: sum |t^alpha/alpha!| = (sum |t_i|)^m/m!. *)
Theorem scalar_divided_multinomial_absolute (R : realFieldType) n (t : 'I_n -> R) m :
  \sum_(a : symmetric_indices n m)
    `|symmetric_scalar_monomial t (symmetric_indices_unbound a) /
      (symmetric_multi_factorial (symmetric_indices_unbound a))%:R| =
    (\sum_i `|t i|)^+m / (m`!)%:R.
Proof.
rewrite -(@scalar_divided_multinomial R (@pchar_num R) n (fun i => `|t i|) m).
apply: eq_bigr=> a _; rewrite normrM normfV normr_nat.
congr (_ * _); rewrite /symmetric_scalar_monomial normr_prod.
apply: eq_bigr=> i _; exact: normrX.
Qed.
