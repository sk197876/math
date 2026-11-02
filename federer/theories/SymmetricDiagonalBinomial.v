(** Federer (1969), 1.9.4, p. 43: the ordinary monomial diagonal formula
    with products of binomial coefficients. The proof multiplies the divided
    formula by alpha!; characteristic zero is sufficient for the book's real
    field. The one-variable formula was proved separately over arbitrary
    fields. Local printing correction: Federer's ordinary monomial display
    ends the binomial-coefficient product at alpha_m,beta_m, although the
    multiindices have n coordinates. The product must run over n
    coordinates. There is no p. 43 entry in the saved Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded SymmetricAlgebra SymmetricDirectSum SymmetricDiagonal
  SymmetricMultiIndices SymmetricIndexBounds SymmetricExponentBox SymmetricBoxFibres
  SymmetricBoxSums SymmetricMonomials SymmetricDividedMonomials SymmetricMultiBinomial
  SymmetricDiagonalMonomials.
From Federer Require Import UnitalGradedTensor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Binomial.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation T := (unital_graded_tensor E E false).
Local Notation D := (symmetric_diagonal V).

(** Source for [symmetric_diagonal_monomial_box]: Federer
    1.9.4, p. 43, the ordinary monomial diagonal formula,
    with one term for each coordinatewise exponent choice beta<=alpha. *)
Lemma symmetric_diagonal_monomial_box n (e : 'I_n -> V) (a : symmetric_multi_index n) :
  D (symmetric_monomial e a) =
    \sum_(c : symmetric_exponent_box a)
      ((symmetric_multi_binomial a (symmetric_exponent_box_index a c))%:R : K) *:
        tensor_inj (symmetric_monomial e (symmetric_exponent_box_index a c))
          (symmetric_monomial e (symmetric_multi_difference a (symmetric_exponent_box_index a c))).
Proof.
have h := congr1 (fun z : T => ((symmetric_multi_factorial a)%:R : K) *: z)
  (symmetric_diagonal_divided_monomial_box h0 e a).
have ha := @symmetric_multi_factorial_nonzero K h0 n a.
rewrite /symmetric_divided_monomial linearZ scalerA mulfV // scale1r scaler_sumr in h.
rewrite h; apply: eq_bigr=> c _.
rewrite /symmetric_diagonal_monomial_term /symmetric_divided_monomial
  tensor_inj_scalel tensor_inj_scaler !scalerA.
congr (_ *: _); rewrite mulrA.
exact: (@symmetric_multi_binomial_cancel K h0 n a
  (symmetric_exponent_box_index a c) (symmetric_exponent_box_bound c)).
Qed.

(** Source for [symmetric_diagonal_monomial]: Federer 1.9.4,
    p. 43, the displayed ordinary formula: for each total
    degree p and beta in Xi(n,p) with beta<=alpha, the coefficient
    of e^beta tensor e^(alpha-beta) is product_i binomial(alpha_i,beta_i).
    The statement holds for any vector family, including a basis. *)
Theorem symmetric_diagonal_monomial n (e : 'I_n -> V) (a : symmetric_multi_index n) :
  D (symmetric_monomial e a) =
    \sum_(p < (symmetric_multi_degree a).+1)
      \sum_(b : symmetric_indices n p | symmetric_subindex a b)
        ((symmetric_multi_binomial a (symmetric_indices_unbound b))%:R : K) *:
          tensor_inj (symmetric_monomial e (symmetric_indices_unbound b))
            (symmetric_monomial e (symmetric_multi_difference a (symmetric_indices_unbound b))).
Proof.
rewrite symmetric_diagonal_monomial_box.
exact: (@symmetric_box_sum_by_degree (GRing.Zmodule.clone T _) n a
  (fun b => ((symmetric_multi_binomial a b)%:R : K) *:
    tensor_inj (symmetric_monomial e b)
      (symmetric_monomial e (symmetric_multi_difference a b)))).
Qed.
End Binomial.
