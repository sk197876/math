(** Federer (1969), 1.8.2, p. 40: the ordered product of
    paired one-form blocks is the interleaved volume covector.
    Its two-block representation carries the sign (-1)^(k choose 2),
    as in 1.6.6, p. 27. *)
From mathcomp Require Import all_boot all_order all_algebra binomial.
From Federer Require Import BoundedHom HomogeneousHom AlgebraUP Bilinear GradedAlgebra AlternatingForms
  AlternatingSum AlternatingProduct AlternatingUnit ScalarCoefficients
  OneFormProducts WordEvaluation FormWordOperations PairedGradedWords ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation A := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation mul := (alg_mul A).
Variable k : nat.
Variables alpha beta : 'I_k -> A_m V K^o 1.

(** Source for [paired_form_product_word]: Federer 1.8.2,
    p. 40, multiplying paired blocks is the ordered interleaved
    one-form word alpha_1,beta_1,...,alpha_k,beta_k. *)
Lemma paired_form_product_word (s : seq 'I_k) :
  foldr mul (alg_one A)
    [seq form_include (form_wedge h2 (scalar_bilinear K) (alpha j) (beta j)) | j <- s] =
  @one_form_algebra_word K h2 V (scalar_algebra K) (flatten [seq [:: alpha j; beta j] | j <- s]).
Proof.
elim: s => [|j s ih] //=.
rewrite ih /one_form_algebra_word.
set w := @word_eval K (Choice.clone (A_m V K^o 1) _) A
  (@form_include K V K^o 1) (flatten [seq [:: alpha i; beta i] | i <- s]).
change (mul (form_include (form_wedge h2 (scalar_bilinear K) (alpha j) (beta j))) w =
  mul (form_include (alpha j)) (mul (form_include (beta j)) w)).
by rewrite form_wedge_include alg_assoc.
Qed.

(** Source for [paired_form_product_two_blocks]: Federer 1.8.2,
    p. 40, identifying the interleaved volume covector with the
    two-block product and its permutation sign from 1.6.6, p. 27. *)
Lemma paired_form_product_two_blocks :
  foldr mul (alg_one A)
    [seq form_include (form_wedge h2 (scalar_bilinear K) (alpha j) (beta j)) | j <- enum 'I_k] =
  (-1 : K)^+'C(k,2) *:
    form_include (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o)
      (concatenate_family alpha beta)).
Proof.
rewrite paired_form_product_word.
have h := @paired_word_interleaving_sign K A (A_star_grading V K^o)
  (@alternating_wedge_graded K h2 V K^o _ (scalar_bilinear K))
  (@coefficient_form_homogeneous K V K^o 1)
  (@alternating_wedge_anticommutative K h2 V K^o _ (scalar_bilinear K) (@mulrC K))
  (Choice.clone (A_m V K^o 1) _) (@form_include K V K^o 1)
  (@form_include_homogeneous K V K^o 1) (Choice.clone 'I_k _) alpha beta (enum 'I_k).
rewrite size_enum_ord in h.
rewrite (@one_forms_wedge_concatenate K h2 V (scalar_algebra K) k k alpha beta)
  form_wedge_include
  -(@one_form_algebra_wordE K h2 V (scalar_algebra K) k alpha)
  -(@one_form_algebra_wordE K h2 V (scalar_algebra K) k beta).
exact h.
Qed.
End Products.
