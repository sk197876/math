(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import AlternatingProduct AlternatingFamily NonemptyProduct
  MultipleShuffles FamilyArguments IteratedShuffle OneDegreeShuffles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, the formula when every p(i)=1. The explicit degree
    hypothesis lets us retain the very same family and product as in the
    preceding formula. form_words alpha [::v] denotes its evaluation on
    the one argument v; one_degrees_nth proves that the degree is one. *)
Section OneForms.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable degrees : seq nat.
Hypothesis hone : all (pred1 1%N) degrees.
Variable alpha : form_family V W degrees.
(** Source for [one_family_values]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Definition or construction used to
    formalise this passage. *)
Definition one_family_values (t : (sumn degrees).-tuple V) (sigma : 'S_(sumn degrees)) : seq W :=
  [seq form_words (alpha i) [:: tnth t (sigma (cast_ord (one_degrees_sum hone) i))]
    | i <- enum 'I_(size degrees)].
(** Source for [family_values_one]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma family_values_one t sigma : family_values alpha t sigma = one_family_values t sigma.
Proof. apply: eq_map => i; by rewrite (one_degree_argument hone). Qed.
(** Source for [one_form_permutation_formula]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem one_form_permutation_formula (t : (sumn degrees).-tuple V) : degrees != [::] ->
  iterated_form h2 hmu alpha t = \sum_(sigma : 'S_(sumn degrees))
    FedererPermutation.index K sigma *: nonempty_product mu 0 (one_family_values t sigma).
Proof.
move=> hd; rewrite iterated_formE (forms_product_shuffle h2 hmu alpha t hd).
under eq_bigr do rewrite /multiple_shuffle_term family_values_one.
rewrite -(sum_subtype (@multiple_shuffle_in degrees (sumn degrees))
  (fun sigma => FedererPermutation.index K sigma *: nonempty_product mu 0 (one_family_values t sigma))).
apply: eq_bigl => sigma; exact (@one_degrees_shuffle degrees hone (sumn degrees) sigma).
Qed.
End OneForms.
