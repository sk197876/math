(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import AlternatingProduct AlternatingShuffle AlternatingFamily
  NonemptyProduct PermutationArguments FamilyArguments MultipleShuffles
  MultipleShuffleBijection MultipleShuffleSums SingleBlockShuffle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, the iterated shuffle formula. The product on the right
    is in its given order. The proof works for right-associated products
    even before associativity of the coefficient multiplication is imposed. *)
Section IteratedShuffle.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
(** Source for [multiple_shuffle_term]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition multiple_shuffle_term degrees (alpha : form_family V W degrees)
    (t : (sumn degrees).-tuple V) (sigma : Sh_multi degrees) : W :=
  FedererPermutation.index K (val sigma) *:
    nonempty_product mu 0 (family_values alpha t (val sigma)).
(** Source for [multiple_shuffle_term_single]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma multiple_shuffle_term_single p (alpha : form_family V W [::p]) t :
  multiple_shuffle_term alpha t (identity_Sh [::p]) = form_words (form_family_head alpha) t.
Proof.
change (FedererPermutation.index K (1%g : 'S_(sumn [::p])) *: nonempty_product mu 0 (family_values alpha t 1%g) = form_words (form_family_head alpha) t).
by rewrite (index_one h2) family_values_single scale1r.
Qed.
(** Source for [multiple_shuffle_term_cons]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma multiple_shuffle_term_cons p ds (alpha : form_family V W (p::ds)) t
    (tau : Sh p (sumn ds)) (sigma : Sh_multi ds) : ds != [::] ->
  multiple_shuffle_term alpha t (compose_multiple (tau, sigma)) =
    FedererPermutation.index K (val tau) *:
      mu (form_family_head alpha (shuffle_left_tuple t (val tau)))
        (multiple_shuffle_term (form_family_tail alpha) (shuffle_right_tuple t (val tau)) sigma).
Proof.
move=> hd; rewrite /multiple_shuffle_term (compose_multiple_index h2) compose_multipleE family_values_cons.
rewrite nonempty_product_cons ?family_values_nonempty //.
by rewrite (bilZr hmu) scalerA.
Qed.
(** Source for [forms_product_binary]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma forms_product_binary p ds (alpha : form_family V W (p::ds))
    (t : (p+sumn ds).-tuple V) : ds != [::] ->
  forms_product h2 hmu alpha (exterior_word t) =
    form_wedge h2 hmu (form_family_head alpha) (iterated_form h2 hmu (form_family_tail alpha)) t.
Proof.
move=> hd; rewrite forms_product_cons // -(iterated_form_include h2 hmu (form_family_tail alpha) hd)
  -form_wedge_include form_includeE form_extensionE form_wordsE.
by [].
Qed.
(** Source for [forms_product_shuffle]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem forms_product_shuffle degrees (alpha : form_family V W degrees)
    (t : (sumn degrees).-tuple V) : degrees != [::] ->
  forms_product h2 hmu alpha (exterior_word t) =
    \sum_(sigma : Sh_multi degrees) multiple_shuffle_term alpha t sigma.
Proof.
elim: degrees alpha t => [|p ds ih] alpha t // hd.
case hds: ds ih alpha t hd => [|q rest] ih alpha t hd.
- rewrite forms_product_single form_includeE form_extensionE.
  rewrite (big_pred1 (identity_Sh [::p])); last by move=> sigma; rewrite (Sh_multi_single_unique sigma) inE eqxx.
  exact (esym (multiple_shuffle_term_single alpha t)).
- have hne : q :: rest != [::] by [].
  rewrite forms_product_binary // form_wedge_shuffle.
  rewrite multiple_shuffle_sum.
  apply: eq_bigr => tau _.
  rewrite iterated_formE (ih (form_family_tail alpha) (shuffle_right_tuple t (val tau)) hne).
  rewrite (big_morph (mu (form_family_head alpha (shuffle_left_tuple t (val tau))))
    (bilDr hmu _) (bil0r hmu _)) scaler_sumr.
  apply: eq_bigr => sigma _; symmetry; exact: multiple_shuffle_term_cons hne.
Qed.
(** Source for [iterated_form_shuffle]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem iterated_form_shuffle degrees (alpha : form_family V W degrees)
    (t : (sumn degrees).-tuple V) : degrees != [::] ->
  iterated_form h2 hmu alpha t = \sum_(sigma : Sh_multi degrees)
    FedererPermutation.index K (val sigma) *:
      nonempty_product mu 0 [seq alpha i (block_tuple i t (val sigma)) | i <- enum 'I_(size degrees)].
Proof.
move=> hd; rewrite iterated_formE (forms_product_shuffle alpha t hd).
apply: eq_bigr => sigma _; by rewrite /multiple_shuffle_term family_values_tuples.
Qed.
End IteratedShuffle.
