(** Federer (1969), 1.10.5, p. 47, the shuffle argument for product norms;
    supporting iterated form of the binary formula in 1.10.2, p. 45. The
    unsigned formula uses ordered coefficient multiplication.
    Right-associated products let the proof work for any bilinear
    multiplication; in an associative algebra this is the unparenthesized
    product in the sources. Nonempty products do not require a coefficient
    unit. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import TensorUP Bilinear AlgebraUP Graded GradedComponents
  Hom HomogeneousHom BoundedHom SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormSum SymmetricFormProduct SymmetricFormShuffle NonemptyProduct
  Shuffles AlternatingShuffle MultipleShuffles PermutationArguments ShuffleComposition SingleBlockShuffle
  MultipleShuffleBijection MultipleShuffleSums OneDegreeShuffles.
From Federer Require Import SymmetricFormFamily SymmetricFamilyArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section IteratedShuffle.
Variable K : fieldType.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.

(** Source for [symmetric_multiple_shuffle_term]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Each summand is the ordered coefficient product of the block
    evaluations, without a sign. *)
Definition symmetric_multiple_shuffle_term degrees (alpha : symmetric_form_family V W degrees)
    (t : (sumn degrees).-tuple V) (sigma : Sh_multi degrees) : W :=
  nonempty_product mu 0 (symmetric_family_values alpha t (val sigma)).

(** Source for [symmetric_multiple_shuffle_term_single]: Federer 1.10.5, p.
    47, supporting iterated shuffle calculation from 1.10.2, p. 45. In
    words: For one block the sole shuffle summand is the original form
    value. *)
Lemma symmetric_multiple_shuffle_term_single p (alpha : symmetric_form_family V W [::p]) t :
  symmetric_multiple_shuffle_term alpha t (identity_Sh [::p]) = sform_words (symmetric_form_family_head alpha) t.
Proof.
change (nonempty_product mu 0 (symmetric_family_values alpha t 1%g) = sform_words (symmetric_form_family_head alpha) t).
by rewrite symmetric_family_values_single.
Qed.

(** Source for [symmetric_multiple_shuffle_term_cons]: Federer 1.10.5, p.
    47, supporting iterated shuffle calculation from 1.10.2, p. 45. In
    words: Composing the first-block shuffle with the tail shuffle gives the
    recursive summand. *)
Lemma symmetric_multiple_shuffle_term_cons p ds (alpha : symmetric_form_family V W (p::ds)) t
    (tau : Sh p (sumn ds)) (sigma : Sh_multi ds) : ds != [::] ->
  symmetric_multiple_shuffle_term alpha t (compose_multiple (tau, sigma)) =
    mu (symmetric_form_family_head alpha (shuffle_left_tuple t (val tau)))
        (symmetric_multiple_shuffle_term (symmetric_form_family_tail alpha) (shuffle_right_tuple t (val tau)) sigma).
Proof.
move=> hd; rewrite /symmetric_multiple_shuffle_term compose_multipleE symmetric_family_values_cons.
by rewrite nonempty_product_cons ?symmetric_family_values_nonempty.
Qed.

(** Source for [symmetric_family_product_binary]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    Evaluation of a family product splits into the first form and the
    iterated tail. *)
Lemma symmetric_family_product_binary p ds (alpha : symmetric_form_family V W (p::ds))
    (t : (p+sumn ds).-tuple V) : ds != [::] ->
  symmetric_family_product hmu alpha (symmetric_word t) =
    sform_product hmu (symmetric_form_family_head alpha) (symmetric_iterated_form hmu (symmetric_form_family_tail alpha)) t.
Proof.
move=> hd; rewrite symmetric_family_product_cons // -(symmetric_iterated_form_include hmu (symmetric_form_family_tail alpha) hd)
  -sform_product_include sform_includeE sform_extensionE sform_wordsE.
by [].
Qed.

(** Source for [symmetric_family_product_shuffle]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    The iterated symmetric product is the sum of the ordered block
    evaluations over all block shuffles. *)
Theorem symmetric_family_product_shuffle degrees (alpha : symmetric_form_family V W degrees)
    (t : (sumn degrees).-tuple V) : degrees != [::] ->
  symmetric_family_product hmu alpha (symmetric_word t) =
    \sum_(sigma : Sh_multi degrees) symmetric_multiple_shuffle_term alpha t sigma.
Proof.
elim: degrees alpha t => [|p ds ih] alpha t // hd.
case hds: ds ih alpha t hd => [|q rest] ih alpha t hd.
- rewrite symmetric_family_product_single sform_includeE sform_extensionE.
  rewrite (big_pred1 (identity_Sh [::p])); last by move=> sigma; rewrite (Sh_multi_single_unique sigma) inE eqxx.
  exact (esym (symmetric_multiple_shuffle_term_single alpha t)).
- have hne : q :: rest != [::] by [].
  rewrite symmetric_family_product_binary // sform_product_shuffle.
  rewrite multiple_shuffle_sum.
  apply: eq_bigr => tau _.
  rewrite symmetric_iterated_formE (ih (symmetric_form_family_tail alpha) (shuffle_right_tuple t (val tau)) hne).
  rewrite (big_morph (mu (symmetric_form_family_head alpha (shuffle_left_tuple t (val tau))))
    (bilDr hmu _) (bil0r hmu _)).
  apply: eq_bigr => sigma _; symmetry; exact: symmetric_multiple_shuffle_term_cons hne.
Qed.

(** Source for [symmetric_iterated_form_shuffle]: Federer 1.10.5, p. 47,
    supporting iterated shuffle calculation from 1.10.2, p. 45. In words:
    State the unsigned iterated shuffle formula using actual tuple
    evaluations. *)
Theorem symmetric_iterated_form_shuffle degrees (alpha : symmetric_form_family V W degrees)
    (t : (sumn degrees).-tuple V) : degrees != [::] ->
  symmetric_iterated_form hmu alpha t = \sum_(sigma : Sh_multi degrees)
      nonempty_product mu 0 [seq alpha i (block_tuple i t (val sigma)) | i <- enum 'I_(size degrees)].
Proof.
move=> hd; rewrite symmetric_iterated_formE (symmetric_family_product_shuffle alpha t hd).
apply: eq_bigr => sigma _; by rewrite /symmetric_multiple_shuffle_term symmetric_family_values_tuples.
Qed.
End IteratedShuffle.
