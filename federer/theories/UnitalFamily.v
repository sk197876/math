(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import AlternatingProduct AlternatingUnit AlternatingFamily
  NonemptyProduct UnitalProduct MultipleShuffles SingleBlockShuffle FamilyArguments
  IteratedShuffle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: the unit assertion also gives the empty iterated
    product. With a unit, the shuffle formula holds for every family,
    including the empty family and forms of degree zero. *)
(** Source for [Sh_multi_nil_unique]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Sh_multi_nil_unique (sigma : Sh_multi [::]) : sigma = identity_Sh [::].
Proof. apply: val_inj; apply/permP=> i; case: i => i hi; exfalso; by move: hi; rewrite ltn0. Qed.

Section UnitalFamily.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable u : W.
Hypothesis hur : right_id u mu.
(** Source for [unital_forms_product]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition unital_forms_product degrees (alpha : form_family V W degrees) : A_star V W :=
  foldr (alternating_wedge h2 hmu) (coefficient_form V u) (form_family_list alpha).
(** Source for [unital_forms_product_nonempty]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma unital_forms_product_nonempty degrees (alpha : form_family V W degrees) : degrees != [::] ->
  unital_forms_product alpha = forms_product h2 hmu alpha.
Proof.
move=> hd; rewrite /unital_forms_product /forms_product
  -(nonempty_product_foldr (alternating_unit_right h2 hmu hur)).
exact: nonempty_product_default (form_family_list_nonempty alpha hd).
Qed.
(** Source for [unital_forms_product_empty]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma unital_forms_product_empty (alpha : form_family V W [::]) :
  unital_forms_product alpha = coefficient_form V u.
Proof. by rewrite /unital_forms_product form_family_list_nil. Qed.
(** Source for [unital_forms_product_homogeneous]: Federer (1969), 1.4.2,
    pp. 18-19, block-degree notation and iterated shuffle formula. In words:
    For an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma unital_forms_product_homogeneous degrees (alpha : form_family V W degrees) :
  homogeneous (A_star_grading V W) (sumn degrees) (unital_forms_product alpha).
Proof.
case: degrees alpha => [|p ds] alpha.
- rewrite unital_forms_product_empty; exact: coefficient_form_homogeneous.
- rewrite unital_forms_product_nonempty //; exact: forms_product_homogeneous.
Qed.
(** Source for [unital_iterated_form]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition unital_iterated_form degrees (alpha : form_family V W degrees) : A_m V W (sumn degrees) :=
  form_component (sumn degrees) (unital_forms_product alpha).
(** Source for [unital_iterated_form_include]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma unital_iterated_form_include degrees (alpha : form_family V W degrees) :
  form_include (unital_iterated_form alpha) = unital_forms_product alpha.
Proof. rewrite /unital_iterated_form form_componentK; exact: unital_forms_product_homogeneous. Qed.
(** Source for [unital_iterated_form_shuffle]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem unital_iterated_form_shuffle degrees (alpha : form_family V W degrees)
    (t : (sumn degrees).-tuple V) :
  unital_iterated_form alpha t = \sum_(sigma : Sh_multi degrees)
    FedererPermutation.index K (val sigma) *: foldr mu u (family_values alpha t (val sigma)).
Proof.
rewrite /unital_iterated_form form_componentE.
case: degrees alpha t => [|p ds] alpha t.
- rewrite unital_forms_product_empty coefficient_formE exterior_augmentation_word.
  have ht : val t = [::] := size0nil (size_tuple t).
  rewrite ht /word_degree_zero scale1r.
  rewrite (big_pred1 (identity_Sh [::])); last by move=> sigma; rewrite (Sh_multi_nil_unique sigma) inE eqxx.
  change (u = FedererPermutation.index K (1%g : 'S_0) *: foldr mu u (family_values alpha t 1%g)).
  by rewrite (index_one h2) /family_values enum_ord0 /= scale1r.
- have hd : p::ds != [::] by [].
  rewrite (unital_forms_product_nonempty alpha hd) (forms_product_shuffle h2 hmu alpha t hd).
  apply: eq_bigr => sigma _; rewrite /multiple_shuffle_term; congr (_ *: _).
  rewrite -(nonempty_product_foldr hur).
  exact: nonempty_product_default (family_values_nonempty alpha t (val sigma) hd).
Qed.
End UnitalFamily.
