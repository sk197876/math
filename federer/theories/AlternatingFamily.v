(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Alternating.
From Federer Require Import AlternatingProduct NonemptyProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, the m alternating forms of degrees p(i). The sequence
    of degrees retains their order. Products of nonempty families are
    defined without adding a unit to the coefficient algebra. *)
Section Families.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [form_family]: Federer (1969), 1.4.2, pp. 18-19, block-degree
    notation and iterated shuffle formula. In words: For an ordered family
    of forms, sum over permutations increasing on each prescribed block,
    multiplying the block evaluations in the original order and weighting by
    permutation index. Definition or construction used to formalise this
    passage. *)
Definition form_family degrees := forall i : 'I_(size degrees), A_m V W (nth 0%N degrees i).
(** Source for [form_family_list]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition form_family_list degrees (alpha : form_family degrees) : seq (A_star V W) :=
  [seq form_include (alpha i) | i <- enum 'I_(size degrees)].
(** Source for [form_family_head]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition form_family_head p ds (alpha : form_family (p::ds)) : A_m V W p := alpha ord0.
(** Source for [form_family_tail]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition form_family_tail p ds (alpha : form_family (p::ds)) : form_family ds :=
  fun i => alpha (lift ord0 i).
(** Source for [form_family_list_size]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma form_family_list_size degrees (alpha : form_family degrees) :
  size (form_family_list alpha) = size degrees.
Proof. by rewrite /form_family_list size_map size_enum_ord. Qed.
(** Source for [form_family_list_cons]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma form_family_list_cons p ds (alpha : form_family (p::ds)) :
  form_family_list alpha = form_include (form_family_head alpha) :: form_family_list (form_family_tail alpha).
Proof.
rewrite /form_family_list enum_ordSl map_cons.
congr (_ :: _); exact (esym (map_comp (fun i => form_include (alpha i)) (lift ord0) (enum 'I_(size ds)))).
Qed.
(** Source for [form_family_list_nil]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma form_family_list_nil (alpha : form_family [::]) : form_family_list alpha = [::].
Proof. by rewrite /form_family_list enum_ord0. Qed.
(** Source for [form_family_list_nonempty]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma form_family_list_nonempty degrees (alpha : form_family degrees) :
  degrees != [::] -> form_family_list alpha != [::].
Proof.
move=> hd; apply/eqP=> he; have hs := congr1 size he.
by move: hd; rewrite -size_eq0 -(form_family_list_size alpha) hs.
Qed.
End Families.
Arguments form_family {K} V W degrees.

Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
(** Source for [forms_product]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition forms_product degrees (alpha : form_family V W degrees) : A_star V W :=
  nonempty_product (alternating_wedge h2 hmu) 0 (form_family_list alpha).
(** Source for [forms_product_single]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma forms_product_single p (alpha : form_family V W [::p]) :
  forms_product alpha = form_include (form_family_head alpha).
Proof. by rewrite /forms_product form_family_list_cons form_family_list_nil. Qed.
(** Source for [forms_product_cons]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma forms_product_cons p ds (alpha : form_family V W (p::ds)) : ds != [::] ->
  forms_product alpha = alternating_wedge h2 hmu
    (form_include (form_family_head alpha)) (forms_product (form_family_tail alpha)).
Proof.
move=> hd; rewrite /forms_product form_family_list_cons nonempty_product_cons //.
exact: form_family_list_nonempty hd.
Qed.
(** Source for [forms_product_homogeneous]: Federer (1969), 1.4.2, pp.
    18-19, block-degree notation and iterated shuffle formula. In words: For
    an ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma forms_product_homogeneous degrees (alpha : form_family V W degrees) :
  degrees != [::] -> homogeneous (A_star_grading V W) (sumn degrees) (forms_product alpha).
Proof.
elim: degrees alpha => [|p ds ih] alpha //.
case: ds ih alpha => [|q ds] ih alpha hd.
- rewrite forms_product_single /= addn0; exact: form_include_homogeneous.
- rewrite forms_product_cons //.
  apply: alternating_wedge_graded; first exact: form_include_homogeneous.
  exact: ih.
Qed.
(** Source for [iterated_form]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Definition iterated_form degrees (alpha : form_family V W degrees) : A_m V W (sumn degrees) :=
  form_component (sumn degrees) (forms_product alpha).
(** Source for [iterated_formE]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma iterated_formE degrees (alpha : form_family V W degrees) (t : (sumn degrees).-tuple V) :
  iterated_form alpha t = forms_product alpha (exterior_word t).
Proof. exact: form_componentE. Qed.
(** Source for [iterated_form_include]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma iterated_form_include degrees (alpha : form_family V W degrees) : degrees != [::] ->
  form_include (iterated_form alpha) = forms_product alpha.
Proof. move=> hd; rewrite /iterated_form form_componentK; exact: forms_product_homogeneous hd. Qed.
End Products.
