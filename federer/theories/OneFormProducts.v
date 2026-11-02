(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import AlternatingAlgebra.
From Federer Require Import FormCasts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3 uses ordered products of one-forms. This specialises
    the exact product and shuffle formula of 1.4.2 to an m-indexed
    family, also for m=0. *)
Section OneFormProducts.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable u : W.
Hypothesis hur : right_id u mu.
(** Source for [one_forms_product]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Definition or construction used to
    formalise this passage. *)
Definition one_forms_product m (alpha : 'I_m -> A_m V W 1) : A_star V W :=
  foldr (alternating_wedge h2 hmu) (coefficient_form V u)
    [seq form_include (alpha i) | i <- enum 'I_m].
(** Source for [one_forms_wedge]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Definition or construction used to
    formalise this passage. *)
Definition one_forms_wedge m (alpha : 'I_m -> A_m V W 1) : A_m V W m :=
  form_component m (one_forms_product alpha).
(** Source for [constant_family_product]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma constant_family_product m (alpha : 'I_m -> A_m V W 1) :
  unital_forms_product h2 hmu u (constant_form_family alpha) = one_forms_product alpha.
Proof. by rewrite /unital_forms_product constant_family_list. Qed.
(** Source for [one_forms_product_homogeneous]: Federer (1969), 1.4.2, p.
    19, specialisation p(i)=1. In words: The alternating product of
    one-forms evaluates as the sum over all permutations of the signed
    ordered products of the one-form values. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma one_forms_product_homogeneous m (alpha : 'I_m -> A_m V W 1) :
  homogeneous (A_star_grading V W) m (one_forms_product alpha).
Proof.
have h := unital_forms_product_homogeneous h2 hmu hur (constant_form_family alpha).
by rewrite constant_family_product ones_sum in h.
Qed.
(** Source for [one_forms_wedge_include]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma one_forms_wedge_include m (alpha : 'I_m -> A_m V W 1) :
  form_include (one_forms_wedge alpha) = one_forms_product alpha.
Proof. rewrite /one_forms_wedge form_componentK; exact: one_forms_product_homogeneous. Qed.
(** Source for [one_forms_wedgeE]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma one_forms_wedgeE m (alpha : 'I_m -> A_m V W 1) (t : m.-tuple V) :
  one_forms_wedge alpha t = one_forms_product alpha (exterior_word t).
Proof. exact: form_componentE. Qed.

(** Source for [constant_family_one_values]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma constant_family_one_values m (alpha : 'I_m -> A_m V W 1) (t : m.-tuple V) (sigma : 'S_m) :
  family_values (constant_form_family alpha) (tcast (esym (ones_sum m)) t)
    (cast_perm (esym (ones_sum m)) sigma) =
      [seq alpha i [tuple tnth t (sigma i)] | i <- enum 'I_m].
Proof.
rewrite (family_values_one (all_pred1_nseq 1%N m)) /one_family_values.
have hi (i : 'I_(size (nseq m 1%N))) :
    cast_ord (one_degrees_sum (all_pred1_nseq 1%N m)) i =
      cast_ord (esym (ones_sum m)) (cast_ord (size_nseq m 1%N) i).
  exact: val_inj.
under eq_map do rewrite constant_family_words hi cast_tnth_perm.
have ev i : form_words (alpha (cast_ord (size_nseq m 1%N) i))
    [:: tnth t (sigma (cast_ord (size_nseq m 1%N) i))] =
    alpha (cast_ord (size_nseq m 1%N) i) [tuple tnth t (sigma (cast_ord (size_nseq m 1%N) i))].
  exact (@form_wordsE K V W 1 (alpha (cast_ord (size_nseq m 1%N) i))
    [tuple tnth t (sigma (cast_ord (size_nseq m 1%N) i))]).
under eq_map do rewrite ev.
by rewrite (map_comp (fun i => alpha i [tuple tnth t (sigma i)]) (cast_ord (size_nseq m 1%N))) cast_enum.
Qed.

(** Source for [one_forms_wedge_permutations]: Federer (1969), 1.4.2, p. 19,
    specialisation p(i)=1. In words: The alternating product of one-forms
    evaluates as the sum over all permutations of the signed ordered
    products of the one-form values. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem one_forms_wedge_permutations m (alpha : 'I_m -> A_m V W 1) (t : m.-tuple V) :
  one_forms_wedge alpha t = \sum_(sigma : 'S_m) FedererPermutation.index K sigma *:
    foldr mu u [seq alpha i [tuple tnth t (sigma i)] | i <- enum 'I_m].
Proof.
pose ds := nseq m 1%N.
pose a := constant_form_family alpha.
pose t' := tcast (esym (ones_sum m)) t.
have h := unital_iterated_form_shuffle h2 hmu hur a t'.
rewrite /unital_iterated_form form_componentE constant_family_product /t' val_tcast in h.
rewrite one_forms_wedgeE h.
rewrite -(sum_subtype (@multiple_shuffle_in ds (sumn ds))
  (fun sigma => FedererPermutation.index K sigma *: foldr mu u (family_values a t' sigma))).
have he : (fun sigma : 'S_(sumn ds) => multiple_shuffle_in ds sigma) =1 predT.
  move=> sigma; exact (@one_degrees_shuffle ds (all_pred1_nseq 1%N m) (sumn ds) sigma).
rewrite (eq_bigl _ _ he) (reindex (cast_perm (esym (ones_sum m)))).
- apply: eq_bigr => sigma _; by rewrite index_cast_perm /a /t' constant_family_one_values.
- apply: onW_bij; exists (cast_perm (ones_sum m)).
  + exact: cast_permKV.
  + exact: cast_permK.
Qed.
End OneFormProducts.
