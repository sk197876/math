(** Federer (1969), 1.10.5, p. 47, induced inner product. The permutation
    formula holds without a finite-dimensional hypothesis and includes
    degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import AlgebraUP Hom BoundedHom GradedComponents
  InnerProductUP InnerSymmetricPolarity InnerSymmetric InnerSymmetricMonomials
  SymmetricAlgebra SymmetricGrading SymmetricLowPowers SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormSum SymmetricPairing SymmetricFormProduct SymmetricFormUnit
  SymmetricDualMonomialProducts SymmetricOneFormProductFormula ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Formula.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_symmetric_polarity_words]: Federer 1.10.5,
    p. 47, supporting evaluation of the generator polarity on
    a singleton word: the result is the original inner product. *)
Lemma inner_symmetric_polarity_words x y :
  sform_words (inner_symmetric_polarity hB y) [:: x] = B x y.
Proof.
have he : symmetric_tuple_component [tuple x] = symmetric_first_inclusion V x.
  apply: val_inj.
  change (component_val (symmetric_tuple_component [tuple x]) =
    component_val (symmetric_first_inclusion V x)).
  rewrite symmetric_tuple_componentE.
  by rewrite /symmetric_first_inclusion /=.
change (sform_words (inner_symmetric_polarity hB y) [tuple x] = B x y).
rewrite sform_wordsE -symmetric_pairing_tuple he.
exact: inner_symmetric_polarityE.
Qed.

(** Source for [inner_symmetric_tuple_extension]: Federer 1.10.5,
    p. 47, supporting use of the algebra extension: gamma of a
    vector product is the actual product of the individual polarities. *)
Lemma inner_symmetric_tuple_extension m (w : m.-tuple V) :
  inner_symmetric_extension hB (symmetric_word w) =
    foldr (symmetric_forms_product (scalar_bilinear R))
      (@symmetric_coefficient_form R V R^o 1)
      [seq sform_include (inner_symmetric_polarity hB (tnth w i)) | i <- enum 'I_m].
Proof.
have he := @inner_symmetric_word R V B hB m (tnth w) (enum 'I_m).
by rewrite map_tnth_enum /symmetric_one_form_word in he.
Qed.

(** Source for [symmetric_inner_tuple_permutations_positive]: Federer
    1.10.5, p. 47. For positive degree, the inner product of two products is
    the unsigned sum over permutations of products of the original pairings. *)
Theorem symmetric_inner_tuple_permutations_positive m (v w : m.-tuple V) :
  (0 < m)%N ->
  symmetric_inner_form hB (symmetric_tuple_component v) (symmetric_tuple_component w) =
    \sum_(sigma : 'S_m) \prod_(i < m) B (tnth v (sigma i)) (tnth w i).
Proof.
move=> hm; rewrite symmetric_inner_formE !symmetric_tuple_componentE
  inner_symmetric_tuple_extension (symmetric_one_form_product_permutations _ v hm).
apply: eq_bigr=> sigma _; apply: eq_bigr=> i _.
exact: inner_symmetric_polarity_words.
Qed.

(** Source for [symmetric_inner_tuple_permutations]: Federer 1.10.5, p. 47,
    induced inner product The unsigned permutation formula includes degree
    zero, where both products are the unit and the unique empty permutation
    contributes one. *)
Theorem symmetric_inner_tuple_permutations m (v w : m.-tuple V) :
  symmetric_inner_form hB (symmetric_tuple_component v) (symmetric_tuple_component w) =
    \sum_(sigma : 'S_m) \prod_(i < m) B (tnth v (sigma i)) (tnth w i).
Proof.
case: m v w=> [|m] v w; last exact: symmetric_inner_tuple_permutations_positive.
rewrite symmetric_inner_formE !symmetric_tuple_componentE
  inner_symmetric_tuple_extension enum_ord0.
change (@symmetric_coefficient_form R V R^o 1 (symmetric_word v) =
  \sum_(sigma : 'S_0) \prod_(i < 0) B (tnth v (sigma i)) (tnth w i)).
rewrite symmetric_coefficient_formE.
rewrite (tuple0 v) /= symmetric_word_nil symmetric_augmentation_unit scale1r.
under eq_bigr do rewrite big_ord0.
by rewrite sumr_const card_Sn /=.
Qed.
End Formula.
