(** Federer (1969), 3.4.6, p. 322: the original
    mixed coefficient is the actual symmetric derivative
    evaluated on its two repeated argument blocks. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import TensorUP Bilinear Hom HomogeneousHom SymmetricAlgebra SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricDividedMonomials PolynomialTaylorTerms
  PolynomialTaylorTermContinuity HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_mixed_form_value]: the original
    pairing of v^i/i! and z^j/j! equals the
    actual (i+j)-form on the concatenated repeated blocks,
    divided by i!j!, 3.4.6, p. 322.
    Both zero-order blocks are retained. *)
Lemma weierstrass_mixed_form_value (R:realType) (X:lmodType R) i j
    (F:S_m X R^o (i+j)) v z:
  sform_polynomial_value (symmetric_taylor_term j F v) z=
    ((i`!)%:R*(j`!)%:R)^-1*F [tuple of [tuple v | s<i]++[tuple z | s<j]].
Proof.
rewrite symmetric_taylor_term_value addnK /symmetric_divided_vector_power
  (bilZl (@symmetric_product_bilinear R X)) (bilZr (@symmetric_product_bilinear R X))
  !linearZ /=.
rewrite symmetric_product_commute !symmetric_vector_power_constant_tuple symmetric_word_cat.
change (((j`!)%:R:R)^-1*(((i`!)%:R:R)^-1*
  sform_extension F (symmetric_word ([tuple v | s<i]++[tuple z | s<j])))=
  (((i`!)%:R:R)*(j`!)%:R)^-1*F [tuple of [tuple v | s<i]++[tuple z | s<j]]).
rewrite sform_extensionE.
have hWord:sform_words F ([tuple v | s<i]++[tuple z | s<j])=
    F [tuple of [tuple v | s<i]++[tuple z | s<j]].
  exact:(sform_wordsE F [tuple of [tuple v | s<i]++[tuple z | s<j]]).
rewrite hWord.
change (((j`!)%:R:R)^-1*(((i`!)%:R:R)^-1*
    F [tuple of [tuple v | s<i]++[tuple z | s<j]])=
  (((i`!)%:R:R)*(j`!)%:R)^-1*F [tuple of [tuple v | s<i]++[tuple z | s<j]]).
rewrite invfM;ring.
Qed.
