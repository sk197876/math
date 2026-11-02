(** Federer (1969), 1.10.5, pp. 47-48, norm estimates for symmetric forms
    and products. These supporting scalar-extraction identities follow from
    the existing algebra and multilinear universal properties, in every
    characteristic. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_word_scalars]: Federer 1.10.5,
    pp. 47-48, supporting normalization of the factors in a product.
    One scalar in each slot factors out as their product, including
    the empty product. *)
Lemma symmetric_word_scalars (K : fieldType) (V : lmodType K) (I : Type)
    (v : I -> V) (c : I -> K) s :
  symmetric_word [seq c i *: v i | i <- s] =
    (\prod_(i <- s) c i) *: symmetric_word [seq v i | i <- s].
Proof.
elim: s=> [|i s ih]; first by rewrite /= big_nil scale1r.
rewrite /= big_cons !symmetric_word_cons linearZ ih.
by rewrite (bilZl (symmetric_product_bilinear V))
  (bilZr (symmetric_product_bilinear V)) scalerA.
Qed.

(** Source for [symmetric_form_tuple_scalars]: Federer 1.10.5,
    p. 47, supporting multilinearity in all slots at once:
    evaluation on separately scaled vectors extracts the product of scalars. *)
Lemma symmetric_form_tuple_scalars (K : fieldType) (V W : lmodType K) m
    (f : S_m V W m) (v : 'I_m -> V) (c : 'I_m -> K) :
  f [tuple c i *: v i | i < m] = (\prod_(i < m) c i) *: f [tuple v i | i < m].
Proof.
rewrite -!sform_wordsE -!sform_extensionE.
change (sform_extension f (symmetric_word [seq c i *: v i | i <- enum 'I_m]) =
  (\prod_(i < m) c i) *:
    sform_extension f (symmetric_word [seq v i | i <- enum 'I_m])).
by rewrite symmetric_word_scalars linearZ big_enum.
Qed.
