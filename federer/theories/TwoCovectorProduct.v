(** Federer (1969), 1.7.3, p. 29, the wedge products appearing in the
    alternating two-form normal form; the product is defined in 1.4.2, pp.
    18-19. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingForms AlternatingProduct
  OneFormCommutator OneFormIdentification OneFormLinear ScalarCoefficients
  Hom InnerProductUP InnerPolarity SkewNormalFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [two_covector_productE]: Federer 1.7.3,
    p. 29, supporting evaluation of one term in the normal
    form: (alpha wedge beta)(x,y)=alpha(x)beta(y)-alpha(y)beta(x). *)
Lemma two_covector_productE (R : fieldType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (a b : A_m V R^o 1) x y :
  form_wedge h2 (scalar_bilinear R) a b [tuple x; y] =
    a [tuple x] * b [tuple y] - a [tuple y] * b [tuple x].
Proof.
have h := @one_forms_wedge_two R h2 V R^o _ (scalar_bilinear R)
  (one_hom a) (one_hom b) x y.
rewrite /one_generator !one_homK !one_homE in h.
exact h.
Qed.

(** Source for [inner_covector_pair_product]: Federer
    1.7.3, pp. 29-30, a pair of vectors contributes the
    wedge product of their inner-product polarities. *)
Lemma inner_covector_pair_product (R : realFieldType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    a b x y :
  form_wedge h2 (scalar_bilinear R) (inner_polarity hB a) (inner_polarity hB b)
    [tuple x; y] = skew_pair_form B a b x y.
Proof.
rewrite two_covector_productE !inner_polarityE /skew_pair_form.
by rewrite [B y a * B x b]mulrC.
Qed.
