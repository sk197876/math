(** Federer (1969), 1.6.6, pp. 26-27: products and conjugate products of
    one-forms. Supporting word identities from the algebra laws of 1.4.2,
    pp. 18-19. Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates OneFormProducts WordEvaluation
  AlgebraUP AlternatingCoefficientMap FormCoefficients ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Words.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Local Notation A := (alternating_unital_algebra h2 V W).

(** Source for [one_form_algebra_word]: Federer 1.6.6,
    p. 27, displayed products. Ordered multiplication of included
    one-forms in the unital alternating algebra. *)
Definition one_form_algebra_word (s : seq (A_m V W 1)) : A :=
  @word_eval K (Choice.clone (A_m V W 1) _) A (@form_include K V W 1) s.

(** Source for [one_form_algebra_wordE]: Federer 1.6.6,
    p. 27, displayed products. The word is the inclusion of the
    existing homogeneous one-form product. *)
Lemma one_form_algebra_wordE m (a : 'I_m -> A_m V W 1) :
  one_form_algebra_word [seq a j | j <- enum 'I_m] =
  form_include (one_forms_wedge h2 (alg_bilinear W) (alg_one W) a).
Proof.
rewrite (one_forms_wedge_include h2 (alg_bilinear W) (@alg_unitr K W)) /one_forms_product.
have h s : one_form_algebra_word [seq a j | j <- s] =
  foldr (alternating_wedge h2 (alg_bilinear W)) (coefficient_form V (alg_one W))
    [seq form_include (a j) | j <- s].
  by elim: s => [|j s ih] //=; rewrite /one_form_algebra_word /= in ih *; rewrite ih.
exact: h.
Qed.

(** Source for [one_forms_wedge_concatenate]: Federer 1.6.6,
    p. 27, the two blocks alpha_lambda and bar(alpha_mu).
    Concatenating one-form families is their alternating product,
    including either empty block. *)
Lemma one_forms_wedge_concatenate p q (a : 'I_p -> A_m V W 1) (b : 'I_q -> A_m V W 1) :
  one_forms_wedge h2 (alg_bilinear W) (alg_one W) (concatenate_family a b) =
  form_wedge h2 (alg_bilinear W)
    (one_forms_wedge h2 (alg_bilinear W) (alg_one W) a)
    (one_forms_wedge h2 (alg_bilinear W) (alg_one W) b).
Proof.
apply: (can_inj (@form_includeK K V W (p+q))).
rewrite form_wedge_include -!one_form_algebra_wordE concatenate_family_sequence.
by rewrite /one_form_algebra_word word_eval_cat.
Qed.
End Words.

Section Coefficients.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables W Z : algebra K.
Variable f : algebra_map W Z.
Local Notation A := (alternating_unital_algebra h2 V W).
Local Notation B := (alternating_unital_algebra h2 V Z).

(** Source for [one_form_word_coefficients]: Federer 1.6.6,
    pp. 26-27, conjugation of products. Any coefficient algebra map
    commutes with an ordered word of one-forms. *)
Lemma one_form_word_coefficients (s : seq (A_m V W 1)) :
  alternating_coefficient_map h2 V f (one_form_algebra_word h2 s) =
  one_form_algebra_word h2 [seq form_coefficients f a | a <- s].
Proof.
elim: s => [|a s ih].
- exact: algebra_map_one.
- change (alternating_coefficient_map h2 V f
    (alg_mul A (form_include a) (one_form_algebra_word h2 s)) =
    alg_mul B (form_include (form_coefficients f a))
      (one_form_algebra_word h2 [seq form_coefficients f b | b <- s])).
  rewrite algebra_map_mul ih form_coefficients_include; by [].
Qed.

(** Source for [one_forms_wedge_coefficients]: Federer 1.6.6,
    pp. 26-27, conjugation of products. The homogeneous product
    commutes with coefficient algebra maps, also in degree zero. *)
Lemma one_forms_wedge_coefficients m (a : 'I_m -> A_m V W 1) :
  form_coefficients f (one_forms_wedge h2 (alg_bilinear W) (alg_one W) a) =
  one_forms_wedge h2 (alg_bilinear Z) (alg_one Z) (fun j => form_coefficients f (a j)).
Proof.
apply: (can_inj (@form_includeK K V Z m)).
rewrite form_coefficients_include -!one_form_algebra_wordE.
change (alternating_coefficient_map h2 V f (one_form_algebra_word h2 [seq a j | j <- enum 'I_m]) =
  one_form_algebra_word h2 [seq form_coefficients f (a j) | j <- enum 'I_m]).
by rewrite one_form_word_coefficients -map_comp.
Qed.
End Coefficients.
