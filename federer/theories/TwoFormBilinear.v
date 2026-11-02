(** Federer (1969), 1.7.3, pp. 29-30: the alternating two-form viewed as the
    bilinear function phi(x,y). *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingForms AlternatingWords TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TwoForm.
Variable R : fieldType.
Variable V : lmodType R.
Variable phi : A_m V R^o 2.

(** Source for [two_form_bilinear]: Federer 1.7.3,
    pp. 29-30, supporting bilinearity of the displayed phi(x,y). *)
Lemma two_form_bilinear : @bilinear R V V R^o (fun x y => phi [tuple x; y]).
Proof.
split=> y a x z.
- have h := form_words_multilinear phi [::] [::y] a x z.
  change (form_words phi [tuple a *: x+z; y] =
    a *: form_words phi [tuple x; y] + form_words phi [tuple z; y]) in h.
  by rewrite !form_wordsE in h.
- have h := form_words_multilinear phi [::y] [::] a x z.
  change (form_words phi [tuple y; a *: x+z] =
    a *: form_words phi [tuple y; x] + form_words phi [tuple y; z]) in h.
  by rewrite !form_wordsE in h.
Qed.

(** Source for [two_form_diagonal_zero]: Federer 1.7.3,
    pp. 29-30, supporting alternation of phi(x,y). *)
Lemma two_form_diagonal_zero x : phi [tuple x; x] = 0.
Proof.
have hn : ~~ uniq [::x; x] by rewrite /= in_cons eqxx.
have h := form_words_alternating phi hn.
change (form_words phi [tuple x; x] = 0) in h.
by rewrite form_wordsE in h.
Qed.

(** Source for [two_form_skew]: Federer 1.7.3, pp. 29-30,
    the alternating two-form satisfies phi(x,y)=-phi(y,x),
    as used to obtain the skewsymmetric endomorphism. *)
Lemma two_form_skew x y : phi [tuple x; y] = - phi [tuple y; x].
Proof.
have h := two_form_diagonal_zero (x+y).
rewrite (bilDl two_form_bilinear) !(bilDr two_form_bilinear)
  !two_form_diagonal_zero add0r addr0 in h.
apply/eqP; rewrite -addr_eq0; apply/eqP; exact h.
Qed.
End TwoForm.
