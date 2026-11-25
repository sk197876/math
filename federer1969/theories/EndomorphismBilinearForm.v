(** Federer (1969), 1.7.3, p. 29: the bilinear form S(x,y)=f(x).y used to
    diagonalise a symmetric endomorphism. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP TensorUP Bilinear SymmetricEndomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section AssociatedForm.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable f : {linear V -> V}.

(** Source for [endomorphism_bilinear_form]: Federer 1.7.3,
    p. 29, the displayed definition S(x,y)=f(x).y. *)
Definition endomorphism_bilinear_form x y := B (f x) y.

(** Source for [endomorphism_bilinear_formP]: Federer 1.7.3,
    p. 29, supporting bilinearity of the associated form. *)
Lemma endomorphism_bilinear_formP : @bilinear R V V R^o endomorphism_bilinear_form.
Proof.
split=> y a x z; rewrite /endomorphism_bilinear_form.
- by rewrite linearP (bilDl (inner_bilinear hB)) (bilZl (inner_bilinear hB)).
- by rewrite (bilDr (inner_bilinear hB)) (bilZr (inner_bilinear hB)).
Qed.

(** Source for [endomorphism_form_symmetric]: Federer 1.7.3,
    p. 29, the form associated with a symmetric endomorphism is
    symmetric, so the principal-axis theorem applies. *)
Lemma endomorphism_form_symmetric : is_symmetric_endomorphism B f ->
  forall x y, endomorphism_bilinear_form x y = endomorphism_bilinear_form y x.
Proof. move=> hf x y; by rewrite /endomorphism_bilinear_form hf (inner_symmetric hB). Qed.
End AssociatedForm.
