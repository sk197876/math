(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingForms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1: A^0(V,W)=W. Functions on the single empty tuple are
    identified with their values; no nonempty position or repeated pair
    exists in arity zero. Both identifications are linear and inverse. *)
Section DegreeZero.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [zero_form_multilinear]: Federer (1969), 1.4.1, p. 17,
    sentence imposing the convention A^0(V,W)=W. In words: The degree-zero
    identifications use the convention that a zero-form is a coefficient in
    W. Supporting lemma for this passage; not separately stated in the book. *)
Lemma zero_form_multilinear (w : W) : @m_linear K V W 0 (fun _ => w).
Proof.
move=> s t h; have hs := h.
by rewrite size_cat /= addnS in hs.
Qed.
(** Source for [zero_form_alternating]: Federer (1969), 1.4.1, p. 17,
    sentence imposing the convention A^0(V,W)=W. In words: The degree-zero
    identifications use the convention that a zero-form is a coefficient in
    W. Supporting lemma for this passage; not separately stated in the book. *)
Lemma zero_form_alternating (w : W) : @alternating K V W 0 (fun _ => w).
Proof. by move=> t; rewrite (tuple0 t). Qed.
(** Source for [zero_form]: Federer (1969), 1.4.1, p. 17, sentence imposing
    the convention A^0(V,W)=W. In words: The degree-zero identifications use
    the convention that a zero-form is a coefficient in W. Definition or
    construction used to formalise this passage. *)
Definition zero_form (w : W) : A_m V W 0 :=
  @AlternatingForm K V W 0 (fun _ => w)
    (introT (asboolP _) (conj (zero_form_multilinear w) (zero_form_alternating w))).
(** Source for [zero_form_value]: Federer (1969), 1.4.1, p. 17, sentence
    imposing the convention A^0(V,W)=W. In words: The degree-zero
    identifications use the convention that a zero-form is a coefficient in
    W. Definition or construction used to formalise this passage. *)
Definition zero_form_value (f : A_m V W 0) : W := f [tuple].
(** Source for [zero_formE]: Federer (1969), 1.4.1, p. 17, sentence imposing
    the convention A^0(V,W)=W. In words: The degree-zero identifications use
    the convention that a zero-form is a coefficient in W. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma zero_formE w t : zero_form w t = w.
Proof. by []. Qed.
(** Source for [zero_formK]: Federer (1969), 1.4.1, p. 17, sentence imposing
    the convention A^0(V,W)=W. In words: The degree-zero identifications use
    the convention that a zero-form is a coefficient in W. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma zero_formK : cancel zero_form zero_form_value.
Proof. by []. Qed.
(** Source for [zero_form_valueK]: Federer (1969), 1.4.1, p. 17, sentence
    imposing the convention A^0(V,W)=W. In words: The degree-zero
    identifications use the convention that a zero-form is a coefficient in
    W. Supporting lemma for this passage; not separately stated in the book. *)
Lemma zero_form_valueK : cancel zero_form_value zero_form.
Proof. move=> f; apply: form_ext => t; by rewrite (tuple0 t). Qed.
(** Source for [zero_form_linear]: Federer (1969), 1.4.1, p. 17, sentence
    imposing the convention A^0(V,W)=W. In words: The degree-zero
    identifications use the convention that a zero-form is a coefficient in
    W. Supporting lemma for this passage; not separately stated in the book. *)
Lemma zero_form_linear : linear zero_form.
Proof. move=> a x y; apply: form_ext => t; by []. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W (A_m V W 0)
  *:%R zero_form zero_form_linear.
(** Source for [zero_form_value_linear]: Federer (1969), 1.4.1, p. 17,
    sentence imposing the convention A^0(V,W)=W. In words: The degree-zero
    identifications use the convention that a zero-form is a coefficient in
    W. Supporting lemma for this passage; not separately stated in the book. *)
Lemma zero_form_value_linear : linear zero_form_value.
Proof. by move=> a f g; rewrite /zero_form_value form_addE form_scaleE. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (A_m V W 0) W
  *:%R zero_form_value zero_form_value_linear.
End DegreeZero.
