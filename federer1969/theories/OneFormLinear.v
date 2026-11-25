(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import AlternatingAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3: evaluate a one-covector on a vector. This is the
    corresponding linear map in Hom(V,W), as used explicitly in 1.4.4. *)
Section OneFormLinear.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [one_form_evaluation]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition one_form_evaluation (omega : A_m V W 1) (v : V) := omega [tuple v].
(** Source for [one_form_evaluation_linear]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma one_form_evaluation_linear omega : linear (one_form_evaluation omega).
Proof.
move=> a v w; have h := form_words_multilinear omega [::] [::] a v w.
change (form_words omega [tuple a *: v + w] =
  a *: form_words omega [tuple v] + form_words omega [tuple w]) in h.
by rewrite !form_wordsE in h.
Qed.
HB.instance Definition _ omega := GRing.isLinear.Build K V W *:%R
  (one_form_evaluation omega) (one_form_evaluation_linear omega).
(** Source for [one_hom]: Federer (1969), 1.4.3, p. 19, opening assertion
    and biorthogonal-vector argument. In words: Increasing products of a
    finite independent family of covectors are independent; evaluation on
    the corresponding products of biorthogonal vectors gives the Kronecker
    pairing. Definition or construction used to formalise this passage. *)
Definition one_hom (omega : A_m V W 1) : Hom V W :=
  hom_of_linear (GRing.Linear.clone _ _ _ _ (one_form_evaluation omega) _).
(** Source for [one_homE]: Federer (1969), 1.4.3, p. 19, opening assertion
    and biorthogonal-vector argument. In words: Increasing products of a
    finite independent family of covectors are independent; evaluation on
    the corresponding products of biorthogonal vectors gives the Kronecker
    pairing. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma one_homE omega v : one_hom omega v = omega [tuple v].
Proof. by []. Qed.
(** Source for [one_hom_linear]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma one_hom_linear : linear one_hom.
Proof.
move=> a phi psi; apply: hom_ext => v.
by rewrite hom_addE hom_scaleE !one_homE form_addE form_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (A_m V W 1) (Hom V W) *:%R one_hom one_hom_linear.
(** Source for [one_hom_injective]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma one_hom_injective : injective one_hom.
Proof.
move=> phi psi h; apply: form_ext => /tupleP [v t].
rewrite (tuple0 t); exact (congr1 (fun f : Hom V W => f v) h).
Qed.
End OneFormLinear.
