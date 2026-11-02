(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Exterior.
From Federer Require Import Hom HomogeneousHom AlternatingForms AlternatingWords
  AlternatingExtension AlternatingIsomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1, the pairing paragraph: <xi,h>=h(xi); the same notation
    for a form and for its corresponding homogeneous linear map has the
    same value under the two isomorphisms. *)
Section Pairing.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation P := (exterior_power V m).
Local Notation A := (A_m V W m).
Local Notation H := (Hom_m W (exterior_grading V) m).
(** Source for [pairing_hom]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Definition or
    construction used to formalise this passage. *)
Definition pairing_hom (x : P) (h : Hom P W) := h x.
(** Source for [pairing]: Federer (1969), 1.4.1, p. 17, paragraph extending
    the evaluation notation. In words: The pairing is evaluation of a linear
    map on an m-vector and has the same value under the identifications with
    forms and homogeneous linear maps. Definition or construction used to
    formalise this passage. *)
Definition pairing (x : P) (f : A) := form_to_hom f x.
(** Source for [pairing_homogeneous]: Federer (1969), 1.4.1, p. 17,
    paragraph extending the evaluation notation. In words: The pairing is
    evaluation of a linear map on an m-vector and has the same value under
    the identifications with forms and homogeneous linear maps. Definition
    or construction used to formalise this passage. *)
Definition pairing_homogeneous (x : P) (h : H) := h (component_val x).
(** Source for [pairing_homE]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma pairing_homE x h : pairing_hom x h = h x.
Proof. by []. Qed.
(** Source for [pairing_form_hom]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma pairing_form_hom x f : pairing x f = pairing_hom x (form_to_hom f).
Proof. by []. Qed.
(** Source for [pairing_form_homogeneous]: Federer (1969), 1.4.1, p. 17,
    paragraph extending the evaluation notation. In words: The pairing is
    evaluation of a linear map on an m-vector and has the same value under
    the identifications with forms and homogeneous linear maps. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma pairing_form_homogeneous x f : pairing x f = pairing_homogeneous x (form_homogeneous f).
Proof. by []. Qed.
(** Source for [pairing_hom_identification]: Federer (1969), 1.4.1, p. 17,
    paragraph extending the evaluation notation. In words: The pairing is
    evaluation of a linear map on an m-vector and has the same value under
    the identifications with forms and homogeneous linear maps. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma pairing_hom_identification x h : pairing x (hom_to_form h) = pairing_hom x h.
Proof. by rewrite /pairing hom_to_formK. Qed.
(** Source for [pairing_homogeneous_identification]: Federer (1969), 1.4.1,
    p. 17, paragraph extending the evaluation notation. In words: The
    pairing is evaluation of a linear map on an m-vector and has the same
    value under the identifications with forms and homogeneous linear maps.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma pairing_homogeneous_identification x h :
  pairing x (homogeneous_form h) = pairing_homogeneous x h.
Proof. by rewrite /pairing /form_to_hom homogeneous_formK. Qed.
(** Source for [pairing_tuple]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma pairing_tuple (t : m.-tuple V) f : pairing (e_lambda idfun t) f = f t.
Proof. exact: form_to_hom_tuple. Qed.
(** Source for [pairing_bilinear]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma pairing_bilinear : bilinear pairing.
Proof.
split.
- move=> f; exact: hom_linear.
- move=> x a f g; rewrite /pairing linearP hom_addE hom_scaleE; by [].
Qed.
(** Source for [pairing_ext]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma pairing_ext (f g : A) : (forall x, pairing x f = pairing x g) -> f = g.
Proof.
move=> h; have he : form_to_hom f = form_to_hom g by apply: hom_ext.
exact (can_inj (@form_to_homK K V W m) he).
Qed.
End Pairing.
