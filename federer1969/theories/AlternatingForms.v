(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import Exterior TensorPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1, first paragraph: an m-linear alternating function has
    domain V^m. A tuple is the actual ordered m-tuple of arguments.
    Linearity at a position is expressed by its prefix and suffix, keeping
    every other entry fixed. This includes the vacuous condition m=0. *)
Section TupleContexts.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.

(** Source for [context_tupleP]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma context_tupleP (s t : seq V) (h : size (s ++ (0 : V) :: t) == m) v :
  size (s ++ v :: t) == m.
Proof. move: h; by rewrite !size_cat. Qed.
(** Source for [context_tuple]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Definition or
    construction used to formalise this passage. *)
Definition context_tuple s t h v : m.-tuple V := Tuple (@context_tupleP s t h v).
Arguments context_tuple s t h v : clear implicits.
(** Source for [context_tupleE]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma context_tupleE s t h v : val (context_tuple s t h v) = s ++ v :: t.
Proof. by []. Qed.
End TupleContexts.
Arguments context_tuple {K V m} s t h v.

Section Forms.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation F := (GRing.Lmodule.clone K (m.-tuple V -> W) _).

(** Source for [m_linear]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Definition or
    construction used to formalise this passage. *)
Definition m_linear (f : m.-tuple V -> W) : Prop :=
  forall (s t : seq V) (h : size (s ++ (0 : V) :: t) == m),
    linear (fun v => f (context_tuple s t h v)).
(** Source for [alternating]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Definition or
    construction used to formalise this passage. *)
Definition alternating (f : m.-tuple V -> W) : Prop :=
  forall t : m.-tuple V, ~~ uniq t -> f t = 0.
(** Source for [form_pred]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Definition or
    construction used to formalise this passage. *)
Definition form_pred (f : F) := `[< m_linear f /\ alternating f >].

(** Source for [A_m]: Federer (1969), 1.4.1, pp. 16-17, opening definition
    of alternating forms. In words: An m-linear map is alternating when it
    vanishes whenever two distinct argument positions contain the same
    vector; these forms make up A^m(V,W). Definition or construction used to
    formalise this passage. *)
Record A_m := AlternatingForm {
  form_fun : m.-tuple V -> W;
  form_proof : form_pred form_fun
}.
Coercion form_fun : A_m >-> Funclass.
(** Source for [form_rect]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Definition or
    construction used to formalise this passage. *)
Definition form_rect (P : A_m -> Type)
    (h : forall f hf, P (@AlternatingForm f hf)) (z : A_m) : P z :=
  match z as z' return P z' with @AlternatingForm f hf => h f hf end.
HB.instance Definition _ := [isSub for form_fun by form_rect].
HB.instance Definition _ := [Choice of A_m by <:].

(** Source for [form_closed]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma form_closed : GRing.submod_closed form_pred.
Proof.
split.
- apply/asboolP; split; last by move=> t _.
  by move=> s t h a x y; rewrite /= scaler0 add0r.
- move=> a f g /asboolP [hf af] /asboolP [hg ag]; apply/asboolP; split.
  + move=> s t h b x y.
    change (a *: f (context_tuple s t h (b *: x + y)) + g (context_tuple s t h (b *: x + y)) =
      b *: (a *: f (context_tuple s t h x) + g (context_tuple s t h x)) +
        (a *: f (context_tuple s t h y) + g (context_tuple s t h y))).
    rewrite (hf s t h) (hg s t h) !scalerDr !scalerA addrACA.
    by rewrite [a * b]mulrC.
  + move=> t ht; change (a *: f t + g t = 0).
    by rewrite af // ag // scaler0 add0r.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build K F form_pred A_m form_closed.

(** Source for [form_multilinear]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma form_multilinear (f : A_m) : m_linear f.
Proof. exact: (proj1 (elimT (asboolP _) (form_proof f))). Qed.
(** Source for [form_alternating]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma form_alternating (f : A_m) : alternating f.
Proof. exact: (proj2 (elimT (asboolP _) (form_proof f))). Qed.
(** Source for [form_ext]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma form_ext (f g : A_m) : f =1 g -> f = g.
Proof. move=> h; apply: val_inj; exact: funext h. Qed.
(** Source for [form_zeroE]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma form_zeroE t : (0 : A_m) t = 0.
Proof. by []. Qed.
(** Source for [form_addE]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma form_addE (f g : A_m) t : (f+g) t = f t + g t.
Proof. by []. Qed.
(** Source for [form_scaleE]: Federer (1969), 1.4.1, pp. 16-17, opening
    definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma form_scaleE a (f : A_m) t : (a *: f) t = a *: f t.
Proof. by []. Qed.

(** Federer 1.4.1: the repetition condition is exactly equality of two
    arguments at distinct positions, as stated in the book. *)
(** Source for [alternating_repetition]: Federer (1969), 1.4.1, pp. 16-17,
    opening definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma alternating_repetition (f : m.-tuple V -> W) : alternating f <->
  forall (t : m.-tuple V) (i j : 'I_m), i != j -> tnth t i = tnth t j -> f t = 0.
Proof.
split.
- move=> hf t i j hij ht; apply: hf; apply/negP=> hu.
  have hi : injective (tnth t) by apply/tuple_uniqP; exact: hu.
  by move: hij; rewrite (hi i j ht) eqxx.
- move=> hf t ht.
  have hn : ~~ injectiveb (tnth t).
    apply/negP=> /injectiveP hi.
    have hu : uniq t by apply/tuple_uniqP; exact: hi.
    by move: ht; rewrite hu.
  have /injectivePn [i [j hij heq]] := hn.
  exact: hf t i j hij heq.
Qed.

(** Source for [form_repeated_arguments]: Federer (1969), 1.4.1, pp. 16-17,
    opening definition of alternating forms. In words: An m-linear map is
    alternating when it vanishes whenever two distinct argument positions
    contain the same vector; these forms make up A^m(V,W). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma form_repeated_arguments (f : A_m) (t : m.-tuple V) (i j : 'I_m) :
  i != j -> tnth t i = tnth t j -> f t = 0.
Proof. exact: (proj1 (alternating_repetition f) (form_alternating f) t i j). Qed.
End Forms.
Arguments A_m {K} V W m.
