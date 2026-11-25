(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import TensorUP Bilinear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1: Hom(V,W) is the vector space of all linear maps, also
    when either space has infinite dimension. Operations are pointwise. *)
Section HomSpace.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation F := (GRing.Lmodule.clone K (V -> W) _).
(** Source for [hom_pred]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition hom_pred (f : V -> W) := `[< linear f >].

(** Source for [Hom]: Federer (1969), 1.4.1, p. 17, factorisation paragraph
    and first displayed isomorphism. In words: Every alternating m-linear
    map factors uniquely through the m-th exterior power, giving the
    isomorphism between forms and linear maps on that power. Definition or
    construction used to formalise this passage. *)
Record Hom := HomMap {
  hom_fun : V -> W;
  hom_proof : hom_pred hom_fun
}.
Coercion hom_fun : Hom >-> Funclass.
(** Source for [hom_rect]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition hom_rect (P : Hom -> Type)
    (h : forall f hf, P (@HomMap f hf)) (z : Hom) : P z :=
  match z as z' return P z' with @HomMap f hf => h f hf end.
HB.instance Definition _ := [isSub for hom_fun by hom_rect].
HB.instance Definition _ := [Choice of Hom by <:].

(** Source for [hom_closed]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_closed : GRing.submod_closed (fun f : F => `[< linear f >]).
Proof.
split.
- apply/asboolP=> a x y; by rewrite /= scaler0 add0r.
- move=> a f g /asboolP hf /asboolP hg; apply/asboolP=> b x y.
  change (a *: f (b *: x + y) + g (b *: x + y) =
    b *: (a *: f x + g x) + (a *: f y + g y)).
  rewrite hf hg !scalerDr !scalerA addrACA.
  by rewrite [a * b]mulrC.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  K F (fun f : F => `[< linear f >]) Hom hom_closed.

(** Source for [hom_linear]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_linear (f : Hom) : linear (hom_fun f).
Proof. apply/asboolP; exact: hom_proof. Qed.
HB.instance Definition _ (f : Hom) := GRing.isLinear.Build K V W *:%R
  (hom_fun f) (hom_linear f).

(** Source for [hom_of_linear]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition hom_of_linear (f : {linear V -> W}) : Hom :=
  @HomMap f (introT (asboolP _) (linearP f)).
(** Source for [hom_as_linear]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition hom_as_linear (f : Hom) : {linear V -> W} :=
  GRing.Linear.clone _ _ _ _ (hom_fun f) _.

(** Source for [hom_ext]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_ext (f g : Hom) : f =1 g -> f = g.
Proof. move=> h; apply: val_inj; exact: funext h. Qed.
(** Source for [hom_zeroE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_zeroE x : (0 : Hom) x = 0.
Proof. by []. Qed.
(** Source for [hom_addE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_addE (f g : Hom) x : (f+g) x = f x + g x.
Proof. by []. Qed.
(** Source for [hom_scaleE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_scaleE a (f : Hom) x : (a *: f) x = a *: f x.
Proof. by []. Qed.
(** Source for [hom_eval_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma hom_eval_linear x : linear (fun f : Hom => f x).
Proof. by move=> a f g; rewrite hom_addE hom_scaleE. Qed.

(** Source for [hom_of_linearE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_of_linearE (f : {linear V -> W}) x : hom_of_linear f x = f x.
Proof. by []. Qed.
(** Source for [hom_as_linearE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_as_linearE (f : Hom) x : hom_as_linear f x = f x.
Proof. by []. Qed.
(** Source for [hom_of_asK]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_of_asK (f : Hom) : hom_of_linear (hom_as_linear f) = f.
Proof. apply: hom_ext => x; by []. Qed.
End HomSpace.
Arguments Hom {K} V W.

Section HomComposition.
Variable K : fieldType.
Variables U V W : lmodType K.
(** Source for [hom_comp]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition hom_comp (f : Hom V W) (g : Hom U V) : Hom U W :=
  hom_of_linear (linear_comp (hom_as_linear f) (hom_as_linear g)).
(** Source for [hom_compE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_compE f g x : hom_comp f g x = f (g x).
Proof. by []. Qed.
(** Source for [hom_precompose_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma hom_precompose_linear (g : Hom U V) : linear (fun f : Hom V W => hom_comp f g).
Proof. move=> a f h; apply: hom_ext => x; by rewrite !hom_compE !hom_addE !hom_scaleE. Qed.
(** Source for [hom_postcompose_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma hom_postcompose_linear (f : Hom V W) : linear (fun g : Hom U V => hom_comp f g).
Proof.
move=> a g h; apply: hom_ext => x; rewrite !hom_compE !hom_addE !hom_scaleE.
exact: hom_linear.
Qed.
End HomComposition.
