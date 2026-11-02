(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP GradedAlgebra GradedSums GradedComponents.
From Federer Require Import Hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1: Hom^m(A,W) consists of the linear maps vanishing on
    every homogeneous summand of degree different from m. The following
    construction applies to any internally graded vector space. *)
Section HomogeneousMaps.
Variable K : fieldType.
Variables V W : lmodType K.
Variable G : grading V.
Variable m : nat.
Local Notation H := (GRing.Lmodule.clone K (Hom V W) _).
(** Source for [hom_degree]: Federer (1969), 1.4.1, p. 17, second displayed
    isomorphism. In words: Forms of degree m identify with linear maps on
    the whole exterior algebra that vanish on every homogeneous component of
    degree different from m. Definition or construction used to formalise
    this passage. *)
Definition hom_degree (f : Hom V W) : Prop :=
  forall n x, n != m -> homogeneous G n x -> f x = 0.
(** Source for [hom_degree_pred]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Definition or construction used to
    formalise this passage. *)
Definition hom_degree_pred f := `[< hom_degree f >].
(** Source for [Hom_m]: Federer (1969), 1.4.1, p. 17, second displayed
    isomorphism. In words: Forms of degree m identify with linear maps on
    the whole exterior algebra that vanish on every homogeneous component of
    degree different from m. Definition or construction used to formalise
    this passage. *)
Record Hom_m := HomogeneousHom {
  hom_m_val : Hom V W;
  hom_m_proof : hom_degree_pred hom_m_val
}.
Coercion hom_m_val : Hom_m >-> Hom.
(** Source for [hom_m_rect]: Federer (1969), 1.4.1, p. 17, second displayed
    isomorphism. In words: Forms of degree m identify with linear maps on
    the whole exterior algebra that vanish on every homogeneous component of
    degree different from m. Definition or construction used to formalise
    this passage. *)
Definition hom_m_rect (P : Hom_m -> Type)
    (h : forall f hf, P (@HomogeneousHom f hf)) (z : Hom_m) : P z :=
  match z as z' return P z' with @HomogeneousHom f hf => h f hf end.
HB.instance Definition _ := [isSub for hom_m_val by hom_m_rect].
HB.instance Definition _ := [Choice of Hom_m by <:].

(** Source for [hom_degree_closed]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma hom_degree_closed : GRing.submod_closed hom_degree_pred.
Proof.
split.
- apply/asboolP=> n x hn hx; exact: hom_zeroE.
- move=> a f g /asboolP hf /asboolP hg; apply/asboolP=> n x hn hx.
  by rewrite hom_addE hom_scaleE (hf n x hn hx) (hg n x hn hx) scaler0 add0r.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  K H hom_degree_pred Hom_m hom_degree_closed.

(** Source for [hom_m_degree]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma hom_m_degree (f : Hom_m) : hom_degree f.
Proof. apply/asboolP; exact: hom_m_proof. Qed.
(** Source for [hom_m_ext]: Federer (1969), 1.4.1, p. 17, second displayed
    isomorphism. In words: Forms of degree m identify with linear maps on
    the whole exterior algebra that vanish on every homogeneous component of
    degree different from m. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma hom_m_ext (f g : Hom_m) : f =1 g -> f = g.
Proof. move=> h; apply: val_inj; exact: hom_ext h. Qed.
(** Source for [hom_m_zeroE]: Federer (1969), 1.4.1, p. 17, second displayed
    isomorphism. In words: Forms of degree m identify with linear maps on
    the whole exterior algebra that vanish on every homogeneous component of
    degree different from m. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma hom_m_zeroE x : (0 : Hom_m) x = 0.
Proof. by []. Qed.
(** Source for [hom_m_addE]: Federer (1969), 1.4.1, p. 17, second displayed
    isomorphism. In words: Forms of degree m identify with linear maps on
    the whole exterior algebra that vanish on every homogeneous component of
    degree different from m. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma hom_m_addE (f g : Hom_m) x : (f+g) x = f x + g x.
Proof. by []. Qed.
(** Source for [hom_m_scaleE]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma hom_m_scaleE a (f : Hom_m) x : (a *: f) x = a *: f x.
Proof. by []. Qed.

(** Source for [hom_m_projection]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma hom_m_projection (f : Hom_m) x : f (grade G m x) = f x.
Proof.
elim/(graded_induction (G:=G)): x => [|x y hx hy|n x hx].
- by rewrite !linear0.
- rewrite !linearD.
  change (f (grade G m x) + f (grade G m y) = f x + f y).
  by rewrite hx hy.
- rewrite (grade_homogeneous m hx); case hmn: (m == n).
  + by [].
  + rewrite linear0; symmetry; apply: hom_m_degree hx.
    by rewrite eq_sym hmn.
Qed.

(** Source for [homogeneous_restrict]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Definition or construction used to
    formalise this passage. *)
Definition homogeneous_restrict (f : Hom_m) : Hom (graded_component G m) W :=
  hom_of_linear (linear_comp (hom_as_linear f)
    (GRing.Linear.clone _ _ _ _ (@component_val K V G m) _)).

(** Source for [homogeneous_extend_degree]: Federer (1969), 1.4.1, p. 17,
    second displayed isomorphism. In words: Forms of degree m identify with
    linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_extend_degree (f : Hom (graded_component G m) W) :
  hom_degree (hom_of_linear (linear_comp (hom_as_linear f)
    (GRing.Linear.clone _ _ _ _ (component G m) _))).
Proof.
move=> n x hn hx.
change (f (component G m x) = 0).
have hz : component G m x = 0.
  apply: val_inj; change (grade G m x = (0 : V)).
  rewrite (grade_homogeneous m hx).
  by rewrite eq_sym (negPf hn).
by rewrite hz linear0.
Qed.
(** Source for [homogeneous_extend]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Definition or construction used to
    formalise this passage. *)
Definition homogeneous_extend (f : Hom (graded_component G m) W) : Hom_m :=
  @HomogeneousHom
    (hom_of_linear (linear_comp (hom_as_linear f)
      (GRing.Linear.clone _ _ _ _ (component G m) _)))
    (introT (asboolP _) (homogeneous_extend_degree f)).

(** Source for [homogeneous_restrictE]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma homogeneous_restrictE (f : Hom_m) x : homogeneous_restrict f x = f (component_val x).
Proof. by []. Qed.
(** Source for [homogeneous_extendE]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma homogeneous_extendE f x : homogeneous_extend f x = f (component G m x).
Proof. by []. Qed.
(** Source for [homogeneous_restrictK]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma homogeneous_restrictK : cancel homogeneous_restrict homogeneous_extend.
Proof. move=> f; apply: hom_m_ext => x; exact: hom_m_projection. Qed.
(** Source for [homogeneous_extendK]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma homogeneous_extendK : cancel homogeneous_extend homogeneous_restrict.
Proof. move=> f; apply: hom_ext => x; change (f (component G m (component_val x)) = f x); by rewrite componentK. Qed.

(** Source for [homogeneous_restrict_linear]: Federer (1969), 1.4.1, p. 17,
    second displayed isomorphism. In words: Forms of degree m identify with
    linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_restrict_linear : linear homogeneous_restrict.
Proof.
move=> a f g; apply: hom_ext => x.
by rewrite homogeneous_restrictE hom_m_addE hom_m_scaleE hom_addE hom_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K Hom_m (Hom (graded_component G m) W)
  *:%R homogeneous_restrict homogeneous_restrict_linear.
(** Source for [homogeneous_extend_linear]: Federer (1969), 1.4.1, p. 17,
    second displayed isomorphism. In words: Forms of degree m identify with
    linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_extend_linear : linear homogeneous_extend.
Proof.
move=> a f g; apply: hom_m_ext => x.
by rewrite homogeneous_extendE hom_addE hom_scaleE hom_m_addE hom_m_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom (graded_component G m) W) Hom_m
  *:%R homogeneous_extend homogeneous_extend_linear.
End HomogeneousMaps.
Arguments Hom_m {K V} W G m.
