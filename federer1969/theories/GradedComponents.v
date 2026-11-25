(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP GradedAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.2.1 and 1.3.1: the actual vector space
    A_n, not merely the predicate that a vector is homogeneous of degree n. *)
Section Components.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.
Variable n : nat.

(** Source for [graded_component]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Record graded_component := Component {
  component_val : V;
  component_proof : grade G n component_val == component_val
}.
(** Source for [component_rect]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Definition component_rect (P : graded_component -> Type)
    (h : forall x hx, P (@Component x hx)) (z : graded_component) : P z :=
  match z as z' return P z' with @Component x hx => h x hx end.
HB.instance Definition _ := [isSub for component_val by component_rect].
HB.instance Definition _ := [Choice of graded_component by <:].

(** Source for [component_closed]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma component_closed : GRing.submod_closed (fun x : V => grade G n x == x).
Proof.
split; first by apply/eqP; exact: linear0.
move=> a x y /eqP hx /eqP hy; apply/eqP.
by rewrite linearP hx hy.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  K V (fun x : V => grade G n x == x) graded_component component_closed.

(** Source for [component_val_linear]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma component_val_linear : linear component_val.
Proof.
move=> a x y; change (val (a *: x + y) = a *: val x + val y).
exact: linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K graded_component V
  *:%R component_val component_val_linear.

(** Source for [component_homogeneous]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma component_homogeneous (x : graded_component) : homogeneous G n (component_val x).
Proof. apply/eqP; exact: component_proof. Qed.

(** Source for [component]: Federer (1969), 1.2.1, p. 11, opening paragraph
    and degree condition. In words: A graded algebra is a vector space with
    a specified direct sum indexed by nonnegative integers and a bilinear
    multiplication that adds degrees. Definition or construction used to
    formalise this passage. *)
Definition component (x : V) : graded_component :=
  @Component (grade G n x) (introT eqP (homogeneous_grade G n x)).

(** Source for [componentE]: Federer (1969), 1.2.1, p. 11, opening paragraph
    and degree condition. In words: A graded algebra is a vector space with
    a specified direct sum indexed by nonnegative integers and a bilinear
    multiplication that adds degrees. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma componentE x : component_val (component x) = grade G n x.
Proof. by []. Qed.

(** Source for [component_linear]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma component_linear : linear component.
Proof. by move=> a x y; apply/val_inj; rewrite !linearP /= linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V graded_component
  *:%R component component_linear.

(** Source for [componentK]: Federer (1969), 1.2.1, p. 11, opening paragraph
    and degree condition. In words: A graded algebra is a vector space with
    a specified direct sum indexed by nonnegative integers and a bilinear
    multiplication that adds degrees. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma componentK : cancel component_val component.
Proof. by move=> x; apply/val_inj; exact: component_homogeneous. Qed.
End Components.
Arguments component_val {K V G n} _.
Arguments component {K V} G n _.

Section ComponentMap.
Variable K : fieldType.
Variables V W : lmodType K.
Variables (G : grading V) (H : grading W).
Variable f : {linear V -> W}.
Hypothesis hf : preserves_grading G H f.
Variable n : nat.

(** Source for [component_map]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Definition component_map (x : graded_component G n) : graded_component H n :=
  @Component K W H n (f (component_val x))
    (introT eqP (hf (component_homogeneous x))).

(** Source for [component_mapE]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma component_mapE x : component_val (component_map x) = f (component_val x).
Proof. by []. Qed.
(** Source for [component_map_linear]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma component_map_linear : linear component_map.
Proof. by move=> a x y; apply/val_inj; rewrite !linearP /= linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (graded_component G n)
  (graded_component H n) *:%R component_map component_map_linear.
End ComponentMap.
