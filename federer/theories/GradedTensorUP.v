(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP AlgebraUP GradedAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.3: the graded universal property is independent of the
    construction. Uniqueness requires only this property, not the stronger
    universal property for ungraded target algebras. *)
Section GradedUniversalProperty.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable G : grading A.
Variable iota : {linear V -> A}.

(** Source for [is_graded_tensor_algebra]: Federer (1969), 1.2.3, p. 12,
    universal mapping property in the last two paragraphs. In words: Every
    linear map into the degree-one part of a unital associative graded
    algebra extends uniquely to a unit-preserving graded algebra
    homomorphism. Definition or construction used to formalise this passage. *)
Definition is_graded_tensor_algebra : Prop :=
  forall (B : algebra K) (H : grading B),
    graded_product H (alg_mul B) ->
    forall f : {linear V -> B}, (forall v, homogeneous H 1 (f v)) ->
    exists g : algebra_map A B,
      (forall v, g (iota v) = f v) /\ preserves_grading G H g /\
      (forall h : algebra_map A B,
        (forall v, h (iota v) = f v) -> preserves_grading G H h ->
        forall x, h x = g x).
End GradedUniversalProperty.

Section GradedUniqueness.
Variable K : fieldType.
Variable V : lmodType K.
Variables A B : algebra K.
Variables (G : grading A) (H : grading B).
Variables (iota : {linear V -> A}) (iota' : {linear V -> B}).
Hypotheses (ha : graded_product G (alg_mul A))
  (hb : graded_product H (alg_mul B))
  (hi : forall v, homogeneous G 1 (iota v))
  (hi' : forall v, homogeneous H 1 (iota' v))
  (hu : is_graded_tensor_algebra G iota)
  (hu' : is_graded_tensor_algebra H iota').

(** Source for [graded_tensor_algebra_unique]: Federer (1969), 1.2.3, p. 12,
    universal mapping property in the last two paragraphs. In words: Every
    linear map into the degree-one part of a unital associative graded
    algebra extends uniquely to a unit-preserving graded algebra
    homomorphism. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem graded_tensor_algebra_unique :
  exists (f : algebra_map A B) (g : algebra_map B A),
    (forall v, f (iota v) = iota' v) /\
    (forall v, g (iota' v) = iota v) /\
    preserves_grading G H f /\ preserves_grading H G g /\
    cancel f g /\ cancel g f /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = iota' v) -> preserves_grading G H h ->
      forall x, h x = f x).
Proof.
have [f [fi [fg fu]]] := @hu B H hb iota' hi'.
have [g [gi [gg gu]]] := @hu' A G ha iota hi.
have [u [ui [ug uu]]] := @hu A G ha iota hi.
have [v [vi [vg vu]]] := @hu' B H hb iota' hi'.
have gf : forall a, algebra_comp g f (iota a) = iota a.
  by move=> a; change (g (f (iota a)) = iota a); rewrite fi gi.
have fg' : forall a, algebra_comp f g (iota' a) = iota' a.
  by move=> a; change (f (g (iota' a)) = iota' a); rewrite gi fi.
have gfg : preserves_grading G G (algebra_comp g f).
  by move=> n x hx; apply: gg; exact: fg hx.
have fgg : preserves_grading H H (algebra_comp f g).
  by move=> n x hx; apply: fg; exact: gg hx.
exists f, g; split=> //; split=> //; split=> //; split=> //; split.
  move=> x; exact: eq_trans (uu (algebra_comp g f) gf gfg x)
    (esym (uu (algebra_id A) (fun _ => erefl _) (fun _ _ h => h) x)).
split; last exact: fu.
move=> x; exact: eq_trans (vu (algebra_comp f g) fg' fgg x)
  (esym (vu (algebra_id B) (fun _ => erefl _) (fun _ _ h => h) x)).
Qed.
End GradedUniqueness.
