(** Federer (1969), 1.9.1, pp. 41-42: the graded universal property of the
    symmetric algebra, independent of its construction. The sources use real
    scalars; the statements here work over any field. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP AlgebraUP GradedAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section GradedUniversalProperty.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable G : grading A.
Variable iota : {linear V -> A}.

(** Source for [is_graded_symmetric_algebra]: Federer 1.9.1, p. 41, the
    final universal-property paragraphs. In words: Abstract specification:
    each linear map into degree one of a commutative graded unital algebra
    has a unique graded extension. *)
Definition is_graded_symmetric_algebra : Prop :=
  forall (B : algebra K) (H : grading B),
    commutative (alg_mul B) -> graded_product H (alg_mul B) ->
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
Hypotheses (ca : commutative (alg_mul A))
  (cb : commutative (alg_mul B))
  (ha : graded_product G (alg_mul A))
  (hb : graded_product H (alg_mul B))
  (hi : forall v, homogeneous G 1 (iota v))
  (hi' : forall v, homogeneous H 1 (iota' v))
  (hu : is_graded_symmetric_algebra G iota)
  (hu' : is_graded_symmetric_algebra H iota').

(** Source for [graded_symmetric_algebra_unique]: Federer 1.9.1, p. 41, the
    final universal-property paragraphs. In words: The universal property
    determines the algebra up to a unique unit-preserving graded isomorphism
    extending the generators. *)
Theorem graded_symmetric_algebra_unique :
  exists (f : algebra_map A B) (g : algebra_map B A),
    (forall v, f (iota v) = iota' v) /\
    (forall v, g (iota' v) = iota v) /\
    preserves_grading G H f /\ preserves_grading H G g /\
    cancel f g /\ cancel g f /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = iota' v) -> preserves_grading G H h ->
      forall x, h x = f x).
Proof.
have [f [fi [fg fu]]] := @hu B H cb hb iota' hi'.
have [g [gi [gg gu]]] := @hu' A G ca ha iota hi.
have [u [ui [ug uu]]] := @hu A G ca ha iota hi.
have [v [vi [vg vu]]] := @hu' B H cb hb iota' hi'.
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
