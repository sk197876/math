(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.1, universal mapping property and uniqueness up to isomorphism.
    This construction-independent version asks that generator squares vanish;
    the graded anticommutative version follows in characteristic different
    from two. The square-zero version also applies in characteristic two. *)
Section UniversalProperty.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.

(** Source for [is_exterior_algebra]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Definition or construction
    used to formalise this passage. The square-zero target condition is used
    in the proof on p. 14. The abstract ungraded square-zero property
    formalised here is stronger than the printed graded anticommutative
    formulation and also works in characteristic two. *)
Definition is_exterior_algebra : Prop :=
  (forall v, alg_mul A (iota v) (iota v) = 0) /\
  (forall (B : algebra K) (f : {linear V -> B}),
    (forall v, alg_mul B (f v) (f v) = 0) ->
    exists g : algebra_map A B,
      (forall v, g (iota v) = f v) /\
      (forall h : algebra_map A B,
        (forall v, h (iota v) = f v) -> forall x, h x = g x)).

(** Source for [exterior_algebra_ext]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Supporting lemma for this
    passage; not separately stated in the book. The square-zero target
    condition is used in the proof on p. 14. The abstract ungraded
    square-zero property formalised here is stronger than the printed graded
    anticommutative formulation and also works in characteristic two. *)
Lemma exterior_algebra_ext (H : is_exterior_algebra) (B : algebra K)
    (f g : algebra_map A B) :
  (forall v, f (iota v) = g (iota v)) -> forall x, f x = g x.
Proof.
move=> e; have [hs hu] := H.
have hg : forall v,
    alg_mul B (linear_comp g iota v) (linear_comp g iota v) = 0.
  by move=> v; rewrite /= -algebra_map_mul hs linear0.
have [h [hi hh]] := hu B (linear_comp g iota) hg.
by move=> x; rewrite (hh f e) (hh g (fun v => erefl _)).
Qed.
End UniversalProperty.
Arguments exterior_algebra_ext {K V A iota} H {B} f g _ x.

Section Uniqueness.
Variable K : fieldType.
Variable V : lmodType K.
Variables A B : algebra K.
Variables (iota : {linear V -> A}) (iota' : {linear V -> B}).
Hypotheses (H : is_exterior_algebra iota) (H' : is_exterior_algebra iota').

(** Source for [exterior_algebra_unique]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: The tensor-algebra
    extension factors through the exterior quotient precisely when the
    images of the generators have square zero. Supporting lemma for this
    passage; not separately stated in the book. The square-zero target
    condition is used in the proof on p. 14. The abstract ungraded
    square-zero property formalised here is stronger than the printed graded
    anticommutative formulation and also works in characteristic two. *)
Theorem exterior_algebra_unique :
  exists (f : algebra_map A B) (g : algebra_map B A),
    (forall v, f (iota v) = iota' v) /\
    (forall v, g (iota' v) = iota v) /\
    cancel f g /\ cancel g f /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = iota' v) -> forall x, h x = f x).
Proof.
have [hs hu] := H; have [hs' hu'] := H'.
have [f [fi fu]] := hu B iota' hs'.
have [g [gi gu]] := hu' A iota hs.
exists f, g; split=> //; split=> //; split.
  apply: (exterior_algebra_ext H (algebra_comp g f) (algebra_id A)) => v /=.
  by rewrite fi gi.
split.
  apply: (exterior_algebra_ext H' (algebra_comp f g) (algebra_id B)) => v /=.
  by rewrite gi fi.
exact: fu.
Qed.
End Uniqueness.

(** Federer 1.3.1, characterisation among graded anticommutative algebras:
    this is the literal graded universal property, kept separate from the
    stronger square-zero property above and from every construction. *)
Section GradedUniversalProperty.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable G : grading A.
Variable iota : {linear V -> A}.

(** Source for [is_graded_exterior_algebra]: Federer (1969), 1.3.1, p. 14,
    universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Definition
    or construction used to formalise this passage. *)
Definition is_graded_exterior_algebra : Prop :=
  forall (B : algebra K) (H : grading B),
    graded_product H (alg_mul B) -> graded_anticommutative H (alg_mul B) ->
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
  (hca : graded_anticommutative G (alg_mul A))
  (hcb : graded_anticommutative H (alg_mul B))
  (hi : forall v, homogeneous G 1 (iota v))
  (hi' : forall v, homogeneous H 1 (iota' v))
  (hu : is_graded_exterior_algebra G iota)
  (hu' : is_graded_exterior_algebra H iota').

(** Source for [graded_exterior_algebra_unique]: Federer (1969), 1.3.1, p.
    14, universal mapping property and its proof. In words: Linear maps into
    degree one of an anticommutative associative unital graded algebra
    extend uniquely to unit-preserving graded algebra maps; square-zero
    images make the tensor extension factor through the quotient. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem graded_exterior_algebra_unique :
  exists (f : algebra_map A B) (g : algebra_map B A),
    (forall v, f (iota v) = iota' v) /\
    (forall v, g (iota' v) = iota v) /\
    preserves_grading G H f /\ preserves_grading H G g /\
    cancel f g /\ cancel g f /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = iota' v) -> preserves_grading G H h ->
      forall x, h x = f x).
Proof.
have [f [fi [fg fu]]] := @hu B H hb hcb iota' hi'.
have [g [gi [gg gu]]] := @hu' A G ha hca iota hi.
have [u [ui [ug uu]]] := @hu A G ha hca iota hi.
have [v [vi [vg vu]]] := @hu' B H hb hcb iota' hi'.
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
