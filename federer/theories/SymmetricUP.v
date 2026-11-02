(** Federer (1969), 1.9.1, p. 41: abstract symmetric-algebra extension and
    uniqueness. The ungraded property here strengthens the printed graded
    property; targets must remain commutative and unital. Arbitrary fields
    are allowed instead of the sources' real scalars. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP AlgebraUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section UniversalProperty.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable iota : {linear V -> A}.

(** Source for [is_symmetric_algebra]: Federer 1.9.1, p. 41,
    universal-property paragraphs. In words: Abstract specification of unique extension to commutative unital
    targets; commutativity of the source is required separately.
    This ungraded consequence is a local strengthening of the graded
    source statement, proved from the abstract extension property. *)
Definition is_symmetric_algebra : Prop :=
  forall (B : algebra K), commutative (alg_mul B) ->
  forall f : {linear V -> B},
  exists g : algebra_map A B,
    (forall v, g (iota v) = f v) /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = f v) -> forall x, h x = g x).

(** Source for [symmetric_algebra_ext]: Federer 1.9.1, p. 41,
    universal-property paragraphs. In words: Supporting extensionality: two algebra maps to a commutative
    target agree if they agree on every generator.
    This ungraded consequence is a local strengthening of the graded
    source statement, proved from the abstract extension property. *)
Lemma symmetric_algebra_ext (H : is_symmetric_algebra) (B : algebra K)
    (hB : commutative (alg_mul B)) (f g : algebra_map A B) :
  (forall v, f (iota v) = g (iota v)) -> forall x, f x = g x.
Proof.
move=> e.
have [h [hi hu]] := H B hB (linear_comp g iota).
by move=> x; rewrite (hu f e) (hu g (fun v => erefl _)).
Qed.
End UniversalProperty.
Arguments symmetric_algebra_ext {K V A iota} H {B} hB f g _ x.

Section Uniqueness.
Variable K : fieldType.
Variable V : lmodType K.
Variables A B : algebra K.
Variables (iota : {linear V -> A}) (iota' : {linear V -> B}).
Hypotheses (hA : commutative (alg_mul A))
  (hB : commutative (alg_mul B))
  (H : is_symmetric_algebra iota) (H' : is_symmetric_algebra iota').

(** Source for [symmetric_algebra_unique]: Federer 1.9.1, p. 41,
    universal-property paragraphs. In words: Unique unit-preserving isomorphism between two commutative
    algebras with the same universal property.
    This ungraded consequence is a local strengthening of the graded
    source statement, proved from the abstract extension property. *)
Theorem symmetric_algebra_unique :
  exists (f : algebra_map A B) (g : algebra_map B A),
    (forall v, f (iota v) = iota' v) /\
    (forall v, g (iota' v) = iota v) /\
    cancel f g /\ cancel g f /\
    (forall h : algebra_map A B,
      (forall v, h (iota v) = iota' v) -> forall x, h x = f x).
Proof.
have [f [fi fu]] := H hB iota'.
have [g [gi gu]] := H' hA iota.
exists f, g; split=> //; split=> //; split.
  apply: (symmetric_algebra_ext H hA (algebra_comp g f) (algebra_id A)) => v /=.
  by rewrite fi gi.
split.
  apply: (symmetric_algebra_ext H' hB (algebra_comp f g) (algebra_id B)) => v /=.
  by rewrite gi fi.
exact: fu.
Qed.
End Uniqueness.
