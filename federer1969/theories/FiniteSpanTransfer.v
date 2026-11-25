(** Federer (1969), 1.7.1, p. 28: supporting span calculations for
    Gram-Schmidt, especially preservation of each prefix span. These are
    elementary consequences of the existing finite-span definition, not
    additional assertions in the book. Source context are recorded in
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import FiniteSpans FiniteSpanSpace InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Spans.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [in_finite_span_subtract]: Federer 1.7.1,
    p. 28, supporting closure under subtraction of the old projection. *)
Lemma in_finite_span_subtract n (e : 'I_n -> V) x y :
  in_finite_span e x -> in_finite_span e y -> in_finite_span e (x-y).
Proof.
move=> hx hy; apply: in_finite_span_add hx _.
rewrite -scaleN1r; exact: in_finite_span_scale hy.
Qed.

(** Source for [finite_span_mono]: Federer 1.7.1, p. 28,
    supporting span transfer: containing every generator implies
    containing its whole finite span. *)
Lemma finite_span_mono m n (e : 'I_m -> V) (f : 'I_n -> V) :
  (forall i, in_finite_span f (e i)) ->
  forall x, in_finite_span e x -> in_finite_span f x.
Proof.
move=> hf x [c ->]; apply: big_ind.
- exact: in_finite_span_zero.
- exact: in_finite_span_add.
- move=> i _; exact: in_finite_span_scale (hf i).
Qed.

(** Source for [finite_span_extensional]: Federer 1.7.1,
    p. 28, replacing a family by a pointwise equal family preserves its span. *)
Lemma finite_span_extensional n (e f : 'I_n -> V) :
  e =1 f -> forall x, in_finite_span e x <-> in_finite_span f x.
Proof.
move=> h x; split; apply: finite_span_mono => i.
- rewrite h; exact: finite_span_generator.
- rewrite -h; exact: finite_span_generator.
Qed.

(** Source for [finite_span_snoc_decomposition]: Federer
    1.7.1, p. 28, the span after adjoining a vector consists of
    an old-span vector plus a scalar multiple of the new vector. *)
Lemma finite_span_snoc_decomposition n (e : 'I_n -> V) v x :
  in_finite_span (ordinal_snoc e v) x <->
  exists y a, in_finite_span e y /\ x = y + a *: v.
Proof.
split.
- move=> [c hc].
  exists (\sum_i c (widen_ord (leqnSn n) i) *: e i), (c ord_max); split.
    by exists (fun i => c (widen_ord (leqnSn n) i)).
  rewrite hc big_ord_recr ordinal_snoc_last; congr (_ + _).
  apply: eq_bigr => i _; by rewrite ordinal_snoc_before.
- move=> [y [a [hy ->]]]; apply: in_finite_span_add.
  + exact: in_finite_span_snoc hy.
  + apply: in_finite_span_scale; exact: in_finite_span_last.
Qed.

(** Source for [finite_span_snoc_transfer]: Federer 1.7.1,
    p. 28, supporting comparison of the enlarged prefix spans.
    It suffices to transfer the old span and the new generator. *)
Lemma finite_span_snoc_transfer m n (e : 'I_m -> V) (f : 'I_n -> V) v w :
  (forall x, in_finite_span e x -> in_finite_span f x) ->
  in_finite_span (ordinal_snoc f w) v ->
  forall x, in_finite_span (ordinal_snoc e v) x -> in_finite_span (ordinal_snoc f w) x.
Proof.
move=> hef hv x /finite_span_snoc_decomposition [y [a [hy ->]]].
apply: in_finite_span_add; last exact: in_finite_span_scale hv.
exact: in_finite_span_snoc (hef y hy).
Qed.

(** Source for [finite_span_snoc_equiv]: Federer 1.7.1,
    p. 28, adjoining the same vector to two families with the same
    span preserves equality of their enlarged spans. *)
Lemma finite_span_snoc_equiv m n (e : 'I_m -> V) (f : 'I_n -> V) v :
  (forall x, in_finite_span e x <-> in_finite_span f x) ->
  forall x, in_finite_span (ordinal_snoc e v) x <-> in_finite_span (ordinal_snoc f v) x.
Proof.
move=> h x; split.
- exact (@finite_span_snoc_transfer m n e f v v
    (fun y => proj1 (h y)) (in_finite_span_last f v) x).
- exact (@finite_span_snoc_transfer n m f e v v
    (fun y => proj2 (h y)) (in_finite_span_last e v) x).
Qed.
End Spans.
