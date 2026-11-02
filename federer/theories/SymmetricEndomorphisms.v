(** Federer (1969), 1.7.3, p. 29: symmetric and skewsymmetric endomorphisms
    and orthogonal reducibility. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws TensorUP
  Bilinear ModuleQuotient.
From Federer Require Import OrthogonalComplement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_symmetric_endomorphism]: Federer 1.7.3,
    p. 29, definition: f(x).y = x.f(y) for all x,y. *)
Definition is_symmetric_endomorphism (R : fieldType) (V : lmodType R)
    (B : V -> V -> R) (f : {linear V -> V}) :=
  forall x y, B (f x) y = B x (f y).

(** Source for [is_skewsymmetric_endomorphism]: Federer 1.7.3,
    p. 29, definition: f(x).y = -x.f(y) for all x,y. *)
Definition is_skewsymmetric_endomorphism (R : fieldType) (V : lmodType R)
    (B : V -> V -> R) (f : {linear V -> V}) :=
  forall x y, B (f x) y = - B x (f y).

(** Source for [invariant_subspace]: Federer 1.7.3, p. 29,
    the condition f(W) is contained in W. *)
Definition invariant_subspace (R : fieldType) (V : lmodType R)
    (f : {linear V -> V}) (W : subspace V) := forall x, W x -> W (f x).

Section Reducibility.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable f : {linear V -> V}.

(** Source for [symmetric_orthogonal_reducibility]: Federer
    1.7.3, p. 29, an invariant subspace has invariant orthogonal
    complement for a symmetric endomorphism. No dimension restriction. *)
Theorem symmetric_orthogonal_reducibility (W : subspace V) :
  is_symmetric_endomorphism B f -> invariant_subspace f W ->
  invariant_subspace f (orthogonal_complement hB W).
Proof. move=> hf hW x hx y hy; rewrite hf; exact: hx (hW y hy). Qed.

(** Source for [skewsymmetric_orthogonal_reducibility]: Federer 1.7.3, p.
    29, the same invariance assertion for a skewsymmetric endomorphism, as
    expanded in the cited. *)
Theorem skewsymmetric_orthogonal_reducibility (W : subspace V) :
  is_skewsymmetric_endomorphism B f -> invariant_subspace f W ->
  invariant_subspace f (orthogonal_complement hB W).
Proof. move=> hf hW x hx y hy; by rewrite hf (hx _ (hW y hy)) oppr0. Qed.

(** Source for [skewsymmetric_square_symmetric]: Federer 1.7.3,
    p. 29, the square of a skewsymmetric endomorphism is symmetric.
    This is the algebraic step in the dimension-at-most-two assertion. *)
Theorem skewsymmetric_square_symmetric : is_skewsymmetric_endomorphism B f ->
  is_symmetric_endomorphism B (linear_comp f f).
Proof. move=> hf x y; change (B (f (f x)) y = B x (f (f y))); by rewrite !hf opprK. Qed.

(** Source for [skewsymmetric_diagonal_zero]: Federer 1.7.3,
    pp. 29-30, supporting alternation of the bilinear form f(x).y
    associated with a skewsymmetric endomorphism. *)
Lemma skewsymmetric_diagonal_zero : is_skewsymmetric_endomorphism B f ->
  forall x, B (f x) x = 0.
Proof.
move=> hf x; have h := hf x x; rewrite (inner_symmetric hB x (f x)) in h.
have hz : (2 : R) * B (f x) x = 0.
  by rewrite mulr_natl mulr2n {1}h addNr.
move/eqP: hz; rewrite mulf_eq0 pnatr_eq0 /= => /eqP; exact.
Qed.
End Reducibility.
