(** Federer (1969), 1.6.5, pp. 25-26, supporting extension of
    the basis-pair calculation to arbitrary multivectors.
    The general bilinear extension principle below uses only the
    abstract spanning property of the two bases. *)

From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [bilinear_basis_ext]: Federer 1.6.5, pp. 25-26,
    supporting spanning argument. Two bilinear maps agreeing on
    every pair of basis vectors agree on every pair of vectors. *)
Theorem bilinear_basis_ext (K : fieldType) (I J : choiceType)
  (U V W : lmodType K) (e : I -> U) (b : J -> V)
  (he : is_basis e) (hb : is_basis b) (f g : U -> V -> W)
  (hf : bilinear f) (hg : bilinear g) :
  (forall i j, f (e i) (b j) = g (e i) (b j)) -> forall x y, f x y = g x y.
Proof.
move=> h; apply: (basis_induction he).
- by move=> y; rewrite (bil0l hf) (bil0l hg).
- move=> x z hx hz y; by rewrite (bilDl hf) (bilDl hg) hx hz.
- move=> c x hx y; by rewrite (bilZl hf) (bilZl hg) hx.
- move=> i; apply: (basis_induction hb).
  + by rewrite (bil0r hf) (bil0r hg).
  + move=> y z hy hz; by rewrite (bilDr hf) (bilDr hg) hy hz.
  + move=> c y hy; by rewrite (bilZr hf) (bilZr hg) hy.
  + exact: h.
Qed.
