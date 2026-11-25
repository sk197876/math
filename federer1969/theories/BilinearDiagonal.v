(** Federer (1969), 1.7.3, p. 29: supporting quadratic identities for the
    principal-axis maximisation argument. These are consequences of
    bilinearity, separate from positivity or an inner-product construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Diagonal.
Variable R : fieldType.
Variable V : lmodType R.
Variable S : V -> V -> R.
Hypothesis hS : @bilinear R V V R^o S.

(** Source for [bilinear_diagonal_scale]: Federer 1.7.3,
    p. 29, supporting quadratic homogeneity: S(ax,ax)=a^2 S(x,x). *)
Lemma bilinear_diagonal_scale a x : S (a*:x) (a*:x) = a^+2 * S x x.
Proof.
rewrite (bilZl hS) (bilZr hS).
change (a * (a * S x x) = a^+2 * S x x).
by rewrite mulrA -expr2.
Qed.
End Diagonal.
