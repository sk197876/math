(** Federer (1969), 1.7.3, p. 29: supporting form lambda B-S in the
    principal-axis maximality argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Difference.
Variable R : fieldType.
Variable V : lmodType R.
Variable B S : V -> V -> R.
Variable lambda : R.

(** Source for [bilinear_difference]: Federer 1.7.3, p. 29,
    supporting quadratic defect lambda B(x,y)-S(x,y), where
    lambda is a maximum of S on a constrained unit sphere. *)
Definition bilinear_difference x y := lambda * B x y - S x y.

(** Source for [bilinear_differenceP]: Federer 1.7.3, p. 29,
    supporting bilinearity of the quadratic defect. *)
Lemma bilinear_differenceP : @bilinear R V V R^o B ->
  @bilinear R V V R^o S -> @bilinear R V V R^o bilinear_difference.
Proof.
move=> hB hS; split=> y a x z; rewrite /bilinear_difference.
- rewrite (bilDl hB) (bilZl hB) (bilDl hS) (bilZl hS).
  change (lambda * (a * B x y + B z y) - (a * S x y + S z y) =
    a * (lambda * B x y - S x y) + (lambda * B z y - S z y)).
  by rewrite mulrDr mulrBr opprD [lambda * (a * _)]mulrCA addrACA.
- rewrite (bilDr hB) (bilZr hB) (bilDr hS) (bilZr hS).
  change (lambda * (a * B y x + B y z) - (a * S y x + S y z) =
    a * (lambda * B y x - S y x) + (lambda * B y z - S y z)).
  by rewrite mulrDr mulrBr opprD [lambda * (a * _)]mulrCA addrACA.
Qed.

(** Source for [bilinear_difference_symmetric]: Federer 1.7.3,
    p. 29, symmetry of the supporting defect form follows from
    symmetry of B and S. *)
Lemma bilinear_difference_symmetric : (forall x y, B x y = B y x) ->
  (forall x y, S x y = S y x) ->
  forall x y, bilinear_difference x y = bilinear_difference y x.
Proof. move=> hB hS x y; by rewrite /bilinear_difference hB hS. Qed.
End Difference.
