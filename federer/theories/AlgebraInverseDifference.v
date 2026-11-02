(** Federer (1969), 3.1.11, p. 220:
    algebraic resolvent and quadratic remainder identities
    for the inversion operator. These identities use
    associativity and both inverse laws, not commutativity. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Bilinear AlgebraInverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [algebra_inverse_difference]: the inverse
    difference identity supporting differentiation of
    inversion in Federer 3.1.11, p. 220. *)
Lemma algebra_inverse_difference (K : fieldType) (A : algebra K) (x v y w : A) :
  is_two_sided_algebra_inverse x v -> is_two_sided_algebra_inverse y w ->
  w-v=alg_mul A v (alg_mul A (x-y) w).
Proof.
move=> [hxv hvx] [hyw hwy].
by rewrite (bilBl (alg_bilinear A)) hyw (bilBr (alg_bilinear A))
  alg_unitr alg_assoc hvx alg_unitl.
Qed.

(** Source for [algebra_inverse_perturbation_difference]:
    the resolvent identity for T+S and T, supporting
    Federer 3.1.11, p. 220. *)
Lemma algebra_inverse_perturbation_difference (K : fieldType) (A : algebra K)
    (x v h w : A) :
  is_two_sided_algebra_inverse x v -> is_two_sided_algebra_inverse (x+h) w ->
  w-v= -alg_mul A v (alg_mul A h w).
Proof.
move=> hv hw; rewrite (algebra_inverse_difference hv hw).
have hid : x-(x+h)= -h by rewrite opprD addrA subrr add0r.
rewrite hid -[(-h)]scaleN1r (bilZl (alg_bilinear A))
  (bilZr (alg_bilinear A)) scaleN1r; by [].
Qed.

(** Source for [algebra_inverse_quadratic_remainder]:
    subtracting the linear term -T^(-1) S T^(-1)
    leaves a quadratic expression, supporting the
    inversion derivative in Federer 3.1.11, p. 220. *)
Lemma algebra_inverse_quadratic_remainder (K : fieldType) (A : algebra K)
    (x v h w : A) :
  is_two_sided_algebra_inverse x v -> is_two_sided_algebra_inverse (x+h) w ->
  w-v+alg_mul A v (alg_mul A h v)=
    alg_mul A v (alg_mul A h (alg_mul A v (alg_mul A h w))).
Proof.
move=> hv hw; have hd := algebra_inverse_perturbation_difference hv hw.
by rewrite hd addrC -(bilBr (alg_bilinear A)) -(bilBr (alg_bilinear A))
  -[v-w]opprB hd opprK.
Qed.
