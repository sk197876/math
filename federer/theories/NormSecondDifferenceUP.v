(** Federer (1969), 3.1.11, p. 219:
    the quadratic second-difference remainder and its symmetry.
    This intrinsic remainder statement precedes the proof
    that the actual second differential satisfies it. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_second_difference]: the four function
    values in the second displayed limit of Federer 3.1.11,
    p. 219. The base point is kept explicit. *)
Definition norm_second_difference (R : realType) (X Y : lmodType R)
    (f : X->Y) (a u v : X) :=
  f (a+u+v)-f (a+u)-f (a+v)+f a.

(** Source for [norm_second_difference_symmetric]: exchanging
    u and v leaves the four-point difference fixed,
    supporting the symmetry conclusion in Federer 3.1.11,
    p. 219. *)
Lemma norm_second_difference_symmetric (R : realType) (X Y : lmodType R)
    (f : X->Y) (a u v : X) :
  norm_second_difference f a u v=norm_second_difference f a v u.
Proof. by rewrite /norm_second_difference (addrAC a u v)
  (addrAC (f (a+v+u)) (-f (a+u)) (-f (a+v))). Qed.

(** Source for [has_norm_quadratic_second_remainder]:
    the second-difference limit in Federer 3.1.11,
    p. 219, expressed by epsilon estimates. The
    zero increments are included without dividing by zero.
    B takes the last argument first, as in D(Df). *)
Definition has_norm_quadratic_second_remainder (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (f : X->Y) (a : X) (B : Hom X (Hom X Y)) :=
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall u v, NX u<d -> NX v<d ->
      NY (norm_second_difference f a u v-B v u)<=e*(NX u+NX v)^+2.

(** Source for [linear_remainder_difference_identity]:
    subtracting the two first-order operator remainders,
    supporting the calculation of Dg_v in Federer 3.1.11,
    p. 219. This is an additive-group identity. *)
Lemma linear_remainder_difference_identity (V : zmodType) (a b c d e : V) :
  (a-b-c)-(d-b-e)=a-d-(c-e).
Proof.
by rewrite !opprB !addrA (addrAC (a-b-c) e b)
  (addrAC (a-b) (-c) b) subrK (addrAC (a-c) e (-d))
  (addrAC a (-c) (-d)) (addrAC (a-d) (-c) e).
Qed.

(** Source for [norm_second_difference_translate]:
    the reduction to a= 0 in Federer 3.1.11, p. 219,
    leaves the four-point difference unchanged. *)
Lemma norm_second_difference_translate (R : realType) (X Y : lmodType R)
    (f : X->Y) (a u v : X) :
  norm_second_difference (fun x=>f (a+x)-f a) 0 u v=
    norm_second_difference f a u v.
Proof.
have hc (x y z : Y) : (x-z)-(y-z)=x-y by rewrite opprB addrA subrK.
rewrite /norm_second_difference !add0r addr0 subrr addr0 addrA hc opprB addrA.
by rewrite (addrAC (f (a+u+v)-f (a+u)) (f a) (-f (a+v))).
Qed.
