(** Federer (1969), 3.4.7, p. 325: analytic
    pullback makes the ambient germ ring a module over
    the transverse germ ring. This hierarchy adapter records
    only the original scalar action and its algebraic laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [ring_restricted_space]: the underlying
    additive group with scalars restricted along the ring
    homomorphism in 3.4.7, p. 325. This adapter
    does not choose analytic representatives or a polynomial basis. *)
Definition ring_restricted_space (A B:nzRingType) (embed:{rmorphism A->B})
    (V:Type):Type:=V.
HB.instance Definition _ (A B:nzRingType) (embed:{rmorphism A->B}) (V:choiceType):=
  Choice.copy (ring_restricted_space embed V) V.
HB.instance Definition _ (A B:nzRingType) (embed:{rmorphism A->B}) (V:zmodType):=
  GRing.Zmodule.copy (ring_restricted_space embed V) V.
Section Action.
Variables A B:nzRingType.
Variable embed:{rmorphism A->B}.
Variable V:lmodType B.
Local Notation VR:=(ring_restricted_space embed V).

(** Source for [ring_restricted_scale]: the transverse
    scalar action supporting 3.4.7, p. 325. *)
Definition ring_restricted_scale (a:A) (x:VR):VR:=embed a*:x.

(** Source for [ring_restricted_scale_associative]: the
    associative action law supporting 3.4.7, p. 325. *)
Lemma ring_restricted_scale_associative a b x:
  ring_restricted_scale a (ring_restricted_scale b x) = ring_restricted_scale (a*b) x.
Proof. by rewrite /ring_restricted_scale rmorphM scalerA. Qed.

(** Source for [ring_restricted_scale_one]: the unit
    action law supporting 3.4.7, p. 325. *)
Lemma ring_restricted_scale_one:left_id 1 ring_restricted_scale.
Proof. by move=>x;rewrite /ring_restricted_scale rmorph1 scale1r. Qed.

(** Source for [ring_restricted_scale_add_vectors]: vector
    distributivity of the action in 3.4.7, p. 325. *)
Lemma ring_restricted_scale_add_vectors a:
  {morph ring_restricted_scale a:x y/x+y}.
Proof. by move=>x y;rewrite /ring_restricted_scale scalerDr. Qed.

(** Source for [ring_restricted_scale_add_scalars]: scalar
    distributivity of the action in 3.4.7, p. 325. *)
Lemma ring_restricted_scale_add_scalars x:
  {morph ring_restricted_scale^~x:a b/a+b}.
Proof. by move=>a b;rewrite /ring_restricted_scale rmorphD scalerDl. Qed.
HB.instance Definition _:=GRing.Zmodule_isLmodule.Build A VR
  ring_restricted_scale_associative ring_restricted_scale_one
  ring_restricted_scale_add_vectors ring_restricted_scale_add_scalars.
End Action.
