(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332:
    the original prefix and equation differentials
    separate source vectors. This is the
    kernel calculation for applying the existing
    analytic inverse theorem to the joint map. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_joint_coordinate_separation]:
    the joint differential of p_m and
    the defining equations has zero kernel,
    3.4.12, p. 339, extending 3.4.8(10), pp. 331–332. The
    nonzero original W' and delta cancel
    successively; all original coordinates then vanish. *)
Theorem field_joint_coordinate_separation (R:fieldType) (X Y:lmodType R)
    (index:finType) (first:index) (P:Hom X Y) (xi:index->Hom X R^o)
    (D:index->Hom X R^o) (delta wD:R) (tD:index->R):
  (forall u,P u = 0 ->(forall j,xi j u = 0) ->u=0) ->
  (forall j u,P u = 0 ->D j u = if j==first then wD*xi first u else
    delta*xi j u-tD j*xi first u) ->
  delta!=0 ->wD!=0 ->
  forall u,P u = 0 ->(forall j,D j u = 0) ->u=0.
Proof.
move=>hSeparate hDirections hDelta hWD u hP hD.
have hFirst:xi first u = 0.
  have hProduct:wD*xi first u = 0.
    have h:=hD first;by rewrite (@hDirections first u hP) eqxx in h.
  apply/eqP;move/eqP:hProduct;by rewrite mulf_eq0 (negbTE hWD) orFb.
apply:(hSeparate u hP)=>j.
case:(eqVneq j first)=>[->|hOther];first exact:hFirst.
have hProduct:delta*xi j u = 0.
  have h:=hD j;by rewrite (@hDirections j u hP) (negbTE hOther) hFirst mulr0 subr0 in h.
apply/eqP;move/eqP:hProduct;by rewrite mulf_eq0 (negbTE hDelta) orFb.
Qed.
