(** Federer (1969), 3.4.8(2),(10), pp. 326, 332–333:
    orthogonal changes of coordinates preserve
    local vanishing on the inverse-image
    set. Prove this general topology
    connection from the actual inverse maps. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets topology.
From Federer Require Import GermVanishingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.

(** Source for [vanishing_near_homeomorphism]:
    the condition I=ideal(var I) is
    invariant under the coordinate change
    defining I_g, supporting the last
    assertion of 3.4.8(10), pp. 332–333.
    Actual open preimages transport the
    original neighbourhood witnesses in both directions. *)
Theorem vanishing_near_homeomorphism (X:topologicalType) (A:zmodType)
    (u v:X->X) (a:X) (S:set X) (f g:X->A):
  continuous u ->continuous v ->u a=a ->v a=a ->
  cancel u v ->cancel v u ->(forall x,g x=f (u x)) ->
  (vanishes_near_on a S f <->vanishes_near_on a (u @^-1` S) g).
Proof.
move=>hU hV hUA hVA hUV hVU hValues;split.
- move=>[W [hW [ha hZero]]].
  exists (u @^-1` W);split.
  + exact:(continuousP u).1 hU W hW.
  split;first by rewrite /= hUA.
  move=>x hx hWx;rewrite hValues;exact:hZero (u x) hx hWx.
- move=>[W [hW [ha hZero]]].
  exists (v @^-1` W);split.
  + exact:(continuousP v).1 hV W hW.
  split;first by rewrite /= hVA.
  move=>x hx hWx.
  have hS:(u @^-1` S) (v x) by rewrite /= hVU.
  have h:=hZero (v x) hS hWx.
  by rewrite hValues hVU in h.
Qed.
