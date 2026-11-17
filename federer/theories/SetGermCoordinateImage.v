(** Federer (1969), 3.4.8(13), p. 336:
    undo the auxiliary coordinate rotation on each
    original compact representative. The equality of germs
    follows by continuous inverse images of their actual
    equality neighbourhoods. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermContinuousPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_coordinate_image]: the equality
    gamma(psi_lambda(S_lambda))=var(I_g) in
    3.4.8(13), p. 336. This supporting
    topological connection keeps the actual source sets. *)
Theorem set_germ_coordinate_image (X:topologicalType) a (u v g h:X->X) (S H:set X):
  continuous v ->v a=a ->cancel u v ->cancel v u ->
  (forall x,h x=g (u x)) ->
  @set_germ X a S=@set_germ X a (h @^-1` H) ->
  @set_germ X a (u @` S)=@set_germ X a (g @^-1` H).
Proof.
move=>hV hCentre hVU hUV hComposition hGerm.
have hImage:u @` S=v @^-1` S.
  apply/seteqP;split.
  - by move=>x [z hz <-];rewrite /= hVU.
  - move=>x hx;exists (v x);first exact:hx;exact:hUV.
have hPreimage:v @^-1` (h @^-1` H)=g @^-1` H.
  apply/seteqP;split=>x;by rewrite /= hComposition hUV.
rewrite hImage -hPreimage.
exact:(@set_germ_continuous_preimage_equality X X v a a S (h @^-1` H) hV hCentre hGerm).
Qed.
