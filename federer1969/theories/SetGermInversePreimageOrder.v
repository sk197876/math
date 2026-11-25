(** Federer (1969), 3.4.8(11), pp. 333–335:
    an original invertible continuous coordinate map
    preserves and reflects germ containment. Apply the
    proved preimage equality connection to the defining
    Boolean intersection equation. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermContinuousPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_continuous_preimage_subset]:
    local containment survives the original coordinate
    preimage, supporting 3.4.8(11), pp. 333–335. *)
Lemma set_germ_continuous_preimage_subset (X Y:topologicalType) (u:X->Y) a b (S T:set Y):
  continuous u ->u a = b ->set_germ_subset (@set_germ Y b S) (@set_germ Y b T) ->
  set_germ_subset (@set_germ X a (u @^-1` S)) (@set_germ X a (u @^-1` T)).
Proof.
move=>hU hCentre hContained.
rewrite /set_germ_subset (@set_germ_intersection_equation Y b _ _ _ (@SetGerms.laws Y b)) in hContained.
have h:=@set_germ_continuous_preimage_equality X Y u a b (S `&` T) S hU hCentre hContained.
rewrite /set_germ_subset (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)).
exact:h.
Qed.

(** Source for [set_germ_inverse_preimage_subset_reflect]:
    the original inverse coordinate map reflects
    germ containment, supporting the strict exceptional
    cut in 3.4.8(11), p. 334. *)
Lemma set_germ_inverse_preimage_subset_reflect (X Y:topologicalType) (u:X->Y) (v:Y->X)
    a b (S T:set Y):
  continuous v ->v b = a ->cancel v u ->
  set_germ_subset (@set_germ X a (u @^-1` S)) (@set_germ X a (u @^-1` T)) ->
  set_germ_subset (@set_germ Y b S) (@set_germ Y b T).
Proof.
move=>hV hCentre hUV hContained.
have h:=@set_germ_continuous_preimage_subset Y X v b a (u @^-1` S) (u @^-1` T) hV hCentre hContained.
have hCancel E:v @^-1` (u @^-1` E) = E.
  apply:funext=>y;change (E (u (v y)) = E y);by rewrite hUV.
by rewrite !hCancel in h.
Qed.
