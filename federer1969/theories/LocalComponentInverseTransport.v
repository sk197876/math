(** Federer (1969), 3.4.8(11), p. 333:
    a translated local finite component count transfers
    to the original centre. Actual continuous inverses
    identify components through the existing section theorem. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import ContinuousSectionComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [local_component_inverse_transport]:
    translate the finite component neighbourhood back
    to a in 3.4.8(11), p. 333. *)
Theorem local_component_inverse_transport (X Y:topologicalType)
    (u:X->Y) (v:Y->X) (H:set Y) (U:set X):
  continuous u ->continuous v ->cancel u v ->cancel v u ->
  finite_set (connected_component (u @^-1` H) @` ((u @^-1` H) `&` U)) ->
  finite_set (connected_component H @` (H `&` (v @^-1` U))).
Proof.
move=>hU hV hVU hUV hFinite.
pose B:set X:=u @^-1` H.
have hImage:u @` B = H.
  apply/seteqP;split=>y.
  - by move=>[x hx <-].
  - move=>hy;exists (v y);last exact:hUV y.
    change (H (u (v y)));by rewrite hUV.
have hComponents:forall x,B x ->connected_component H (u x) = u @` connected_component B x.
  move=>x hx;rewrite -hImage.
  exact:(@continuous_section_component_image Y X v B u hV
    (fun y _=>hU y) (fun y _=>hVU y) x hx).1.
have hFiniteImages:finite_set ((fun C:set X=>u @` C) @`
    (connected_component B @` (B `&` U))).
  exact:finite_image _ hFinite.
apply:(sub_finite_set _ hFiniteImages)=>C [y [hy hUy] <-].
have hBy:B (v y) by change (H (u (v y)));rewrite hUV.
exists (connected_component B (v y)).
- by exists (v y);first split.
- apply:esym;rewrite -(hComponents (v y) hBy) hUV;by [].
Qed.
