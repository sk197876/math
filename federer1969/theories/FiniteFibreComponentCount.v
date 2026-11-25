(** Federer (1969), 3.4.8(11), p. 335:
    finitely many base components and finite
    projection fibres give finitely many source
    components when every component projects onto
    its base component. The component images
    are supplied by original (10). *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_fibre_component_count]:
    finiteness of the components of T
    in 3.4.8(11), p. 335. One
    fibre over each base component supplies
    a finite family of actual component markers. *)
Theorem finite_fibre_component_count (X Y:topologicalType) (P:X->Y)
    (Z:set X) (V:set Y) (y0:Y):
  (forall x,Z x ->V (P x)) ->
  finite_set (connected_component V @` V) ->
  (forall y,V y ->finite_set [set x|Z x /\ P x = y]) ->
  (forall x,Z x ->P @` connected_component Z x = connected_component V (P x)) ->
  finite_set (connected_component Z @` Z).
Proof.
move=>hRange hBaseFinite hFibres hImages.
pose B:=connected_component V @` V.
have hChoose C:exists y:Y,B C ->C y.
  case:(pselect (B C))=>hC;last by exists y0.
  have [y hy <-]:=hC;exists y=>_.
  exact:connected_component_refl hy.
have [y hY]:=choice hChoose.
have hYV C (hC:B C):V (y C).
  have [z hz hEqual]:=hC.
  have hSub:C `<=` V.
    rewrite -hEqual;exact:(@connected_component_sub Y V z).
  exact:hSub (y C) (hY C hC).
pose F:=\bigcup_(C in B) [set x|Z x /\ P x = y C].
have hFFinite:finite_set F:=bigcup_finite hBaseFinite (fun C hC=>hFibres (y C) (hYV C hC)).
have hFiniteImages:finite_set (connected_component Z @` F):=finite_image _ hFFinite.
apply:(sub_finite_set _ hFiniteImages)=>C [x hx <-].
have hB:B (connected_component V (P x)) by exists (P x);first exact:hRange x hx.
have hMarker:(P @` connected_component Z x) (y (connected_component V (P x))).
  rewrite (hImages x hx);exact:hY (connected_component V (P x)) hB.
have [z hZComponent hPz]:=hMarker.
exists z.
- exists (connected_component V (P x));first exact:hB.
  split;first exact:(@connected_component_sub X Z x z hZComponent).
  exact:hPz.
- exact:esym (@same_connected_component X Z x z hZComponent).
Qed.
