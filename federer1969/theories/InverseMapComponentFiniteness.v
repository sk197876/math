(** Federer (1969), 3.4.8(11), pp. 333–335:
    returning the strata from orthogonal coordinates
    preserves their finite component families. The existing
    inverse-map local transport theorem applies to the
    whole source neighbourhood. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import LocalComponentInverseTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [inverse_map_component_finiteness]:
    finite actual components are preserved under the
    original invertible continuous coordinate map,
    3.4.8(11), pp. 333–335. *)
Theorem inverse_map_component_finiteness (X Y:topologicalType) (u:X->Y) (v:Y->X) (H:set Y):
  continuous u ->continuous v ->cancel u v ->cancel v u ->
  finite_set (connected_component H @` H) ->
  finite_set (connected_component (u @^-1` H) @` (u @^-1` H)).
Proof.
move=>hU hV hVU hUV hFinite.
have hSame:v @^-1` (u @^-1` H) = H.
  apply:funext=>y;change (H (u (v y)) = H y);by rewrite hUV.
have hGiven:finite_set (connected_component (v @^-1` (u @^-1` H)) @`
    ((v @^-1` (u @^-1` H)) `&` setT)).
  by rewrite hSame setIT.
have hResult:=@local_component_inverse_transport Y X v u (u @^-1` H) setT hV hU hUV hVU hGiven.
by rewrite preimage_setT setIT in hResult.
Qed.
