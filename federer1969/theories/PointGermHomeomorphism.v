(** Federer (1969), 3.4.8(11), p. 333:
    the point germ is unchanged by
    the original orthogonal coordinate change.
    This supporting connection uses only the
    continuous inverse, its centre value and
    the actual cancellation equation. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [point_germ_inverse_transport]:
    transport the zero-dimensional point-germ conclusion
    back through the original rotation,
    3.4.8(11), p. 333. *)
Theorem point_germ_inverse_transport (X:topologicalType) (a:X) (u v:X->X) (S:set X):
  continuous v ->u a = a ->v a = a ->(forall x,u (v x) = x) ->
  set_germ_subset (@set_germ X a (u @^-1` S)) (@set_germ X a [set a]) ->
  set_germ_subset (@set_germ X a S) (@set_germ X a [set a]).
Proof.
move=>hV hUa hVa hCancel.
move/set_germ_subset_original=>[W [hW [haW hPoint]]].
apply/set_germ_subset_original;exists (v @^-1` W);split.
- exact:(@open_comp X X v W (fun x _=>hV x) hW).
split;first by change (W (v a));rewrite hVa.
move=>x hx hWx.
have hSPre:(u @^-1` S) (v x) by change (S (u (v x)));rewrite hCancel.
have hVX:v x = a:=hPoint (v x) hSPre hWx.
have hY:=hCancel x;rewrite hVX hUa in hY;exact:esym hY.
Qed.
