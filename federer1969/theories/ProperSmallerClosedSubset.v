(** Federer (1969), 4.1.7, p. 359:
    the second map is proper on the
    support of the first pushed current.
    This supporting restriction theorem uses
    only compact inverse images and closed
    relative subsets, as in 2.2.17, p. 72. *)
From mathcomp Require Import all_boot boolp functions classical_sets topology.
From Federer Require Import ProperMapUP IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [proper_map_smaller_closed_subset]:
    a map proper on B remains
    proper on every ambient closed subset
    A contained in B, supporting the
    original composite-properness hypothesis of
    Federer 4.1.7, p. 359. *)
Theorem proper_map_smaller_closed_subset (X Y:topologicalType) (f:X->Y) (A B:set X):
  closed A->A `<=` B->
  is_proper_map (fun x:set_type B=>f (set_val x))->
  is_proper_map (fun x:set_type A=>f (set_val x)).
Proof.
move=>hA hAB hp K hK.
pose BT:topologicalType:=[the topologicalType of set_type B].
pose AT:topologicalType:=[the topologicalType of set_type A].
pose C:set BT:=((fun x:BT=>f (set_val x)) @^-1` K) `&` (set_val @^-1` A).
have hClosed:@closed BT (set_val @^-1` A).
  apply:preimage_closed;last exact:hA.
  by move=>x _;exact:set_type_val_continuous.
have hC:@compact BT C:=compact_closedI (hp K hK) hClosed.
pose D:set X:=set_val @` C.
have hD:compact D.
  apply:continuous_compact hC;exact:continuous_subspaceT (@set_type_val_continuous X B).
have hDA:D `<=` A by move=>x [z [_ hz] <-];exact:hz.
have hPre:=@set_type_compact_preimage X A D hD hDA.
have hEqual:((fun x:AT=>f (set_val x)) @^-1` K)=(set_val @^-1` D:set AT).
  apply/seteqP;split.
  - move=>x hx;exists (exist _ (set_val x) (mem_set (hAB (set_val x) (set_valP x))));last by [].
    split;first exact:hx.
    exact:set_valP x.
  - move=>x [z [hz hAz] hzx];change (K (f (set_val x))).
    by rewrite -hzx.
by rewrite hEqual.
Qed.
