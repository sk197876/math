(** Federer (1969), 3.4.12, p. 339:
    the original scalar-commuting isometries form a subgroup.
    This missing connection uses only the actual action
    equations and both original inverse identities. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import TopologicalGroupUP PointwiseCommutingLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointwise_commuting_subgroup]: identity,
    composition and inverse retain every original commutation
    equation, as required for U(n) in 3.4.12,
    p. 339. *)
Theorem pointwise_commuting_subgroup (G X I:Type)
    (mul:G->G->G) (inv:G->G) (unit:G) (action:G->X->X)
    (P:I->X->X) (S:set G):
  is_pointwise_commuting_locus action P S ->
  (forall x,action unit x=x) ->
  (forall g h x,action (mul g h) x=action g (action h x)) ->
  (forall g x,action (inv g) (action g x)=x) ->
  (forall g x,action g (action (inv g) x)=x) ->
  is_subgroup mul inv unit S.
Proof.
move=>hS hUnit hMul hLeft hRight;constructor.
- apply/(hS unit)=>i x;by rewrite !hUnit.
- move=>g h /(hS g) hG /(hS h) hH;apply/(hS (mul g h))=>i x.
  by rewrite !hMul hH hG.
- move=>g /(hS g) hG;apply/(hS (inv g))=>i x.
  have hComm:=hG i (action (inv g) x).
  rewrite hRight in hComm.
  have hInverse:=congr1 (action (inv g)) hComm.
  rewrite hLeft in hInverse;exact:esym hInverse.
Qed.
