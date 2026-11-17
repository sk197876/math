(** Federer (1969), 3.4.8(4), p. 326:
    the original fixed-vector subsets are subgroups.
    The argument uses only the actual action equations. *)
From mathcomp Require Import all_boot all_order boolp classical_sets.
From Federer Require Import TopologicalGroupUP PointwiseFixingLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointwise_fixing_subgroup]: identity,
    composition and inversion preserve every original
    fixed-vector equation, 3.4.8(4), p. 326. *)
Theorem pointwise_fixing_subgroup (G X:Type) (mul:G->G->G) (inv:G->G) (unit:G)
  (action:G->X->X) n (e:'I_n->X) (J:set 'I_n) (S:set G):
  is_pointwise_fixing_locus action e J S ->
  (forall x,action unit x = x) ->
  (forall g h x,action (mul g h) x = action g (action h x)) ->
  (forall g x,action (inv g) (action g x) = x) ->
  is_subgroup mul inv unit S.
Proof.
move=>hS hUnit hMul hInverse;constructor.
- apply/(hS unit)=>i hi;exact:hUnit.
- move=>g h /(hS g) hG /(hS h) hH;apply/(hS (mul g h))=>i hi.
  by rewrite hMul (hH i hi) (hG i hi).
- move=>g /(hS g) hG;apply/(hS (inv g))=>i hi.
  by rewrite -[in LHS](hG i hi) hInverse.
Qed.
