(** General topology supporting Federer (1969), 2.5.20, p. 114: basic
    rectangles refine open neighborhoods in X times Y. The countable bases
    are the specifications already used for 2.2.11, p. 68. Source context:
    CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_product_rectangle_refines]: a basic
    rectangle can be chosen inside the complement of spt mu,
    supporting the fibre support inference in Federer 2.5.20,
    p. 114. This is a general product-topology lemma. *)
Lemma countable_product_rectangle_refines (X Y : topologicalType)
    (B : nat -> set X) (C : nat -> set Y) (W : set (X*Y)) x y :
  is_countable_open_base B -> is_countable_open_base C -> open W -> W (x,y) ->
  exists i j, B i x /\ C j y /\ B i `*` C j `<=` W.
Proof.
move=> hB hC hW hxy.
have hn : nbhs (x,y) W by rewrite openE in hW; exact: hW _ hxy.
have [[U V] [hU hV] hUV] := hn.
rewrite nbhsE in hU.
rewrite nbhsE in hV.
have [U' [hU' hx] hUU] := hU.
have [V' [hV' hy] hVV] := hV.
have [i [hi hBi]] := countable_base_refines hB hU' hx.
have [j [hj hCj]] := countable_base_refines hC hV' hy.
exists i,j; split=> //; split=> //.
move=> [u v] [hu hv]; apply: hUV; split.
- exact: hUU (hBi u hu).
- exact: hVV (hCj v hv).
Qed.
