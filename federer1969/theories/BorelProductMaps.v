(** Federer (1969), 2.2.14, p. 70: the product map used to express the graph
    has Borel inverse images. We prove the binary case directly from open
    rectangles and the local Borel-family laws. Source context:
    BorelFunctionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import BorelFamilyBasic TopologicalBorel BorelFunctionUP
  CountableOpenBaseUP CompactTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_pair_function]: supporting product-map assertion in
    Federer 2.2.14, p. 70 Countable open bases in both target factors allow
    an open preimage to be expressed as a countable union of intersections
    of Borel preimages. *)
Theorem borel_pair_function (X Y Z : topologicalType) (f : X -> Y) (g : X -> Z)
    (U : nat -> set Y) (V : nat -> set Z) :
  is_countable_open_base U -> is_countable_open_base V ->
  is_borel_function f -> is_borel_function g -> is_borel_function (fun x => (f x,g x)).
Proof.
move=> hU hV hf hg O ho.
pose D := [set p : nat * nat | U p.1 `*` V p.2 `<=` O].
pose F (p : nat * nat) := (f @^-1` U p.1) `&` (g @^-1` V p.2).
have he : (fun x => (f x,g x)) @^-1` O = \bigcup_(p in D) F p.
  apply/seteqP; split.
  - move=> x hx.
    have [A [B [ha [hb [hfx [hgx hab]]]]]] := open_product_rectangle_at ho hx.
    have [i [hi hia]] := @countable_base_refines Y U hU A ha (f x) hfx.
    have [j [hj hjb]] := @countable_base_refines Z V hV B hb (g x) hgx.
    exists (i,j); last by split.
    move=> [y z] [hy hz]; apply: hab; split; [exact: hia y hy|exact: hjb z hz].
  - move=> x [p hp [hx hy]]; apply: hp; by split.
rewrite he; apply: borel_set_countable_union (countableP D) _=> p hp.
apply: (borel_family_binary_intersection (borel_sets_family X)).
- exact: hf _ (countable_base_open hU p.1).
- exact: hg _ (countable_base_open hV p.2).
Qed.
