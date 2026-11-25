(** General topology supporting Federer (1969), 3.3.10, p. 296:
    the actual Grassmann initial topology inherits a countable base.
    Only the background countable-base and initial-topology laws are used. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [initial_countable_open_base]: background supporting
    the product/Suslin measurability step in Federer 3.3.10, p. 296,
    and the countable bases of 2.2.11, p. 68. Inverse images of a
    countable base form a countable base for the topology initially
    induced by one map. No injectivity or chosen auxiliary base is
    asserted as a mathematical hypothesis of the structure theorem. *)
Theorem initial_countable_open_base (T:choiceType) (Y:topologicalType) (f:T->Y)
    (U:nat->set Y):
  is_countable_open_base U ->
  @is_countable_open_base [the topologicalType of initial_topology f] (fun j=>f @^-1` U j).
Proof.
move=>hU; constructor.
- move=>j; exists (U j); first exact:countable_base_open hU j.
  reflexivity.
- by rewrite (countable_base_empty hU) preimage_set0.
- move=>O [V hV <-] x hx.
  have [j [hj hSub]]:=@countable_base_refines Y U hU V hV (f x) hx.
  exists j; split; first exact:hj.
  move=>z hz; exact:hSub (f z) hz.
Qed.
