(** General topology supporting Federer (1969), 2.2.4, p. 62: extracting a
    countable cover of the points with countable neighborhoods. We prove the
    needed arbitrary-subset version from the countable-base specification.
    Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_base_open_subcover]: supporting Lindelof argument
    in Federer 2.2.4, p. 62. Every open cover of any subset has a countable
    subfamily covering that subset; empty subsets and covers are permitted.
    Choose at most one cover member per base index. *)
Theorem countable_base_open_subcover (T : topologicalType) (U : nat -> set T)
    (A : set T) (C : set (set T)) :
  is_countable_open_base U -> (forall V, C V -> open V) ->
  A `<=` \bigcup_(V in C) V ->
  exists G : set (set T), G `<=` C /\ countable G /\ A `<=` \bigcup_(V in G) V.
Proof.
move=> hU ho hc.
pose J := [set i | exists V, C V /\ U i `<=` V].
have hex i : exists V, J i -> C V /\ U i `<=` V.
  case: (pselect (J i))=> [[V hV]|hn]; first by exists V.
  exists set0=> hi; exact: False_ind _ (hn hi).
pose f i := projT1 (cid (hex i)).
have hf i : J i -> C (f i) /\ U i `<=` f i := projT2 (cid (hex i)).
exists (f @` J); split.
- move=> V [i hi <-]; exact: (hf i hi).1.
- split.
  + apply: sub_countable (card_image_le _ _) _; exact: countableP.
  + move=> x hx; have [V hV hxV] := hc x hx.
    have [i [hix his]] := @countable_base_refines T U hU V (ho V hV) x hxV.
    have hi : J i by exists V.
    exists (f i); first by exists i.
    exact: (hf i hi).2 x hix.
Qed.
