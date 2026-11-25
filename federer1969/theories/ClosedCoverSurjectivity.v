(** Federer (1969), 2.2.8, p. 64: g maps onto X. We use ordinary recursion
    and the abstract child-cover law; no computation through the private
    tree or branch-map witnesses is used. Source context and word encoding:
    ClosedCoverTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates ClosedCoverTreeUP
  SequenceTreePrefixes ClosedCoverBranches ClosedCoverMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_cover_map_surjective]: Federer 2.2.8, p. 64, the
    assertion that img g=X. For each x choose successively a child
    containing x, realise the resulting coordinate sequence, and use
    uniqueness of its branch point. *)
Theorem closed_cover_map_surjective (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E)
    (g : positive_sequence_space R -> T) (hg : is_closed_cover_map E g) :
  forall x, exists n, g n = x.
Proof.
move=> x.
have hc s : exists j : nat, E s x -> E (j::s) x.
  case: (pselect (E s x))=> hs.
  - rewrite (closed_cover_tree_children hE s) in hs.
    have [j _ hj] := hs; exists j=> _; exact hj.
  - exists 0%N=> hx; exfalso; exact: hs hx.
pose j s := projT1 (cid (hc s)).
have hj s : E s x -> E (j s::s) x := projT2 (cid (hc s)).
pose s := nat_rect (fun _ => seq nat) [::] (fun _ t => j t::t).
have hs k : E (s k) x.
  elim: k=> [|k IH]; first by rewrite /s /= (closed_cover_tree_root hE).
  exact: hj IH.
pose a k := j (s k).
pose n := @positive_sequence_from_coordinates R a.
have hp k : sequence_tree_prefix n k = s k.
  elim: k=> [|k IH] //=.
  by rewrite /n positive_sequence_coordinatesK /a IH.
exists n; apply: (@closed_cover_branch_point_unique R T E hE n (g n) x).
- exact: hg.
- move=> k; rewrite hp; exact: hs.
Qed.
