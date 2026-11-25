(** General topology supporting Federer (1969), 2.2.10, p. 66: closedness
    and continuity can be checked on an open cover. The first-coordinate
    cylinders of N supply the cover in the closed-real-parametrisation and
    union arguments. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_from_open_cover_sections]: supporting closedness
    argument in Federer 2.2.10, p. 66: if an open family covers the space
    and each intersection of B with a cover member is closed in the whole
    space, then B is closed. No finiteness premise is needed. *)
Lemma closed_from_open_cover_sections (T : topologicalType) (I : Type)
    (U : I -> set T) (B : set T) :
  (forall i, open (U i)) -> (forall x, exists i, U i x) ->
  (forall i, closed (B `&` U i)) -> closed B.
Proof.
move=> ho hcover hc; rewrite -openC openE=> x hx.
have [i hi] := hcover x.
have hU : nbhs x (U i) by have h := ho i; rewrite openE in h; exact: h x hi.
have hnot : (~` (B `&` U i)) x by move=> [hB _]; exact: hx hB.
have hn : nbhs x (~` (B `&` U i)).
  have h := closed_openC (hc i); rewrite openE in h; exact: h x hnot.
apply: filterS (filterI hU hn)=> y [hy hnB] hB; apply: hnB; by split.
Qed.

(** Source for [continuous_from_open_cover_agreement]: supporting continuity
    argument in Federer 2.2.10, p. 66. Only local agreement is used; no
    restriction topology is imposed outside the chosen pieces. *)
Lemma continuous_from_open_cover_agreement (T V : topologicalType) (I : Type)
    (U : I -> set T) (f : T -> V) (g : I -> T -> V) :
  (forall i, open (U i)) -> (forall x, exists i, U i x) ->
  (forall i, continuous (g i)) ->
  (forall i x, U i x -> f x = g i x) -> continuous f.
Proof.
move=> ho hcover hg he x A hA; have [i hi] := hcover x.
have hU : nbhs x (U i) by have h := ho i; rewrite openE in h; exact: h x hi.
have hA' : nbhs (g i x) A by rewrite -(he i x hi).
have hG : nbhs x (g i @^-1` A) := hg i x A hA'.
apply: filterS (filterI hU hG)=> y [hy hGy].
change (A (f y)); by rewrite (he i y hy).
Qed.
