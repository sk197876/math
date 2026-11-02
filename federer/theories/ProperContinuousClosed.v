(** Federer (1969), 2.2.17, p. 72, openness of the complements of images of
    closed sets. We prove its local compact-neighborhood argument using
    general topology, not an imported proper-map theorem. Source context:
    ProperMapUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import ProperMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [proper_continuous_map_closed]: supporting closed-map fact
    for Federer 2.2.17, p. 72 The proof only needs local compactness and
    Hausdorff separation of the target, a documented strengthening of the
    background lemma. *)
Theorem proper_continuous_map_closed (X Y : topologicalType) (f : X -> Y) :
  hausdorff_space Y -> locally_compact (@setT Y) -> continuous f -> is_proper_map f ->
  forall C, closed C -> closed (f @` C).
Proof.
move=> hY hl hf hp C hC.
have ho : open (~` (f @` C)).
  rewrite openE=> y hy.
  have [K hKnb [hK hKclosed]] := hl y Logic.I.
  rewrite withinET in hKnb.
  pose A := (f @^-1` K) `&` C.
  have hA : compact A := compact_closedI (hp K hK) hC.
  have hAc : compact (f @` A).
    apply: continuous_compact _ hA; exact: continuous_subspaceT hf.
  have hclosed : closed (f @` A) := compact_closed hY hAc.
  have hyn : (~` (f @` A)) y.
    move=> [x [_ hx] hxy]; apply: hy; by exists x.
  have hnb : nbhs y (~` (f @` A)).
    have hh := closed_openC hclosed; rewrite openE in hh; exact: hh y hyn.
  apply: filterS (filterI hKnb hnb)=> z [hzK hzn] [x hx hfx].
  apply: hzn; exists x=> //; split=> //; change (K (f x)); by rewrite hfx.
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.
