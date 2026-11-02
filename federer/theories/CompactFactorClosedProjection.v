(** General topology supporting Federer (1969), 3.2.14,
    p. 252: a closed graph with compact source projection has
    closed range. The compact-factor projection assertion below
    requires neither local compactness nor completeness of the
    second factor. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_factor_closed_projection]: background
    compactness argument for closure of a rectifiable set,
    Federer 3.2.14, p. 252. A closed subset of K times Y has
    closed projection onto Y whenever K is compact. *)
Theorem compact_factor_closed_projection (X Y : topologicalType)
    (K : set X) (C : set (X * Y)) :
  compact K -> closed C ->
  closed [set y | exists x, K x /\ C (x,y)].
Proof.
move=> hK hC.
have ho : open (~` [set y | exists x, K x /\ C (x,y)]).
  rewrite openE=> y hy.
  have hn : nbhs y [set z | forall x, K x -> ~ C (x,z)].
    apply: ((proj1 (compact_near_coveringP K)) hK Y (nbhs y)
      (fun z x => ~ C (x,z)) (nbhs_filter y)).
    move=> x hx.
    have hnxy : (~` C) (x,y) by move=> hc; apply: hy; exists x.
    have hopen := closed_openC hC.
    rewrite openE in hopen.
    have [[U V] [hU hV] hUV] := hopen (x,y) hnxy.
    exists (U,V); first by split.
    move=> [a b] hab; exact: (hUV (a,b) hab).
  apply: filterS hn=> z hz [x [hx hc]]; exact: (hz x hx hc).
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.
