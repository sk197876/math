(** General-topology support for Federer (1969), 2.6.6, pp. 120–121: closed
    constraints with the finite intersection property have a common point in
    a compact set. This is proved by finite open subcovers, including an
    empty compact set. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
From Federer Require Import CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_closed_family_meeting]: supporting compact
    intersection argument for inverse limits in Federer 2.6.6,
    pp. 120–121. Every finite collection must have a point in K. *)
Theorem compact_closed_family_meeting (X : topologicalType) (I : choiceType)
    (K : set X) (C : I -> set X) :
  compact K -> (forall i, closed (C i)) ->
  (forall F : {fset I}, exists x, K x /\ forall i, i \in F -> C i x) ->
  exists x, K x /\ forall i, C i x.
Proof.
move=> hc hC hfinite; apply: contrapT=> hnone.
have hcover : K `<=` \bigcup_(i in setT) (~` C i).
  move=> x hx; apply: contrapT=> hnot; apply: hnone; exists x; split=> // i.
  apply: contrapT=> hCi; apply: hnot; by exists i.
have [F hF hcov] := @compact_open_finite_cover X I setT (fun i=> ~` C i) K hc
  (fun i _=>closed_openC (hC i)) hcover.
have [x [hx hCx]] := hfinite F.
have [i hi hnot] := hcov x hx; exact: hnot (hCx i hi).
Qed.
