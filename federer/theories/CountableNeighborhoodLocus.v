(** General topology supporting the continuum-cardinality assertion in
    Federer (1969), 2.2.4, p. 62. This file proves openness and countability
    of the removed set from an abstract countable base. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_neighborhood_locus]: Supporting Federer 2.2.4, p.
    62.A point is removed precisely when it has a countable open
    neighborhood. *)
Definition countable_neighborhood_locus (T : topologicalType) : set T :=
  [set x | exists V : set T, open V /\ countable V /\ V x].
Arguments countable_neighborhood_locus {T}.

(** Source for [countable_neighborhood_locus_open]: Supporting Federer
    2.2.4, p. 62. *)
Lemma countable_neighborhood_locus_open (T : topologicalType) :
  open (@countable_neighborhood_locus T).
Proof.
rewrite openE=> x [V [ho [hc hx]]].
have hn : nbhs x V by rewrite openE in ho; exact: ho x hx.
apply: filterS hn=> y hy; exists V; by repeat split.
Qed.

(** Source for [countable_neighborhood_locus_countable]: Supporting Federer
    2.2.4, p. 62. *)
Lemma countable_neighborhood_locus_countable (T : topologicalType)
    (U : nat -> set T) : is_countable_open_base U ->
  countable (@countable_neighborhood_locus T).
Proof.
move=> hU; pose C := [set V : set T | open V /\ countable V].
have hc : countable_neighborhood_locus `<=` \bigcup_(V in C) V.
  move=> x [V [ho [hc hx]]]; exists V=> //; by split.
have ho V : C V -> open V by move=> [].
have [G [hG [hcnt hcover]]] := countable_base_open_subcover hU ho hc.
apply: sub_countable (subset_card_le hcover) _.
apply: bigcup_countable hcnt _=> V hV; exact: (hG V hV).2.
Qed.

(** Source for [countable_neighborhood_complement_closed]: Supporting
    Federer 2.2.4, p. 62. *)
Lemma countable_neighborhood_complement_closed (T : topologicalType) :
  closed (~` @countable_neighborhood_locus T).
Proof. exact: open_closedC (@countable_neighborhood_locus_open T). Qed.

(** Source for [countable_neighborhood_complement_nonempty]: Supporting
    Federer 2.2.4, p. 62.An uncountable space cannot be exhausted by its
    countable set of points with countable neighborhoods. *)
Lemma countable_neighborhood_complement_nonempty (T : topologicalType)
    (U : nat -> set T) : is_countable_open_base U ->
  ~ countable (@setT T) -> (~` @countable_neighborhood_locus T) !=set0.
Proof.
move=> hU hnot; apply: contrapT=> he; apply: hnot.
have hsub : (@setT T) `<=` countable_neighborhood_locus.
  move=> x _; apply: contrapT=> hx; apply: he; by exists x.
exact: sub_countable (subset_card_le hsub) (countable_neighborhood_locus_countable hU).
Qed.
