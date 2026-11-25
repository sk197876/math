(** Federer (1969), 2.2.8, p. 64: g(n) is the unique point in all sets along
    the branch n. We state this branch membership property before selecting
    the map; later results use only this property and the abstract tree
    laws. Source context and word encoding: ClosedCoverTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace ClosedCoverTreeUP SequenceTreePrefixes
  ClosedCoverBranches.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_closed_cover_map]: Federer 2.2.8, p. 64,
    abstract definition of g: every value lies in every closed set
    on its coordinate branch. Completeness supplies existence;
    shrinking diameters supply uniqueness. *)
Definition is_closed_cover_map (R : realType) (T : metricType R)
    (E : seq nat -> set T) (g : positive_sequence_space R -> T) : Prop :=
  forall n k, E (sequence_tree_prefix n k) (g n).

(** Source for [closed_cover_map_unique]: supporting uniqueness
    of the parametrisation defined in Federer 2.2.8, p. 64,
    for a fixed abstract cover tree, using the branch-point uniqueness. *)
Lemma closed_cover_map_unique (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E)
    (g h : positive_sequence_space R -> T) :
  is_closed_cover_map E g -> is_closed_cover_map E h -> g = h.
Proof.
move=> hg hh; apply: funext=> n.
exact: (@closed_cover_branch_point_unique R T E hE n (g n) (h n) (hg n) (hh n)).
Qed.
