(** Federer (1969), 2.2.10(2), p. 67: the A(s) constitute Borel partitions
    at every level and refine the closed-cover tree E. Consequences below
    use the abstract recursion laws and the already proved sequence
    disjointification. Source context and word convention:
    CoverPartitionTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import SetSequenceDisjointification BorelFamilyBasic TopologicalBorel
  ClosedCoverTreeUP CoverPartitionTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [cover_partition_child_subset]: supporting nesting
    in Federer 2.2.10(2), p. 67: every child A(s,j)
    lies in its parent A(s). *)
Lemma cover_partition_child_subset (T : Type) (E A : seq nat -> set T)
    (hA : is_cover_partition_tree E A) s j : A (j::s) `<=` A s.
Proof. rewrite (cover_partition_step hA); by move=> x [hx _]. Qed.

(** Source for [cover_partition_within_cover]: supporting
    refinement assertion in Federer 2.2.10(2), p. 67:
    A(s) lies in E(s), so it inherits the relevant diameter bound. *)
Lemma cover_partition_within_cover (R : realType) (T : metricType R)
    (E A : seq nat -> set T) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) s : A s `<=` E s.
Proof.
case: s=> [|j s].
- by rewrite (closed_cover_tree_root hE).
- rewrite (cover_partition_step hA); by move=> x [_ [hx _]].
Qed.

(** Source for [cover_partition_borel]: direct Borel assertion for A(s) in
    Federer 2.2.10(2), p. 67: the closed E(s), finite preceding unions,
    intersection and difference preserve Borel membership. *)
Lemma cover_partition_borel (R : realType) (T : metricType R)
    (E A : seq nat -> set T) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) s : borel_set (A s).
Proof.
elim: s=> [|j s IH].
- rewrite (cover_partition_root hA); exact: open_borel_set (@openT T).
- rewrite (cover_partition_step hA); apply: (@borel_family_binary_intersection T setT _ (borel_sets_family T))=> //.
  apply: borel_set_difference.
  + exact: (@closed_borel_set T (E (j::s)) (@closed_cover_tree_closed R T E hE (j::s))).
  + apply: borel_set_countable_union; first exact: countableP.
    move=> i _; exact: (@closed_borel_set T (E (i::s)) (@closed_cover_tree_closed R T E hE (i::s))).
Qed.

(** Source for [cover_partition_children_disjoint]: direct
    sibling disjointness for A(s) in Federer 2.2.10(2),
    p. 67. Subtraction of all earlier siblings ensures that
    two distinct child pieces have empty intersection. *)
Lemma cover_partition_children_disjoint (T : Type) (E A : seq nat -> set T)
    (hA : is_cover_partition_tree E A) s i j :
  i <> j -> A (i::s) `&` A (j::s) = set0.
Proof.
move=> hij; have hne : i != j by apply/negP=> /eqP he; exact: hij he.
rewrite !(@cover_partition_step T E A hA s); apply/seteqP; split; last by move=> x [].
move=> x [[_ hi] [_ hj]]; exact: (@set_sequence_disjointify_disjoint T (fun k => E (k::s)) i j hne x hi hj).
Qed.

(** Source for [cover_partition_children_cover]: direct exhaustion
    in the partition assertion of Federer 2.2.10(2), p. 67:
    the disjoint children have the same union as the original
    covering children after intersection with their parent. *)
Lemma cover_partition_children_cover (R : realType) (T : metricType R)
    (E A : seq nat -> set T) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) s : A s = \bigcup_j A (j::s).
Proof.
apply/seteqP; split.
- move=> x hx.
  have hEx := @cover_partition_within_cover R T E A hE hA s x hx.
  rewrite (closed_cover_tree_children hE s) -set_sequence_disjointify_union in hEx.
  have [j _ hj] := hEx; exists j=> //; rewrite (cover_partition_step hA); by split.
- move=> x [j _ hj]; exact: (@cover_partition_child_subset T E A hA s j x hj).
Qed.
