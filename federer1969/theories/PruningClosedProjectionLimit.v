(** Federer (1969), 2.2.12, p. 69: the intersection of the closures of the
    pruned projections is exactly the projection of Z_0 restricted to the
    compact coordinate box K. This equality is the decisive step giving a
    closed subset of the original Suslin set. The proof follows the
    compact-fiber tube and truncation argument; the uniform neighborhood
    bound is expressed by finite prefixes. Source context: SequenceBoxes.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceBoxes SequenceFiniteBounds
  CoordinatePruningUP CoordinatePruningBasic CompactTube CompactBoxNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pruned_projection_closed_limit]: the closed set
    C defined in Federer 2.2.12, p. 69, as the intersection
    of the closures of the projections of Z_i. Including stage
    zero is harmless because the stages decrease. *)
Definition pruned_projection_closed_limit (R : realType) (X : topologicalType)
    (F : nat -> set (X * positive_sequence_space R)) : set X :=
  \bigcap_k closure (fst @` F k).

(** Source for [pruned_projection_limit_closed]: direct closedness
    of C in Federer 2.2.12, p. 69: an arbitrary
    intersection of closed sets is closed. *)
Lemma pruned_projection_limit_closed (R : realType) (X : topologicalType)
    (F : nat -> set (X * positive_sequence_space R)) :
  closed (pruned_projection_closed_limit F).
Proof. apply: closed_bigI=> k _; exact: closed_closure. Qed.

(** Source for [pruned_projection_limit_compact_fiber]: direct
    displayed equality C=p[Z_0 intersect (X times K)] in
    Federer 2.2.12, p. 69. The reverse inclusion uses
    the compact tube and the uniformly sufficient finite prefix
    bounds, preserving arbitrary topological X. *)
Theorem pruned_projection_limit_compact_fiber (R : realType) (X : topologicalType)
    (Z : set (X * positive_sequence_space R)) b F :
  is_coordinate_pruning Z b F -> closed Z ->
  pruned_projection_closed_limit F =
    fst @` (Z `&` (setT `*` sequence_coordinate_box b)).
Proof.
move=> hF hZ; apply/seteqP; split.
- move=> x hx; apply: contrapT=> hno.
  have hdis n : sequence_coordinate_box b n -> ~ Z (x,n).
    move=> hn hz; apply: hno; exists (x,n)=> //; split=> //; by split.
  have [V [W [hV [hW [hxV [hKW hrect]]]]]] :=
    compact_fiber_closed_tube hZ (@sequence_coordinate_box_compact R b) hdis.
  have [k hk] := compact_box_prefix_neighborhood hW hKW.
  have hnb : nbhs x V by rewrite openE in hV; exact: hV x hxV.
  have [y [hy hyV]] := hx k Logic.I V hnb.
  have [[z n] hzn hez] := hy.
  rewrite (@coordinate_pruning_prefix_formula R X Z b F hF k) in hzn.
  have hny : W n := hk n hzn.2.
  have hzV : V z by move: hez=> /= ->.
  exact: hrect z n hzV hny hzn.1.
- move=> x [[y n] [hz [_ hn]] <-] k _; apply: subset_closure.
  exists (y,n); last by [].
  rewrite (@coordinate_pruning_prefix_formula R X Z b F hF k).
  split=> // i hi; exact: hn i.
Qed.

(** Source for [pruned_projection_limit_within_original]: direct
    consequence C subset S in Federer 2.2.12, p. 69.
    The compact-fiber representation is contained in the original
    witness before taking its projection. *)
Lemma pruned_projection_limit_within_original (R : realType) (X : topologicalType)
    (Z : set (X * positive_sequence_space R)) b F :
  is_coordinate_pruning Z b F -> closed Z ->
  pruned_projection_closed_limit F `<=` fst @` Z.
Proof.
move=> hF hZ; rewrite (pruned_projection_limit_compact_fiber hF hZ).
move=> x [p [hp _] <-]; by exists p.
Qed.
