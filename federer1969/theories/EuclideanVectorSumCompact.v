(** Federer (1969), 3.2.41, printed p. 278, compact
    approximation: the actual sum of two compact sets is
    compact, as the continuous image of their compact product. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanAdditiveGroup
  TopologicalGroupUP VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_vector_sum_compact]: supporting
    compact target in the first sentence of Federer 3.2.41,
    p. 278. The original sum is identified exactly with
    addition's image of the original Cartesian product;
    empty compact factors are included. *)
Lemma euclidean_vector_sum_compact (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  compact A ->compact B ->compact (vector_set_sum A B).
Proof.
move=> hA hB.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
have hEq:vector_set_sum A B=(fun p:E*E=>p.1+p.2) @` (A `*` B).
  apply/seteqP; split.
  - move=> z /vector_set_sum_membership [x [y [hx [hy ->]]]].
    exists (x,y); last reflexivity; by split.
  - move=> z [[x y] [hx hy] <-]; exact:vector_set_sum_contains hx hy.
have hCont:continuous (fun p:E*E=>p.1+p.2):=
  topological_group_mul_continuous (@euclidean_additive_topological_group R n).
rewrite hEq; exact:continuous_compact (continuous_subspaceT hCont) (compact_setX hA hB).
Qed.
