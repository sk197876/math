(** Federer (1969), 2.2.10, pp. 65–66: closed projection representations,
    including the empty set and whole space. This supporting construction
    represents a closed set A by A times a singleton in N. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SuslinSetUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_set_univalent_projection]: supporting closed-set
    representation for the family F in Federer 2.2.10, p. 66. The witness A
    times a singleton is closed and its projection is one-to-one *)
Lemma closed_set_univalent_projection (R : realType) (T : topologicalType) (A : set T) :
  closed A -> has_univalent_closed_projection R A.
Proof.
move=> hA; pose n0 := @positive_sequence_default R.
have hn : closed [set n0].
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
pose C := [set p : T * positive_sequence_space R | A p.1 /\ p.2 = n0].
exists C; constructor.
- apply: closedI.
  + apply: (proj1 (continuous_closedP (@fst T (positive_sequence_space R))) _ A hA).
    exact: first_projection_continuous.
  + apply: (proj1 (continuous_closedP (@snd T (positive_sequence_space R))) _ [set n0] hn).
    exact: second_projection_continuous.
- apply/seteqP; split.
  + by move=> x [[y n] [hy hn'] <-].
  + move=> x hx; exists (x,n0)=> //; by split.
- move=> [x n] [y m] /= [hx hn'] [hy hm'] hxy.
  rewrite /= in hn' hm' hxy.
  by rewrite hxy hn' hm'.
Qed.

(** Source for [closed_set_suslin]: supporting inclusion of
    closed sets among Suslin sets in Federer 2.2.10,
    pp. 65–66: forget injectivity of the closed witness projection. *)
Lemma closed_set_suslin (R : realType) (T : topologicalType) (A : set T) :
  closed A -> is_suslin_set R A.
Proof.
move=> hA; apply: univalent_closed_projection_is_suslin.
exact: (@closed_set_univalent_projection R T A hA).
Qed.

(** Source for [empty_set_suslin]: supporting empty-set boundary
    case for Federer 2.2.10, pp. 65–66. No inhabitance
    assumption on the ambient topological space is needed. *)
Lemma empty_set_suslin (R : realType) (T : topologicalType) :
  is_suslin_set R (@set0 T).
Proof. apply: closed_set_suslin; exact: closed0. Qed.
