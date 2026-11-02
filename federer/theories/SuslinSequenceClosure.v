(** Federer (1969), 2.2.10, p. 66: countable unions and nonempty countable
    intersections of Suslin sets are Suslin. The proof uses the same
    sequence cylinders and countable-power homeomorphism as the preceding
    univalent-projection argument, without assuming univalence. Source
    context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCountablePower SuslinSetUP
  ClosedProjectionUnion TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import ArrowAsProduct.

(** Source for [suslin_sequence_union]: direct sequence-union
    instance of Federer 2.2.10, p. 66, penultimate paragraph.
    Pasting the closed witnesses along the clopen sequence cylinders
    preserves closedness; no disjointness of the images is needed. *)
Theorem suslin_sequence_union (R : realType) (T : topologicalType) (S : nat -> set T) :
  (forall i, is_suslin_set R (S i)) -> is_suslin_set R (\bigcup_i S i).
Proof.
move=> hs; pose C i := projT1 (cid (hs i)).
have hC i : closed (C i) /\ fst @` C i = S i := projT2 (cid (hs i)).
exists (closed_projection_cylinder_union C); split.
- apply: closed_projection_cylinder_union_closed=> i; exact: (hC i).1.
- rewrite closed_projection_cylinder_union_image.
  apply/seteqP; split.
  + move=> x [i _ hx]; exists i=> //; by move: hx; rewrite (hC i).2.
  + move=> x [i _ hx]; exists i=> //; by rewrite (hC i).2.
Qed.

(** Source for [suslin_sequence_intersection]: direct sequence-
    intersection instance of Federer 2.2.10, p. 66.
    Closed constraints encode one witness for each sequence term,
    then the 2.2.6 homeomorphism encodes their countable array in N. *)
Theorem suslin_sequence_intersection (R : realType) (T : topologicalType)
    (S : nat -> set T) :
  (forall i, is_suslin_set R (S i)) -> is_suslin_set R (\bigcap_i S i).
Proof.
move=> hs; pose C i := projT1 (cid (hs i)).
have hC i : closed (C i) /\ fst @` C i = S i := projT2 (cid (hs i)).
have [f [g [hfg [hgf [hf hg]]]]] := @positive_sequence_countable_power_homeomorphism R.
pose F i (p : T * positive_sequence_space R) := (p.1,g p.2 i).
have hF i : continuous (F i).
  apply: topological_pair_continuous.
  - exact: first_projection_continuous.
  - move=> p.
    have hproj := @proj_continuous _
      (fun _ : nat => [the topologicalType of positive_sequence_space R]) i (g p.2).
    have hgi := continuous_comp (hg p.2) hproj.
    exact: continuous_comp (@second_projection_continuous T (positive_sequence_space R) p) hgi.
pose D := \bigcap_i (F i @^-1` C i).
exists D; split.
- apply: closed_bigI=> i _.
  exact: (proj1 (continuous_closedP (F i)) (hF i) _ (hC i).1).
- apply/seteqP; split.
  + move=> x [[y n] hn <-] i _.
    rewrite -(hC i).2; exists (y,g n i)=> //; exact: hn i Logic.I.
  + move=> x hx.
    have hex i : exists n, C i (x,n).
      have hi : (fst @` C i) x by rewrite (hC i).2; exact: hx i Logic.I.
      have [[y n] hn he] := hi; exists n; by rewrite -he.
    pose ns i := projT1 (cid (hex i)).
    have hns i : C i (x,ns i) := projT2 (cid (hex i)).
    exists (x,f ns)=> // i _; change (C i (x,g (f ns) i)); by rewrite hfg.
Qed.
