(** Federer (1969), 2.2.10, p. 66: countable intersections of univalent
    closed projections are univalent closed projections. Zero-based indexing
    only renames the positive sequence indices. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCountablePower SuslinSetUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import ArrowAsProduct.

(** Source for [univalent_closed_projection_sequence_intersection]: direct
    countable-intersection assertion for F in Federer 2.2.10, p. 66. A
    sequence of unique witnesses is encoded by a single member of N;
    coordinate constraints are closed and their intersection is closed. *)
Theorem univalent_closed_projection_sequence_intersection (R : realType)
    (T : topologicalType) (S : nat -> set T) :
  (forall i, has_univalent_closed_projection R (S i)) ->
  has_univalent_closed_projection R (\bigcap_i S i).
Proof.
move=> hs; pose C i := projT1 (cid (hs i)).
have hC i : is_univalent_closed_projection (S i) (C i) := projT2 (cid (hs i)).
have [f [g [hfg [hgf [hf hg]]]]] := @positive_sequence_countable_power_homeomorphism R.
pose F i (p : T * positive_sequence_space R) := (p.1,g p.2 i).
have hF i : continuous (F i).
  apply: topological_pair_continuous.
  - exact: first_projection_continuous.
  - move=> p.
    have hi := @proj_continuous _
      (fun _ : nat => [the topologicalType of positive_sequence_space R]) i (g p.2).
    have hgi := continuous_comp (hg p.2) hi.
    exact: continuous_comp (@second_projection_continuous T (positive_sequence_space R) p) hgi.
pose D := \bigcap_i (F i @^-1` C i).
exists D; constructor.
- apply: closed_bigI=> i _.
  exact: (proj1 (continuous_closedP (F i)) (hF i) _ (univalent_projection_closed (hC i))).
- apply/seteqP; split.
  + move=> x [[y n] hn <-] i _.
    rewrite -(univalent_projection_image (hC i)); by exists (y,g n i); first exact: hn i Logic.I.
  + move=> x hx.
    have hex i : exists n, C i (x,n).
      have hi : (fst @` C i) x by rewrite (univalent_projection_image (hC i)); exact: hx i Logic.I.
      have [[y n] hn he] := hi; exists n; by rewrite -he.
    pose ns i := projT1 (cid (hex i)).
    have hns i : C i (x,ns i) := projT2 (cid (hex i)).
    exists (x,f ns)=> // i _; change (C i (x,g (f ns) i)); by rewrite hfg.
- move=> [x n] [y m] hn hm he.
  change (x = y) in he; subst y.
  have hcoord : g n = g m.
    apply: funext=> i.
    have hp := @univalent_projection_injective R T (S i) (C i) (hC i)
      (x,g n i) (x,g m i) (hn i Logic.I) (hm i Logic.I) erefl.
    exact: (congr1 (@snd T (positive_sequence_space R)) hp).
  have hnm : n = m by rewrite -(hgf n) -(hgf m) hcoord.
  by rewrite hnm.
Qed.
