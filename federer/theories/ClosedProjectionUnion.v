(** Federer (1969), 2.2.10, p. 66: countable unions of closed projections,
    with univalence for disjoint projected sets. The erratum p. 1 corrects
    book p. 66 lines 13 and 15 to a countable sequence and the correctly
    indexed cylinders. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCylinders
  SequenceCylinderHomeomorphism SuslinSetUP OpenCoverPasting TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_projection_cylinder_union]: supporting
    witness for the countable union in Federer 2.2.10, p. 66:
    the first coordinate selects a closed projection witness and
    the remaining coordinates supply its sequence parameter. *)
Definition closed_projection_cylinder_union (R : realType) (T : topologicalType)
    (C : nat -> set (T * positive_sequence_space R)) : set (T * positive_sequence_space R) :=
  [set p | C (positive_sequence_coordinates p.2 0%N) (p.1,positive_sequence_tail p.2)].

(** Source for [closed_projection_cylinder_union_closed]: direct closedness
    argument for D in Federer 2.2.10, p. 66. Each cylinder section is an
    intersection of two closed sets; the cylinders also form an open cover. *)
Lemma closed_projection_cylinder_union_closed (R : realType) (T : topologicalType)
    (C : nat -> set (T * positive_sequence_space R)) :
  (forall i, closed (C i)) -> closed (closed_projection_cylinder_union C).
Proof.
move=> hc; pose U i := @snd T (positive_sequence_space R) @^-1` positive_sequence_cylinder i.
pose F (p : T * positive_sequence_space R) := (p.1,positive_sequence_tail p.2).
have hF : continuous F.
  apply: topological_pair_continuous; first exact: first_projection_continuous.
  move=> p; exact: continuous_comp
    (@second_projection_continuous T (positive_sequence_space R) p)
    (@positive_sequence_tail_continuous R p.2).
apply: (@closed_from_open_cover_sections _ nat U).
- move=> i; apply: (@open_comp _ _ (@snd T (positive_sequence_space R))
    (positive_sequence_cylinder i)).
  + move=> p _; exact: second_projection_continuous.
  + exact: positive_sequence_cylinder_open.
- move=> [x n]; exists (positive_sequence_coordinates n 0%N); by [].
- move=> i.
  have he : closed_projection_cylinder_union C `&` U i = (F @^-1` C i) `&` U i.
    apply/seteqP; split=> -[x n] [hc' hi]; split=> //.
    + change (C i (x,positive_sequence_tail n)); by move: hc'; rewrite /closed_projection_cylinder_union /= hi.
    + change (C (positive_sequence_coordinates n 0%N) (x,positive_sequence_tail n)); by rewrite hi.
  rewrite he; apply: closedI.
  + exact: (proj1 (continuous_closedP F) hF _ (hc i)).
  + exact: (proj1 (continuous_closedP (@snd T (positive_sequence_space R)))
      (@second_projection_continuous T (positive_sequence_space R))
      _ (@positive_sequence_cylinder_closed R i)).
Qed.

(** Source for [closed_projection_cylinder_union_image]: direct
    image identity for D in Federer 2.2.10, p. 66: the
    projection of the pasted witness is the union of the original
    projections. Disjointness is not needed for this identity. *)
Lemma closed_projection_cylinder_union_image (R : realType) (T : topologicalType)
    (C : nat -> set (T * positive_sequence_space R)) :
  fst @` closed_projection_cylinder_union C = \bigcup_i (fst @` C i).
Proof.
apply/seteqP; split.
- move=> x [[y n] hn <-]; exists (positive_sequence_coordinates n 0%N)=> //.
  by exists (y,positive_sequence_tail n).
- move=> x [i _ [[y n] hn <-]].
  exists (y,positive_sequence_prepend i n)=> //.
  by rewrite /closed_projection_cylinder_union /= positive_sequence_prepend_head positive_sequence_tail_prepend.
Qed.

(** Source for [univalent_closed_projection_disjoint_sequence_union]: direct
    disjoint-union assertion for F in Federer 2.2.10, p. 66. Disjointness
    first determines the cylinder, and univalence of that piece then
    determines the remaining coordinates. *)
Theorem univalent_closed_projection_disjoint_sequence_union (R : realType)
    (T : topologicalType) (S : nat -> set T) :
  (forall i, has_univalent_closed_projection R (S i)) ->
  (forall i j x, S i x -> S j x -> i = j) ->
  has_univalent_closed_projection R (\bigcup_i S i).
Proof.
move=> hs hd; pose C i := projT1 (cid (hs i)).
have hC i : is_univalent_closed_projection (S i) (C i) := projT2 (cid (hs i)).
exists (closed_projection_cylinder_union C); constructor.
- apply: closed_projection_cylinder_union_closed=> i; exact: univalent_projection_closed (hC i).
- rewrite closed_projection_cylinder_union_image.
  apply/seteqP; split.
  + move=> x [i _ hx]; exists i=> //; by move: hx; rewrite (univalent_projection_image (hC i)).
  + move=> x [i _ hx]; exists i=> //; by rewrite (univalent_projection_image (hC i)).
- move=> [x n] [y m] hn hm he; change (x = y) in he; subst y.
  pose i := positive_sequence_coordinates n 0%N.
  pose j := positive_sequence_coordinates m 0%N.
  have hi : S i x.
    rewrite -(univalent_projection_image (hC i)); by exists (x,positive_sequence_tail n).
  have hj : S j x.
    rewrite -(univalent_projection_image (hC j)); by exists (x,positive_sequence_tail m).
  have hij := hd i j x hi hj.
  have hm' : C i (x,positive_sequence_tail m) by rewrite hij.
  have hp := @univalent_projection_injective R T (S i) (C i) (hC i)
    (x,positive_sequence_tail n) (x,positive_sequence_tail m) hn hm' erefl.
  have ht := congr1 (@snd T (positive_sequence_space R)) hp.
  rewrite /= in ht.
  have hnm : n = m.
    rewrite -(@positive_sequence_prepend_tail R i n erefl).
    rewrite -(@positive_sequence_prepend_tail R j m erefl).
    by rewrite hij ht.
  by rewrite hnm.
Qed.
