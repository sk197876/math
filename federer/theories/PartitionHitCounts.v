(** The partition counts in Federer (1969), 2.10.10, p. 176: the number of
    cells meeting a fibre increases under refinement and is bounded by its
    cardinality. This supplies the geometric functional in 2.5.10, p. 101.
    We use the abstract partition-tree laws of 2.2.10(2), p. 67. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic
  ShrinkingBorelPartitionLevels CountingMeasure CountingImageBound DisjointCellCountingBound
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partition_hit_indices]: indices of the
    cells meeting a test set, supporting the characteristic
    sums of Federer 2.10.10, p. 176. For
    the multiplicity formula the test set is a fibre. *)
Definition partition_hit_indices (X : Type) (P : seq nat -> set X)
    (A : set X) n := [set s | size s=n /\ (A `&` P s) !=set0].

(** Source for [partition_hit_count]: the count of cells
    meeting a set at a given level, supporting the increasing
    sequence of characteristic sums in Federer 2.10.10,
    p. 176. The count can be infinite. *)
Definition partition_hit_count (R : realType) (X : Type)
    (P : seq nat -> set X) (A : set X) n :=
  counting_measure (R:=R) (partition_hit_indices P A n).

(** Source for [partition_hit_count_upper]: partition
    disjointness bounds the characteristic sum by the fibre
    multiplicity in Federer 2.10.10, p. 176. *)
Lemma partition_hit_count_upper (R : realType) (X : choiceType)
    (E P : seq nat -> set X) (hP : is_cover_partition_tree E P) A n :
  @partition_hit_count R X P A n<=counting_measure (R:=R) A.
Proof.
rewrite /partition_hit_count /partition_hit_indices.
refine (@disjoint_cells_counting_bound R X [the choiceType of (seq nat : Type)]
  [set s | size s=n] P A _).
move=> s t x hs ht hxs hxt.
apply: (@cover_partition_level_unique X E P hP s t x _ hxs hxt).
by rewrite hs ht.
Qed.

(** Source for [partition_hit_parent_image]: each cell
    meeting the test set has a child meeting it, while every
    child lies in its parent. This realizes the refinement
    assertion of Federer 2.10.10, p. 176. *)
Lemma partition_hit_parent_image (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A n :
  (behead @` partition_hit_indices P A n.+1)=partition_hit_indices P A n.
Proof.
apply/seteqP; split=> s.
- move=> [t [ht [x [hx hpx]]] <-].
  case: t ht hpx=> [|j t] //= ht hpx.
  split; first by move: ht=> [].
  exists x; split=> //; exact: (@cover_partition_child_subset X E P hP t j x hpx).
- move=> [hs [x [hx hpx]]].
  rewrite (@cover_partition_children_cover R X E P hE hP s) in hpx.
  have [j _ hj] := hpx; exists (j::s)=> //.
  split; first by rewrite /= hs.
  exists x; by split.
Qed.

(** Source for [partition_hit_count_increasing]: the
    characteristic sums increase under refinement, as asserted
    in Federer 2.10.10, p. 176. The proof
    counts the parent image and permits infinite values. *)
Lemma partition_hit_count_increasing (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A n :
  @partition_hit_count R X P A n<=@partition_hit_count R X P A n.+1.
Proof.
rewrite /partition_hit_count -(@partition_hit_parent_image R X E P hE hP A n).
exact: counting_measure_image_bound.
Qed.
