(** Federer (1969), 2.2.1, p. 60: Borel partitions of a subset A. We retain
    Federer's arbitrary subset A. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountablyClosedFamilyUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_borel_partition]: Federer 2.2.1, p. 60,
    definition, paraphrased: a countable disjoint family of Borel
    sets whose union equals A. Empty members are permitted, as in
    the printed set-family definition. *)
Record is_borel_partition (T : topologicalType) (A : set T) (G : set (set T)) := {
  borel_partition_countable : countable G;
  borel_partition_disjoint : set_family_disjoint G;
  borel_partition_members : forall B, G B -> borel_set B;
  borel_partition_union : (\bigcup_(B in G) B) = A
}.

(** Source for [borel_partition_set_borel]: Federer 2.2.1,
    p. 60, supporting consequence: the set covered by a Borel
    partition is Borel, by countable-union closure. *)
Lemma borel_partition_set_borel (T : topologicalType) (A : set T) (G : set (set T)) :
  is_borel_partition A G -> borel_set A.
Proof.
move=> hG; rewrite -(borel_partition_union hG).
exact: (@borel_set_countable_union T _ G (fun B => B)
  (borel_partition_countable hG) (borel_partition_members hG)).
Qed.

(** Source for [borel_partition_empty]: Federer 2.2.1,
    p. 60, supporting empty-family convention: the empty family
    is a Borel partition of the empty set. *)
Lemma borel_partition_empty (T : topologicalType) :
  @is_borel_partition T set0 set0.
Proof.
constructor.
- exact: countable0.
- by move=> A B [].
- by move=> B [].
- exact: bigcup_set0.
Qed.

(** Source for [borel_partition_singleton]: Federer 2.2.1,
    p. 60, supporting one-member example: any Borel set has
    the partition consisting of itself, including the empty set. *)
Lemma borel_partition_singleton (T : topologicalType) (A : set T) :
  borel_set A -> is_borel_partition A [set A].
Proof.
move=> hA; constructor.
- exact: countable1.
- move=> B C hB hC hn; exfalso; apply: hn; by rewrite hB hC.
- by move=> B ->.
- apply/seteqP; split=> [x [B -> hx]|x hx] //; by exists A.
Qed.
