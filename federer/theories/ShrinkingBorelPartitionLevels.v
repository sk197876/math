(** The nested small Borel partitions in Federer (1969), 2.10.10, p. 176,
    obtained from the already constructed partition tree of 2.2.10(2), p.
    67. This is preparatory infrastructure for the counting integral in
    2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import ClosedCoverTreeUP CoverPartitionTreeUP
  CoverPartitionTreeBasic BorelImageTreeEquality TopologicalBorel
  BorelFamilyBasic SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cover_partition_level_unique]: disjointness
    within each partition of Federer 2.10.10, p. 176,
    deduced from the tree of 2.2.10(2), p. 67.
    Empty partition cells do not cause an exception. *)
Lemma cover_partition_level_unique (T : Type) (E P : seq nat -> set T)
    (hP : is_cover_partition_tree E P) s t x :
  size s=size t -> P s x -> P t x -> s=t.
Proof.
elim: s t=> [|i s ih] [|j t] //= hsize hx hy.
have hst : size s=size t by move: hsize=> [].
have hp := @cover_partition_child_subset T E P hP s i x hx.
have hq := @cover_partition_child_subset T E P hP t j x hy.
have he := ih t hst hp hq; subst t.
have hij : i=j.
  case: (eqVneq i j)=> [he|hne]; first exact he.
  exfalso; have hn : i<>j by move=> he; move: hne; rewrite he eqxx.
  have hh : (P (i::s) `&` P (j::s)) x by split.
  by rewrite (@cover_partition_children_disjoint T E P hP s i j hn) in hh.
by rewrite hij.
Qed.

(** Source for [cover_partition_level_countable]: countability
    of every partition in Federer 2.10.10, p. 176.
    The index set consists of finite words of the stated length,
    including the unique empty word at level zero. *)
Lemma cover_partition_level_countable n : countable [set s : seq nat | size s=n].
Proof. exact: countableP. Qed.

(** Source for [cover_partition_level_diameter]: shrinking
    diameters of the Borel cells in Federer 2.10.10,
    p. 176, inherited from 2.2.8, p. 64.
    The root is excluded because it is the whole space. *)
Lemma cover_partition_level_diameter (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) s x y : s !=[::] ->
  P s x -> P s y -> mdist x y<=@closed_cover_tree_scale R (size s).
Proof.
move=> hs hx hy; apply: (@closed_cover_tree_diameter R X E hE s hs).
- exact (@cover_partition_within_cover R X E P hE hP s x hx).
- exact (@cover_partition_within_cover R X E P hE hP s y hy).
Qed.

(** Source for [closed_cover_tree_scale_small]: arbitrarily
    small partition cells required in Federer 2.10.10,
    p. 176, using the geometric scales of 2.2.8,
    p. 64. The chosen level is positive. *)
Lemma closed_cover_tree_scale_small (R : realType) (e : R) :
  0<e -> exists n, @closed_cover_tree_scale R n.+1<e.
Proof.
move=> he; have [n hn] := sequence_inverse_power_small he.
exists n; apply: le_lt_trans _ hn.
rewrite /closed_cover_tree_scale; apply: ler_wiXn2l.
- by rewrite invr_ge0 ler0n.
- by rewrite invf_le1 ?ltr0n // ler1n.
- exact: leq_trans (leqnSn n) (leq_addr 2 n.+1).
Qed.
