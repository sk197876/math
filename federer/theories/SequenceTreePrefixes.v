(** Federer (1969), 2.2.8, p. 64: the finite coordinate prefixes indexing
    the branch sets E(n1,...,nk). Natural codes for positive coordinates and
    reversed word storage follow SequenceSpaceUP.v and ClosedCoverTreeUP.v,
    respectively. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace ClosedCoverTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [sequence_tree_prefix]: supporting encoding of
    E(n1,...,nk) in Federer 2.2.8, p. 64. The newest
    coordinate is placed at the head for structural recursion. *)
Fixpoint sequence_tree_prefix (R : realType) (n : positive_sequence_space R) k : seq nat :=
  if k is l.+1 then positive_sequence_coordinates n l :: sequence_tree_prefix n l else [::].

(** Source for [sequence_tree_prefix_size]: supporting level
    identity for Federer 2.2.8, p. 64: the prefix through
    coordinate k contains exactly k entries. *)
Lemma sequence_tree_prefix_size (R : realType) (n : positive_sequence_space R) k :
  size (sequence_tree_prefix n k) = k.
Proof. by elim: k=> [|k IH] //=; rewrite IH. Qed.

(** Source for [sequence_tree_prefix_agreement]: supporting
    prefix identity in Federer 2.2.8, pp. 64–65: coordinate
    agreement through level k makes the two branch sets identical. *)
Lemma sequence_tree_prefix_agreement (R : realType)
    (m n : positive_sequence_space R) k :
  (forall i, (i < k)%N -> positive_sequence_coordinates m i = positive_sequence_coordinates n i) ->
  sequence_tree_prefix m k = sequence_tree_prefix n k.
Proof.
elim: k=> [|k IH] h //=; rewrite (h k (ltnSn k)); congr (_ :: _).
apply: IH=> i hi; exact: h i (ltn_trans hi (ltnSn k)).
Qed.

(** Source for [closed_cover_branch_nested]: Federer 2.2.8,
    p. 64, the displayed decreasing sequence of branch sets;
    every later prefix gives a subset of every earlier prefix. *)
Lemma closed_cover_branch_nested (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E)
    (n : positive_sequence_space R) i j :
  (i <= j)%N -> E (sequence_tree_prefix n j) `<=` E (sequence_tree_prefix n i).
Proof.
move=> hij; elim: j hij=> [|j IH] hij x hx.
- have -> : i = 0%N by apply/eqP; rewrite -leqn0.
  exact hx.
- case: (eqVneq i j.+1)=> [->|hine]; first exact hx.
  apply: IH; first by move: hij; rewrite leq_eqVlt (negbTE hine) /= ltnS.
  exact: (@closed_cover_tree_child_subset R T E hE (sequence_tree_prefix n j)
    (positive_sequence_coordinates n j) x hx).
Qed.
