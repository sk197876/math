(** Federer (1969), 2.2.10, p. 67: disjoint Borel supersets for a sequence
    of pairwise Borel-separated sets. This supporting lemma isolates that
    set-theoretic step; the main separation theorem must supply its
    hypotheses. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import TopologicalBorel BorelSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pairwise_separated_borel_containers]: supporting container
    construction in Federer 2.2.10, p. 67, after (1). Pairwise Borel
    separators yield pairwise disjoint Borel supersets. *)
Theorem pairwise_separated_borel_containers (T : topologicalType) (P : nat -> set T) :
  (forall i j, i <> j -> borel_separated (P i) (P j)) ->
  exists B : nat -> set T,
    (forall i, borel_set (B i) /\ P i `<=` B i) /\
    forall i j, i <> j -> B i `&` B j = set0.
Proof.
move=> hsep.
have hc i j : exists A : set T, borel_set A /\
    (i <> j -> P i `<=` A /\ P j `<=` ~` A).
  case: (pselect (i=j))=> [heq|hne].
  - exists setT; split; first exact: open_borel_set (@openT T).
    by move=> h; exfalso; exact: h heq.
  - have [A [hA [hP hQ]]] := proj1 (borel_separated_one_separator _ _) (hsep i j hne).
    exists A; split=> // _; by split.
pose A i j := projT1 (cid (hc i j)).
have hA i j : borel_set (A i j) /\
    (i <> j -> P i `<=` A i j /\ P j `<=` ~` A i j) := projT2 (cid (hc i j)).
pose B i := \bigcap_(j in [set j | j != i]) (A i j `\` A j i).
exists B; split.
- move=> i; split.
  + apply: borel_set_countable_intersection; first exact: countableP.
    * exists i.+1; change (i.+1 != i); by rewrite eq_sym (ltn_eqF (ltnSn i)).
    * move=> j _; apply: borel_set_difference; [exact: (hA i j).1|exact: (hA j i).1].
  + move=> x hx j hji; change (is_true (j != i)) in hji.
    have hneq : j <> i by move=> h; by move: hji; rewrite h eqxx.
    have hneq' : i <> j by move=> h; exact: hneq (esym h).
    split; [exact: ((hA i j).2 hneq').1 x hx|exact: ((hA j i).2 hneq).2 x hx].
- move=> i j hij; apply/seteqP; split; last by move=> x [].
  move=> x [hi hj].
  have hne : i != j by apply/negP=> /eqP h; exact: hij h.
  have hne' : j != i by rewrite eq_sym.
  exact: (hj i hne).2 (hi j hne').1.
Qed.
