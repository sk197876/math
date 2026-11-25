(** Federer (1969), 2.2.15, p. 71, final criterion: private first-hit index
    for a countable Borel cover. The least natural index exists by natural
    well ordering, and its fibre is A_n minus the union of earlier A_i.
    Source context. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import TopologicalBorel BorelDiscreteIndexUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [first_borel_cover_index_exists]: supporting
    choice and Borelness proof for the countable approximations
    in Federer 2.2.15, p. 71. The first-hit sets
    form a partition even when the original cover overlaps. *)
Theorem first_borel_cover_index_exists (X : topologicalType) (A : nat -> set X) :
  (forall n, borel_set (A n)) -> (forall x, exists n, A n x) ->
  exists q, is_first_borel_cover_index A q.
Proof.
move=> hA hc.
have hw x : exists n, A n x /\ forall i, A i x -> (n <= i)%N.
  have hh : exists n, `[< A n x >] by have [n hn] := hc x; exists n; exact/asboolP.
  have [n /asboolP hn hmin] := ex_minnP hh.
  exists n; split=> // i hi; apply: hmin; exact/asboolP.
pose q x := projT1 (cid (hw x)).
have hq x : A (q x) x /\ forall i, A i x -> (q x <= i)%N := projT2 (cid (hw x)).
exists q; constructor.
- by move=> x; exact: (hq x).1.
- by move=> x i; exact: (hq x).2.
- move=> n.
  have he : [set x | q x = n] = A n `\` \bigcup_(i in [set i | (i < n)%N]) A i.
    apply/seteqP; split.
    + move=> x hx; split; first by rewrite -hx; exact: (hq x).1.
      move=> [i hi hai]; have hle := (hq x).2 i hai.
      have hi0 : (i < n)%N := hi.
      by move: hi0; rewrite -hx ltnNge hle.
    + move=> x [hx hn]; apply/eqP; rewrite eqn_leq (hq x).2 //=.
      rewrite leqNgt; apply/negP=> hlt; apply: hn; exists (q x)=> //; exact: (hq x).1.
  rewrite he; apply: borel_set_difference (hA n) _.
  apply: borel_set_countable_union; first exact: countableP.
  by move=> i hi; exact: hA i.
Qed.
