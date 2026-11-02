(** Federer (1969), 2.6.1, pp. 114–115: expressing a countable rectangle
    cover as a sequence without changing its cost. Empty rectangles fill
    unused natural indices. This is supporting set-theoretic and summation
    infrastructure, using 2.1.1(9), p. 53. they do not state this
    implementation lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_zero_cost_enumeration]: supporting
    equivalence between countable-family and sequence covers in
    Federer 2.6.1, pp. 114–115. Each genuine member
    occurs at its injective natural code, and a zero-cost default
    fills all gaps, including an entirely empty family. *)
Lemma countable_zero_cost_enumeration (R : realType) (J : choiceType)
    (G : set J) (cost : J -> \bar R) (d : J) :
  countable G -> cost d=0 -> (forall j, G j -> 0 <= cost j) ->
  exists u : nat -> J,
    (forall n, G (u n) \/ u n=d) /\
    (forall j, G j -> exists n, u n=j) /\
    nonnegative_sum setT (fun n => cost (u n))=nonnegative_sum G cost.
Proof.
move=> /countable_injP[g hg] hd hcost.
pose E n := G `&` [set j | g j == n].
pose u n := if pselect (exists j, E n j) is left h then projT1 (cid h) else d.
have hsel n : E n (u n) \/ (u n=d /\ E n=set0).
  rewrite /u; case: pselect=> [hh|hn]; first by left; exact: projT2 (cid hh).
  right; split=> //; apply/seteqP; split=> [j hj|j []]; apply: hn; by exists j.
have hinj n j k : E n j -> E n k -> j=k.
  move=> [hj /eqP hej] [hk /eqP hek].
  apply: hg; [exact: mem_set hj|exact: mem_set hk|by rewrite hej hek].
have hsum n : cost (u n)=nonnegative_sum (E n) cost.
  have [hu|[he hz]] := hsel n.
  - have he : E n=[set u n].
      apply/seteqP; split=> [j hj|j hj]; first exact: hinj n j (u n) hj hu.
      by move: hj=> /= ->.
    rewrite he nonnegative_sum_singleton //; exact: hcost (u n) hu.1.
  - by rewrite he hz hd nonnegative_sum_empty.
exists u; split.
- move=> n; have [hu|[he _]] := hsel n; [left; exact: hu.1|by right].
- split.
  + move=> j hj; exists (g j); have [hu|[_ he]] := hsel (g j).
    * exact (hinj (g j) (u (g j)) j hu (conj hj (eqxx _))).
    * exfalso; have hh : E (g j) j by split=> //; exact: eqxx.
      by rewrite he in hh.
  + rewrite (@nonnegative_sum_grouping R J [the choiceType of (nat : Type)] G setT g cost)
      //.
    apply: nonnegative_sum_ext=> n _; exact: hsum.
Qed.
